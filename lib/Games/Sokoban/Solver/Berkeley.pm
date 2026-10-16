package Games::Sokoban::Solver::Berkeley;

# THE STORES ON DISK OF THE TWO BERKELEYDB TWINS -- the seam under
# Games::Sokoban::Solver::Firstbet::Berk (the fb_* family) and under
# Games::Sokoban::Solver::Optimal::Berk (the g_* family). Every store is a
# BerkeleyDB database in a DB_PRIVATE environment of its own, one directory per
# level under the root the caller names (berk_root): only the .brk data files
# touch disk, and the memory pool is the RAM ceiling of the search state, so a
# search can run far past what RAM alone would allow.
#
#   fb_*   one directory per level, <root>/Firstbet/G<id> (or G<id>_<MODE> when
#          the caller tags the stores by mode, so that modes raced at once do not
#          share a file): the deadlock cache bad.brk and the move cache tahy.brk
#          are FACTS about the level and stay from one run to the next, the
#          seen-set pozice.brk is the scratch of one search; G<id>b holds the
#          pull search's scratch.
#   g_*    <root>/Optimal/G<id>, the optimal solver's: bad.brk and tahy.brk as
#          above, plus -- when the caller asks to spill -- the positions with
#          their cost and parent, the cost-ordered queue (a BTREE keyed by
#          cost and sequence, so a cursor on the first record is the cheapest
#          waiting position) and the expanded set; those three are the state
#          of one run, opened empty and deleted at the close.
#
# A directory is one process's at a time: both init subs take a lock file
# and refuse a second opener (two processes on one environment is a crash, and
# was one in the Sokoban project on 2026-08-18). Nothing here deletes a
# directory on its own account but g_close on a solved level: the Firstbet
# twin's directories are reclaimed by fb_sweep, which the caller runs from the
# main thread once the workers are joined, because a worker thread's files stay
# locked by the operating system until then.
#
# This module is loaded only when the caller turns the BerkeleyDB branch on;
# the BerkeleyDB module itself is a recommendation of the distribution, not a
# prerequisite. Lineage: Games::Berkeley of the Sokoban project, less the
# shared-environment family that project had stopped using.

use v5.42;
use BerkeleyDB;
use Carp     qw(confess);
use warnings FATAL => 'uninitialized';
use File::Path ();                           # make_path and remove_tree, always qualified
use Fcntl      ('LOCK_EX', 'LOCK_NB');       # the per-directory locks

our $VERSION = '0.01';

# THE ROOT: the directory every store hangs off, set by the caller before the
# first init (the program takes it from its configuration), or taken from the
# environment variable SOKOBAN_BERK_ROOT. There is no default: a scratch
# directory of gigabytes is not something to create where nobody said.
our $ROOT;

sub berk_root() {
    my $root = $ROOT // $ENV{'SOKOBAN_BERK_ROOT'};
    confess('Berkeley: no root directory for the stores -- set $Games::Sokoban::Solver::Berkeley::ROOT'
            . ' (or SOKOBAN_BERK_ROOT in the environment)')
        unless defined $root and length $root;
    $root =~ tr{\\}{/};
    return $root;
}

# MKDIR, CHECKED -- every environment home in this module goes through here
# (2026-09-12). The shape it replaces was `mkpath($dir) unless -d $dir`, and it
# had two ways of being wrong, both of which end with a BerkeleyDB error that
# says nothing about the directory:
#   * TWO WORKERS SPAWNED AT ONCE both create the home when it is not there --
#     which is exactly the state right after a cleanup -- and the loser of that
#     race gets "File exists" from a mkdir it had every right to lose;
#   * a failure noticed by nobody. make_path with an error reference collects
#     instead of croaking, so the only verdict that counts is taken afterwards
#     and from the filesystem: IS THE DIRECTORY THERE. If it is not, this says
#     which one and what the operating system said about it.
sub make_dir ($dir) {
    return if -d $dir;
    File::Path::make_path($dir, {'error' => \my $err});
    return if -d $dir;    # a lost race is not a failure: somebody else made it
    # die, not confess: the caller chain here is solve(), whose arguments are a
    # compressed blob, and a backtrace through it buries the one line that says
    # which directory and why.
    die "cannot create directory $dir -- "
        . (($err && @$err)
            ? join('; ', map {my ($f, $m) = %$_; ($f eq q{} ? q{} : "$f: ") . $m} @$err)
            : 'and the operating system gave no reason') . "\n";
}

# THE POOL SIZE GOES IN THROUGH A FILE (2026-10-06). BerkeleyDB::Env->new takes
# -Cachesize in bytes, and the module's XS keeps it in a 32-bit int and calls
# set_cachesize only when that int is not zero. So the size was taken modulo
# 4 GB: 4, 8, 12 and 16 GB arrived as 0 and the environment ran on the library's
# own pool of about 260 KB, 6 GB arrived as 2. Every FirstbetBerk campaign up to
# berk-3 ran `--cache 8` and therefore had NO pool -- each touch of a store was a
# ReadFile or a WriteFile through the Windows file cache, and the "RAM ceiling"
# was never what kept the process small. Measured on the installed library:
# 2 M records at -Cachesize 2**33 cost 31.5 GB of reads, at 2**31 none.
# The library reads a DB_CONFIG file from the environment's home before it
# opens, and its set_cachesize line takes gigabytes and bytes apart, so any size
# passes (a 6 GB pool held 4.1 GB of pages without one read). In a DB_PRIVATE
# environment the pool is a CEILING: a buffer is allocated when a page is first
# touched, so asking for more than the stores need costs nothing.
# 0 bytes writes no file and means NO pool -- the regime of those campaigns,
# about a third slower than a pool the store fits into, and nearly free of RAM.
# Anything else under 1 MB is refused: nobody means a pool of that size, and
# the likeliest way to get one is a figure in gigabytes handed over as bytes.
sub pool_config ($home, $bytes) {
    my $file = "$home/DB_CONFIG";
    unless ($bytes) {
        unlink $file;
        return;
    }
    die "a pool of $bytes bytes for $home -- the size is in BYTES, and under 1 MB is no pool at all (0 = none)\n"
        if $bytes < 1048576;
    open(my $fh, '>', $file) or die "cannot write $file: $!\n";
    printf {$fh} "set_cachesize %d %d 1\n", int($bytes / 1073741824), $bytes % 1073741824;
    close($fh) or die "cannot write $file: $!\n";
    return;
}

# A HASH OPENED FOR THE SIZE OF ITS RECORDS, ON 4 KB PAGES (2026-10-06).
# $pairlen is the length of one key plus its value. Two things were wrong with
# the fixed 16 KB / 64 (32 KB / 32 for the move lists) every store here had:
#   * DENSITY. A bucket is split when its page holds more than Ffactor pairs,
#     and 64 pairs of 40 bytes are a sixth of 16 KB: BACKWARD's store cost
#     750 B of file per position, the move lists (three children on average)
#     2 400 B per record. With the library's own formula for Ffactor it is
#     70-100 B, so a pool or the file cache covers ten times as many positions
#     and six games no longer outgrow the machine.
#   * THE END OF A RUN. A pool buffer is one heap block of page size plus a
#     header, and closing the environment frees them one by one. With 16 KB
#     pages a pool that had been FULL took 0.9 / 2.3 / 9.1 s to close at
#     0.25 / 0.5 / 1 GB in one thread -- 2.6 times for the first doubling,
#     4 times for the second -- and six
#     threads closing 2 GB each kept campaign berk-4 at one core for more than
#     eight minutes after its limit, no row written. With 4 KB or 8 KB pages
#     the same close takes 0.1-0.2 s at any size, six threads at once included.
#     Why the larger block is slow was not established (it is above the size
#     the Windows heap serves from its fast lists); the measurement was.
# An EXISTING file keeps the geometry it was created with -- the library reads
# it from the file and ignores these two arguments -- so a kept bad.brk or
# tahy.brk from before this date stays as sparse as it was, and as slow to
# close under a full pool: fb_init gives such a directory no pool (page_size).
sub open_hash ($env, $file, $flags, $pairlen) {
    my $fill = int((4096 - 32) / ($pairlen + 8));
    return BerkeleyDB::Hash->new(
        -Filename => $file, -Flags => $flags, -Env => $env,
        -Pagesize => 4096, -Ffactor => ($fill > 1 ? $fill : 1),
        )
        // die "Cannot open $file: $BerkeleyDB::Error\n";
}

# The page size a store file was created with, read off its first page without
# opening it: every BerkeleyDB file begins with a metadata page that carries the
# access method's magic number at byte 12 and the page size at byte 20, in the
# byte order of the machine that made the file. undef for a file that is not
# there, is too short, or is not a Hash.
sub page_size ($file) {
    open(my $fh, '<:raw', $file) or return undef;
    my $got = read($fh, my $head, 24);
    close $fh;
    return undef unless defined $got and $got == 24;
    for my $order ('V', 'N') {
        my ($magic, $size) = unpack "x12 $order x4 $order", $head;
        return $size if $magic == 0x061561;
    }
    return undef;
}

# A store of the fb_* family failed: say which file and WHERE. die, not confess,
# for make_dir's reason -- the chain above is solve() with a blob in its
# arguments, and the directory is the one thing the reader needs.
sub fb_fail ($file, $dir) {
    die "$file in " . ($dir // '(no directory)') . ": $BerkeleyDB::Error\n";
}

# A lookup that finds nothing answers with this status; any OTHER non-zero
# status is a store that failed, and every accessor of the fb_* family dies on
# it (2026-10-06). They used to read "not zero" as "not there" and to drop the
# status of a write, so a full disk would have left a search running on a store
# that kept nothing: every position new again, the same ones generated without
# end, and an ordinary TIMEOUT with an inflated count at the end of it.
my $NotFound = DB_NOTFOUND;

# A directory is ONE process's: the lock file inside it is taken non-blocking
# and held for the life of the environment; a second opener dies at once,
# naming the directory, instead of corrupting the files. A separate file from
# the databases on purpose -- BerkeleyDB may rewrite those, and a lock must
# outlive any such rewrite. Returns the open handle, which the close drops.
sub take_lock ($dir, $what) {
    open(my $lock, '>>', "$dir/lock") or confess("$what: cannot open $dir/lock: $!\n");
    unless (flock($lock, LOCK_EX | LOCK_NB)) {
        close($lock);
        confess("$what: $dir is open in another process ($dir/lock)\n");
    }
    return $lock;
}


# --- FirstbetBerk per-game env -----------------------------------------------
# Each game gets its OWN env + home dir (<berk_root>/FirstbetBerk/G<id>) so a very
# long single-game run never overloads or contends the shared Bad env that baseline
# Firstbet + the race workers use. The env is DB_PRIVATE: its regions live in process
# memory, so NOTHING but the actual .brk data files (and the one-line DB_CONFIG
# that carries the pool size, see pool_config) touches disk, and the mpool size is
# the RAM CEILING for the offloaded state (disk grows unbounded, RAM does not).
# One env holds this game's Bad + Tahy + Pozice. bad.brk + tahy.brk are what
# a later run wants to find (since the 2.12 tahy() cache read a retry skips the
# whole candidate generation for every position seen before); pozice.brk is the
# trajectory scratch of ONE mode's search and the next fb_init removes it before
# opening. NOTHING HERE DELETES ANYTHING (2026-09-12): the close closes, and what
# is to be reclaimed -- a solved game's directories, a kept game's scratch -- is
# fb_sweep's, from the main thread after the join, where the operating system
# will actually let the files go.
my $FbHome;    # <root>/Firstbet, read off the root at every init and sweep
my ($FbEnv, $FbDir, $FbLock, $FbBad, $FbTahy, $FbPozice);
# BACKWARD scratch env -- separate dir (G<id>b) so it never collides with the forward
# env's persistent Bad/Tahy files; pure trajectory-scratch (a re-run explores a
# different beam), so it is truncated on open and the dir is removed by the sweep.
my ($FbBwdEnv, $FbBwdDir, $FbBseen);


# Opens the game's env with all three DBs. Bad + Tahy are the PERSISTENT pair (DB_CREATE
# reuses a kept dir across a TIMEOUT retry). Pozice (Seen/Parent) is TRAJECTORY-scratch
# belonging to ONE mode's search: each mode opens its own fresh pozice.brk, which fb_close
# REMOVES on mode end. We physically DELETE any leftover pozice.brk here before opening --
# NOT truncate(): BerkeleyDB's truncate only empties the DB logically and keeps the pages
# in the file's free list, so a multi-GB pozice.brk stays multi-GB on disk (observed).
# After a clean run the file is already gone; this only bites a crash-leftover.
# $tag NAMES THE OWNER OF THE STORES (2026-09-09). Empty is the historical
# layout, <root>/FirstbetBerk/G<id>: one directory for the game, so the modes of
# a sequential run inherit each other's Bad and Tahy -- both are facts about the
# GAME (a deadlock is a deadlock, and a position's children do not depend on who
# scores them), so that inheritance is sound and is what the sequence buys.
# A non-empty tag -- the MODE name, set by a driver that races modes on one game
# -- gives G<id>_<TAG> instead, and then no two workers touch one file. The price
# is that each mode starts cold; the two layouts are not merged (yet), so a
# parallel run's stores and a sequential run's are separate bodies of knowledge.
sub fb_init ($gameid, $cachesize = 536870912, $tag = q{}) {    # 512 MB default RAM ceiling

    # A solve that DIED never reached its close, and the driver's worker goes on
    # to the next game: its handles would still be the previous game's, and since
    # the stores open lazily nothing below would replace them. A store handle
    # alone counts too -- a close that died half way leaves exactly that.
    fb_close() if defined $FbEnv or defined $FbBad or defined $FbTahy or defined $FbPozice;
    $FbHome = berk_root() . '/Firstbet';
    $FbDir  = $tag eq q{} ? sprintf('%s/G%d', $FbHome, $gameid)
                          : sprintf('%s/G%d_%s', $FbHome, $gameid, $tag);
    make_dir($FbDir);
    $FbLock = take_lock($FbDir, 'fb_init');
    my $pz = "$FbDir/pozice.brk";
    unlink $pz if -e $pz;    # start from a genuinely EMPTY (small) file, not a truncated 1GB one

    # A KEPT STORE ON LARGE PAGES GETS NO POOL. bad.brk and tahy.brk made before
    # 2026-10-06 have 16 KB and 32 KB pages and keep them (open_hash), and a pool
    # FILLED with pages of that size is what takes minutes to close in a thread.
    # Without a pool such a run is about a third slower and ends when it should;
    # tools/update_berk_merge.pl rewrites the pair onto 4 KB pages.
    my $large = grep {(page_size("$FbDir/$_") // 0) > 8192} 'bad.brk', 'tahy.brk';
    pool_config($FbDir, ($large ? 0 : $cachesize));
    $FbEnv = BerkeleyDB::Env->new(
        -Home  => $FbDir,
        -Flags => DB_CREATE | DB_INIT_MPOOL | DB_PRIVATE,
        )
        or die "Cannot open FirstbetBerk env for game $gameid ($FbDir): $BerkeleyDB::Error\n";
    return;
}


# THE THREE STORES OPEN AT THE FIRST TOUCH (2026-10-06), because that is the
# first moment the length of a position is known -- fb_init is called before the
# game's blob is even unpacked -- and a hash is opened for the size of its
# records (open_hash). A pair is a position and: one byte in Bad, the parent's
# position in Pozice, the children in Tahy -- three of them on average, measured
# on three games of the residue (means 2.8-2.9, the 99th percentile 11). Every
# accessor below asks for this first. pozice.brk was removed by fb_init, and is
# opened with DB_TRUNCATE all the same: where that removal could not happen (a
# file the operating system still held for a worker not yet joined), the
# previous search's positions would otherwise be this one's seen-set.
sub fb_open ($keylen) {
    confess("a FirstbetBerk store was touched with no environment open\n") unless defined $FbEnv;
    $FbBad    = open_hash($FbEnv, 'bad.brk',    DB_CREATE, $keylen + 1);
    $FbTahy   = open_hash($FbEnv, 'tahy.brk',   DB_CREATE, 4 * $keylen);
    $FbPozice = open_hash($FbEnv, 'pozice.brk', DB_CREATE | DB_TRUNCATE, 2 * $keylen);
    return;
}


# CLOSING IS ALL IT DOES. It used to delete as well -- the whole directory when
# the game was solved, pozice.brk otherwise -- and inside a worker thread that
# can never work: the operating system holds the files until the thread is
# JOINED, so the removal failed every time, loudly for a directory (File::Remove
# says "Directory not empty") and silently for a file, and the driver had to do
# it again after the join anyway. USER 2026-09-12: *if it cannot be deleted at
# that moment and can be later, there is no point in the first attempt at all.*
# So the deletion lives in one place now, fb_sweep, called by the driver after
# the join with the games it owns named. Nothing here is lost by waiting: a
# leftover pozice.brk is removed by the next fb_init before it opens anything,
# and bad.brk + tahy.brk are what a later run WANTS to find.
#
# THE STATUS OF EVERY CLOSE IS KEPT AND SAID. With a real pool the pages of a
# store reach the disk at its close, not at the write that made them, so a full
# disk shows HERE and nowhere else. Everything is closed first and the handles
# dropped, whatever failed; then one line on STDERR names the directory. It is
# a warning and not a death: the search this close belongs to has its result,
# and what is in doubt is the pair kept for a LATER run.
sub fb_close () {
    my @failed;
    for my $store (['bad.brk', $FbBad], ['tahy.brk', $FbTahy], ['pozice.brk', $FbPozice]) {
        my ($file, $db) = @$store;
        next unless defined $db;
        push @failed, "$file: $BerkeleyDB::Error" if $db->db_close();
    }
    ($FbBad, $FbTahy, $FbPozice) = (undef, undef, undef);
    if (defined $FbEnv) {
        push @failed, "the environment: $BerkeleyDB::Error" if $FbEnv->close();
        $FbEnv = undef;
    }
    if (defined $FbLock) {
        close($FbLock);    # releases the flock
        $FbLock = undef;
    }
    my $dir = $FbDir;
    $FbDir = undef;
    warn 'FirstbetBerk: the stores in ' . ($dir // '(no directory)') . ' did not close cleanly (' . join('; ', @failed)
        . ") -- what is kept there may be incomplete\n"
        if @failed;
    return;
}

# Main-thread disk sweep for the THREADED drivers (2026-08-06). In ithreads a
# worker's BerkeleyDB files stay OS-locked despite db_close/env-close until the
# thread is JOINED, so every in-thread remove/unlink above silently fails and
# per-game dirs pile up (measured: 64 orphaned bwd dirs / 94 GB + kept tahy.brk
# 112 GB after one long-limit campaign). Call this from the MAIN thread with no
# env open, after thread JOIN, and NAME THE GAMES IT MAY TOUCH:
#   * G<id>b goes (BACKWARD scratch has no cross-run value),
#   * a game in @$solved loses its directories whole (their caches are spent),
#   * any other named game is trimmed to the persistent bad.brk + tahy.brk pair
#     (pozice.brk is per-run trajectory scratch).
# G<id> is the shared layout and G<id>_<MODE> a racing driver's per-mode one;
# both belong to game <id> and are swept by the same rule.
#
# IT TAKES A LIST OF GAMES BECAUSE IT USED TO TAKE THE WHOLE HOME (2026-09-12).
# It read the directory and swept everything it found, so a driver finishing a
# one-game run deleted the stores of every OTHER game -- including a run alive
# in another process at that moment, which then went on searching into file
# handles with no name left, reporting nothing, its directories simply gone.
# That is what happened to game 32102's live BACKWARD while a canary run of
# game 1 was ending. It is the same fault that retired fb_purge_forward on
# 2026-09-09 -- code deleting a directory its caller does not own -- which left
# the engine then and survived here, in the driver's tidy-up, for three days.
# Debris of killed runs is therefore no longer collected as a side effect of
# some other run: a sweep touches what its caller names and nothing else.
sub fb_sweep ($games, $solved = []) {
    $FbHome = berk_root() . '/Firstbet';
    return unless -d $FbHome;
    my %sg = map(($_, 1), @$solved);
    for my $g (@$games) {
        next unless $g =~ /\A\d+\z/a;
        File::Path::remove_tree("$FbHome/G${g}b") if -d "$FbHome/G${g}b";
        for my $d (grep {-d} glob("$FbHome/G$g $FbHome/G${g}_*")) {
            if   ($sg{$g}) { File::Path::remove_tree($d) }
            else           { unlink "$d/pozice.brk" }
        }
    }
    return;
} ## end sub fb_sweep


# fb_purge_forward WAS HERE AND IS GONE (2026-09-09). It removed the forward dir
# G<id> when a game was solved by a mode that never opens it (BACKWARD/ORDER),
# the leftover Bad+Tahy of earlier timed-out forward modes being stale scratch a
# forward solve would have reclaimed. Two reasons it went: fb_sweep(@solved)
# does the same thing already, from the main thread, where the operating system
# will actually let the files go; and it was the one call that deleted a
# directory its own caller did not own -- harmless while modes ran one after
# another, and exactly the 2026-08-18 failure once they race, since it would
# unmap the env of a mode still searching. The engine no longer deletes
# anything but its own; the drivers sweep after the join.


sub fb_setbad ($pozice) {
    fb_open(length $pozice) unless defined $FbPozice;
    $FbBad->db_put($pozice, 1) and fb_fail('bad.brk', $FbDir);
    return;
}


sub fb_isbad ($pozice) {
    fb_open(length $pozice) unless defined $FbPozice;
    my $status = $FbBad->db_get($pozice, my $value);
    return 1 if $status == 0;
    return 0 if $status == $NotFound;
    fb_fail('bad.brk', $FbDir);
}


# Positions are fixed-length within a game, so children pack as concatenated
# a-strings (no Storable). L is read per call from the key length -- NOT a state var
# -- so one process may solve games of different nbox.
sub fb_tahy_set ($pozice, $kids) {
    fb_open(length $pozice) unless defined $FbPozice;
    my $L = length $pozice;
    $FbTahy->db_put($pozice, pack("(a$L)*", @$kids)) and fb_fail('tahy.brk', $FbDir);
    return;
}


sub fb_tahy_get ($pozice) {
    fb_open(length $pozice) unless defined $FbPozice;
    my $status = $FbTahy->db_get($pozice, my $value);
    if ($status) {
        return undef if $status == $NotFound;
        fb_fail('tahy.brk', $FbDir);
    }
    my $L = length $pozice;
    return [unpack("(a$L)*", $value)];
}


sub fb_tahy_del ($pozice) {
    fb_open(length $pozice) unless defined $FbPozice;
    my $status = $FbTahy->db_del($pozice);
    fb_fail('tahy.brk', $FbDir) if $status and $status != $NotFound;
    return;
}


# Seen + Parent combined in one Pozice record: the value IS the parent position (a
# fixed-length string, or '' for Start), so existence = Seen and the value = Parent.
# Firstbet does not use a solution length, so no na* pack is needed.
sub fb_pos_set ($pozice, $parent) {
    fb_open(length $pozice) unless defined $FbPozice;
    $FbPozice->db_put($pozice, $parent) and fb_fail('pozice.brk', $FbDir);
    return;
}


sub fb_pos_present ($pozice) {
    fb_open(length $pozice) unless defined $FbPozice;
    my $status = $FbPozice->db_get($pozice, my $value);
    return 1 if $status == 0;
    return 0 if $status == $NotFound;
    fb_fail('pozice.brk', $FbDir);
}


sub fb_pos_parent ($pozice) {
    fb_open(length $pozice) unless defined $FbPozice;
    my $status = $FbPozice->db_get($pozice, my $value);
    return $value if $status == 0;
    return undef  if $status == $NotFound;
    fb_fail('pozice.brk', $FbDir);
}


sub fb_pos_del ($pozice) {
    fb_open(length $pozice) unless defined $FbPozice;
    my $status = $FbPozice->db_del($pozice);
    fb_fail('pozice.brk', $FbDir) if $status and $status != $NotFound;
    return;
}


# Live record count of the Pozice DB = the seen-set size (the disk analog of RAM's
# scalar %Parent -- discover() adds a record, node_del() removes one). Exact stat (no
# DB_FAST_STAT), called only at solve end, so the O(n) traversal cost is
# negligible; no hand-maintained running counter to drift. A search that never
# touched a store has none open and counts nothing.
sub fb_pos_count () {
    return defined $FbPozice ? $FbPozice->db_stat->{hash_nkeys} : 0;
}


# --- BACKWARD scratch env (%Bseen, FirstbetBerk's pull search) ---------------
# ONE store since Firstbet 3.5 (2026-09-05): the value of a key is the packed
# undoing push followed by the parent's key ('' for a seed), so the node table
# bnode.brk that used to sit beside it is gone -- the seam stores whatever
# string the engine hands it and gives it back unchanged.
#
# The store itself opens at the first write (fb_bseen_set), for the same reason
# as the forward three: the record's length is known only then. It opens with
# DB_TRUNCATE -- scratch never inherits a prior beam, and a file left by a
# killed run is cut to nothing by the filesystem instead of being emptied page
# by page, which is what truncate() did here until 2026-10-06 (the lesson the
# g_* family had learned on 2026-09-06 and this one had not).
sub fb_bwd_init ($gameid, $cachesize = 536870912) {
    fb_bwd_close() if defined $FbBwdEnv or defined $FbBseen;    # a solve that died left its store open (see fb_init)
    $FbHome   = berk_root() . '/Firstbet';
    $FbBwdDir = sprintf('%s/G%db', $FbHome, $gameid);
    make_dir($FbBwdDir);
    pool_config($FbBwdDir, $cachesize);
    $FbBwdEnv = BerkeleyDB::Env->new(
        -Home  => $FbBwdDir,
        -Flags => DB_CREATE | DB_INIT_MPOOL | DB_PRIVATE,
        )
        or die "Cannot open FirstbetBerk BWD env for game $gameid ($FbBwdDir): $BerkeleyDB::Error\n";
    return;
}


# THE STORE IS CLOSED DEAD (2026-10-07). Nothing ever reads bseen.brk again --
# the next search truncates it and the sweep removes its directory -- so its
# pages are not worth one write: db_close(DB_NOSYNC) leaves them where they are,
# and a reopen with DB_TRUNCATE cuts the file to nothing, after which the
# environment has no page of it left to put on disk. Measured on a full pool
# (the scratch probe of 2026-10-06, its --dead arm): 0 GB written at the close,
# against the whole pool. The removal of the directory is fb_sweep's, for the
# reason above fb_close.
sub fb_bwd_close () {
    if (defined $FbBseen) {
        $FbBseen->db_close(DB_NOSYNC);
        $FbBseen = undef;
        if (defined $FbBwdEnv) {
            my $again = BerkeleyDB::Hash->new(
                -Filename => 'bseen.brk', -Flags => DB_CREATE | DB_TRUNCATE, -Env => $FbBwdEnv,
            );
            $again->db_close(DB_NOSYNC) if defined $again;
        }
    }
    my $failed;
    if (defined $FbBwdEnv) {
        $failed   = "$BerkeleyDB::Error" if $FbBwdEnv->close();
        $FbBwdEnv = undef;
    }
    my $dir = $FbBwdDir;
    $FbBwdDir = undef;
    warn 'FirstbetBerk: the environment in ' . ($dir // '(no directory)') . " did not close cleanly ($failed)\n"
        if defined $failed;
    return;
}


# The value is the engine's own record -- pack('nn', from, to) . parent key, or
# '' for a seed -- stored and returned as it is.
sub fb_bseen_set ($pozice, $value) {
    unless (defined $FbBseen) {
        confess("BACKWARD's store was written with no environment open\n") unless defined $FbBwdEnv;
        $FbBseen = open_hash($FbBwdEnv, 'bseen.brk', DB_CREATE | DB_TRUNCATE, 2 * length($pozice) + 4);
    }
    $FbBseen->db_put($pozice, $value) and fb_fail('bseen.brk', $FbBwdDir);
    return;
}


# Before the first write there is no store, and nothing in it.
sub fb_bseen_get ($pozice) {
    return undef unless defined $FbBseen;
    my $status = $FbBseen->db_get($pozice, my $value);
    return $value if $status == 0;
    return undef  if $status == $NotFound;
    fb_fail('bseen.brk', $FbBwdDir);
}


sub fb_bseen_has ($pozice) {
    return 0 unless defined $FbBseen;
    my $status = $FbBseen->db_get($pozice, my $value);
    return 1 if $status == 0;
    return 0 if $status == $NotFound;
    fb_fail('bseen.brk', $FbBwdDir);
}


# --- THE GAME'S OWN env: one directory per game, every store inside ----------
# (2026-08-31, USER: "vsechny databaze do jednoho vlastniho adresare s vlastnim
# ENV".) Used by the WHOLE optimal-solver line -- Solver, Solver01
# and SolverBerk -- so whichever of them runs, it finds the work the others left
# behind. That is what killed sb_adopt: the Bad and Tahy of a game used to live
# in the shared env for Solver.pm and in a private one for SolverBerk, and a
# one-way MOVE was the only bridge between them, so after it Solver.pm could no
# longer see its own cache. Better solutions come in groups, so the natural next
# step after SolverBerk finds one is a fast RAM run -- and that was exactly the
# step the split made impossible.
#
# Two kinds of store live here, and the difference is the whole design:
#   Bad + Tahy       FACTS about the game. A deadlock stays a deadlock and a move
#                    list is a property of the board, so both survive a TIMEOUT
#                    and are removed only when the game is SOLVED.
#   Pozice/Bucket/Expanded  STATE of one run. Opened EMPTY by the caller that
#                    asks for them ($spill), thrown away at every reset and
#                    deleted when the env closes -- by g_close on a TIMEOUT and by
#                    END on a Ctrl-C alike (USER 2026-09-06). Nothing ever reads
#                    them across runs, so a file of theirs on disk is debris.
#
# WHY THE RUN STATE IS THROWN AWAY AND NEVER EMPTIED IN PLACE (2026-09-06). It
# used to be truncate()d: at open, again in the solver's initvars, again in the
# seed threader, and in FIFO at every compaction. BerkeleyDB never shrinks a
# file, and a Hash keeps its bucket count across truncate(), so emptying an
# already-empty Hash walks every page of the file it once filled -- measured:
# 1 GB of empty pozice.brk costs 0.98 s against 1.22 s for the full one, and
# that is with the pages on disk, through a cache smaller than the file. Game
# 13268 after a killed run had pozice.brk and expanded.brk at 17 GB each, so a
# new solve_berk spent its first minutes walking some 100 GB of dead pages
# before the first pop (USER: "zaba na prameni je g_bq_reset"). Now a reset is
# db_close(DB_NOSYNC) -- the dirty pages of a file about to die are not written
# -- and a reopen with DB_TRUNCATE, which is a filesystem truncate to zero:
# 0.14 s on the same 1 GB, 0.02 s once the file is small, and the mpool marks
# the old file dead so nothing of it is flushed into the new one (verified by
# an env close/reopen after the reset). fb_init above had learned the same
# lesson for FirstbetBerk's pozice.brk and deletes the leftover before its env
# opens; this seam resets DURING a run, so it needs the in-env form.
#
# Pozice carries sol AND parent (pack 'na*'). The open list is a BTREE keyed by
# pack('N', cost) . pack('N', sequence): big-endian, so the lexicographic order
# BerkeleyDB keeps IS the numeric cost order and a cursor on the first record is
# the cheapest waiting position -- the disk shape of Solver.pm 2.0's bucket
# queue. Duplicates of a relaxed node are allowed (the sequence number keeps
# keys unique); Expanded is the membership DB that identifies them at pop time.
# It replaces the FIFO Heap + Inheap pair of the 1.x regime -- g_init deletes
# those files if a kept dir still carries them.
#
# DB_PRIVATE: only the .brk data files touch disk and the mpool $cachesize is the
# RAM ceiling -- but it also means ONE PROCESS AT A TIME. That used to be true of
# SolverBerk alone; now that Solver.pm shares this home it is true of it too, so
# g_init takes a lock file and refuses rather than corrupting.
# g_close($delete) removes the whole per-game dir on SOLVED.
my $GHome;    # <root>/Optimal, read off the root at every init
my ($GEnv, $GDir, $GBad, $GTahy, $GPozice, $GBucket, $GBqCur, $GExpanded, $GLock);
my $GBqSeq = 0;


# Open one run-state store EMPTY, whatever the file held before: DB_TRUNCATE has
# the filesystem cut the old file to zero (see the header for why this and not
# truncate()). Called at open and at every reset; the caller closes the old
# handle first.
sub _g_run_open ($file, $btree = 0) {
    my $db = $btree
        ? BerkeleyDB::Btree->new(
            -Filename => $file, -Flags => DB_CREATE | DB_TRUNCATE, -Env => $GEnv,
            -Pagesize => 16384,
            )
        : BerkeleyDB::Hash->new(
            -Filename => $file, -Flags => DB_CREATE | DB_TRUNCATE, -Env => $GEnv,
            -Pagesize => 16384, -Ffactor => 64,
            );
    return $db // die "Cannot open $file in $GDir: $BerkeleyDB::Error\n";
}


# Open this game's own env and attach its stores. $spill also opens the run
# scratch, empty -- SolverBerk asks for it, the RAM solvers do not.
#
# THE LOCK. DB_PRIVATE gives no inter-process protection whatsoever, and this home
# is now shared by four modules, so two runs on one game would quietly corrupt each
# other's files. The lock file is taken non-blocking and held for the life of the
# env; a second run dies at once, naming the game, instead of finding out later.
# It is a separate file from the databases on purpose -- BerkeleyDB may rewrite
# those, and a lock must outlive any such rewrite.
sub g_init ($gameid, $cachesize = 536870912, $spill = 0) {

    # A process that solves several games in a row must close one before opening
    # the next: reassigning $GLock would drop the previous game's lock silently,
    # and its env would keep running unlocked.
    confess("g_init: another game's env is still open -- call g_close first\n")
        if defined $GEnv;

    # -Cachesize is taken modulo 4 GB by the module's XS (see pool_config), so a
    # pool of 4, 8 or 12 GB would silently be NO pool. The fb_* family passes
    # the size through DB_CONFIG instead; this family keeps -Cachesize ON
    # PURPOSE, because its stores still have 16 KB and 32 KB pages and a real
    # pool of such pages is slow to close once it has been full (see
    # open_hash) -- the move to pool_config belongs together with the page
    # sizes, measured. Until then a size the XS cannot carry is refused, and
    # before anything is created or locked.
    confess("g_init: a pool of $cachesize bytes -- the optimal solver's stores take at most 3 GB"
            . " (the BerkeleyDB module keeps the size in 32 bits)\n")
        if $cachesize > 3 * 1073741824;
    $GHome = berk_root() . '/Optimal';
    $GDir  = sprintf('%s/G%d', $GHome, $gameid);
    make_dir($GDir);
    $GLock = take_lock($GDir, 'g_init');
    $GEnv  = BerkeleyDB::Env->new(
        -Home      => $GDir,
        -Flags     => DB_CREATE | DB_INIT_MPOOL | DB_PRIVATE,
        -Cachesize => $cachesize,
    );
    unless (defined $GEnv) {
        close($GLock);    # a lock on an environment that never opened
        $GLock = undef;
        die "Cannot open env for game $gameid ($GDir): $BerkeleyDB::Error\n";
    }
    $GBad = BerkeleyDB::Hash->new(
        -Filename => 'bad.brk', -Flags => DB_CREATE, -Env => $GEnv,
        -Pagesize => 8192, -Ffactor => 128,
        )
        or die "Cannot open Bad db for game $gameid: $BerkeleyDB::Error\n";
    $GTahy = BerkeleyDB::Hash->new(
        -Filename => 'tahy.brk', -Flags => DB_CREATE, -Env => $GEnv,
        -Pagesize => 32768, -Ffactor => 32,
        )
        or die "Cannot open Tahy db for game $gameid: $BerkeleyDB::Error\n";
    if ($spill) {

        # The 1.x run-state files have no reader any more; a kept dir (TIMEOUT
        # of an old run) may still carry them, so reclaim the disk here.
        for my $stale ('heap.brk', 'inheap.brk') {
            unlink "$GDir/$stale" if -f "$GDir/$stale";
        }
        $GPozice   = _g_run_open('pozice.brk');    # scratch: never inherit a prior run's Seen/Parent
        $GBucket   = _g_run_open('bucket.brk', 1);
        $GExpanded = _g_run_open('expanded.brk');
        $GBqCur    = $GBucket->db_cursor()
            or die "Cannot open Bucket cursor for game $gameid: $BerkeleyDB::Error\n";
        $GBqSeq = 0;
    }
} ## end sub g_init


# $delete is true only on SOLVED: the game is done, so the whole directory goes --
# facts and scratch alike. On a TIMEOUT the FACTS stay for the next run, whichever
# module that turns out to be, and the run state goes with the run: nothing ever
# reads it back, and a killed run had been leaving two 17 GB files behind (see the
# header). END calls this too, so a Ctrl-C -- the drivers' SIGINT handler dies, and
# END runs -- cleans up the same way (USER 2026-09-06).
sub g_close ($delete = 0) {
    if (defined $GBqCur) {    # a cursor must close before its database
        $GBqCur->c_close();
        $GBqCur = undef;
    }
    for my $db ($GBad, $GTahy, $GPozice, $GBucket, $GExpanded) {
        $db->db_close() if defined $db;
    }
    ($GBad, $GTahy, $GPozice, $GBucket, $GExpanded) = (undef, undef, undef, undef, undef);
    if (defined $GEnv) {
        $GEnv->close();
        $GEnv = undef;
    }
    if (defined $GLock) {
        close($GLock);    # releases the flock
        $GLock = undef;
    }
    if (defined $GDir and -d $GDir) {
        if ($delete) {
            File::Path::remove_tree($GDir);    # SOLVED -> reclaim disk (whole per-game dir)
        }
        else {                    # the env is closed: a plain unlink is safe now
            unlink "$GDir/$_" foreach grep {-f "$GDir/$_"} ('pozice.brk', 'bucket.brk', 'expanded.brk');
        }
    }
    $GDir = undef;
} ## end sub g_close


sub g_setbad ($pozice) {
    $GBad->db_put($pozice, 1);
    return;
}


sub g_isbad ($pozice) {
    my $value;
    return $GBad->db_get($pozice, $value) == 0 ? 1 : 0;
}


sub g_tahy_get ($pozice) {
    my $value;
    return undef if $GTahy->db_get($pozice, $value);
    my $unp = sprintf('(a%dn)*', length $pozice);
    return [unpack($unp, $value)];
}


sub g_tahy_set ($pozice, $tahy) {
    my $unp = sprintf('(a%dn)*', length $pozice);
    $GTahy->db_put($pozice, pack($unp, @$tahy));
    return;
}


sub g_tahy_del ($pozice) {
    $GTahy->db_del($pozice);
    return;
}


# Pozice = sol (16-bit) + parent position (a-string, '' for the root).
sub g_pos_set ($pozice, $parent, $sol) {
    $GPozice->db_put($pozice, pack('na*', $sol, $parent));
    return;
}


sub g_pos_present ($pozice) {
    my $value;
    return $GPozice->db_get($pozice, $value) == 0 ? 1 : 0;
}


sub g_pos_getsol ($pozice) {
    my $value;
    return undef if $GPozice->db_get($pozice, $value);
    return (unpack('na*', $value))[0];
}


sub g_pos_getparent ($pozice) {
    my $value;
    return undef if $GPozice->db_get($pozice, $value);
    return (unpack('na*', $value))[1];
}


sub g_pos_del ($pozice) {
    $GPozice->db_del($pozice);
    return;
}


# restart() drops all Seen/Parent -- throw the Pozice file away and open a new one.
sub g_pos_reset () {
    $GPozice->db_close(DB_NOSYNC);
    $GPozice = _g_run_open('pozice.brk');
    return;
}


# Insert $pozice at cost $sol. No membership test: a duplicate of a relaxed
# node is allowed (the caller skips the stale copy at pop time); the sequence
# number keeps the key unique so nothing overwrites anything.
sub g_bq_add ($pozice, $sol) {
    $GBucket->db_put(pack('NN', $sol, ++$GBqSeq), $pozice);
    return;
}


# Take the cheapest waiting position: cursor to the FIRST key (BTree order =
# numeric cost order), delete it, return (cost, position). Empty queue -> ().
sub g_bq_pop () {
    my ($key, $value) = ('', '');
    return () if $GBqCur->c_get($key, $value, DB_FIRST);
    $GBqCur->c_del();
    return ((unpack('NN', $key))[0], $value);
}


# Free everything queued at cost >= $bestlen after an improvement: nothing
# there can ever be popped again. Returns how many records went, so the caller
# can keep its open-list counter honest. Runs once per improvement.
sub g_bq_trim ($bestlen) {
    my ($key, $value) = (pack('NN', $bestlen, 0), '');
    my $n = 0;
    my $status = $GBqCur->c_get($key, $value, DB_SET_RANGE);
    while ($status == 0) {
        $GBqCur->c_del();
        ++$n;
        $status = $GBqCur->c_get($key, $value, DB_NEXT);
    }
    return $n;
}


# The seed threader empties the open list -- throw Bucket+Expanded away and open
# new ones. The cursor closes before its database and is reopened on the new one.
sub g_bq_reset () {
    $GBqCur->c_close();
    $GBucket->db_close(DB_NOSYNC);
    $GExpanded->db_close(DB_NOSYNC);
    $GBucket   = _g_run_open('bucket.brk', 1);
    $GExpanded = _g_run_open('expanded.brk');
    $GBqCur    = $GBucket->db_cursor()
        or die "Cannot reopen Bucket cursor: $BerkeleyDB::Error\n";
    $GBqSeq = 0;
    return;
}


# Expanded membership: the disk shape of Solver.pm 2.0's low %Seen bit. A
# separate DB rather than a flag inside the Pozice record, because setting a
# flag there would be a read-modify-write of a variable-length record on every
# expansion -- the same trade the 1.x Inheap note already settled.
sub g_exp_set ($pozice) {
    $GExpanded->db_put($pozice, 1);
    return;
}


sub g_exp_has ($pozice) {
    my $value;
    return $GExpanded->db_get($pozice, $value) == 0 ? 1 : 0;
}


# ...and its per-key delete, which every sibling store already had (g_pos_del,
# g_tahy_del, fb_pos_del, fb_tahy_del) and this one lacked because the DIAL regime never
# clears the bit: a popped cost is final. Both other modes of the portfolio do clear it
# (2026-09-02) -- ASTAR when a cheaper route RE-OPENS an expanded node, and FIFO at every
# pop, where the same store carries the QUEUED bit instead of the expanded one. The
# reasoning behind keeping membership in its own DB (see g_exp_set) argues nothing
# against a delete.
sub g_exp_del ($pozice) {
    $GExpanded->db_del($pozice);
    return;
}


sub END {
    fb_close()     if defined $FbEnv;    # DB_PRIVATE env: flush the .brk files, keep the dir
    fb_bwd_close() if defined $FbBwdEnv;
    g_close()      if defined $GEnv;     # the game's env: flush, keep the dir, drop the lock
}

1;

__END__

=head1 NAME

Games::Sokoban::Solver::Berkeley - the on-disk stores of the two BerkeleyDB twins

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Berkeley ();
    $Games::Sokoban::Solver::Berkeley::ROOT = '/scratch/soko-solver';

    # the Firstbet twin's family: one directory per level, the caches kept
    Games::Sokoban::Solver::Berkeley::fb_init($id, 512 * 2**20, $mode_tag);
    ...
    Games::Sokoban::Solver::Berkeley::fb_close();
    Games::Sokoban::Solver::Berkeley::fb_sweep([$id], [$id_if_solved]);

    # the optimal solver's family: the whole search in the level's directory
    Games::Sokoban::Solver::Berkeley::g_init($id, 512 * 2**20, 1);
    ...
    Games::Sokoban::Solver::Berkeley::g_close($solved);

=head1 DESCRIPTION

The seam under L<Games::Sokoban::Solver::Firstbet::Berk> and
L<Games::Sokoban::Solver::Optimal::Berk>: every search structure those twins
keep on disk is a BerkeleyDB database in a private environment of the level's
own, under the root directory C<$ROOT> (or the environment variable
C<SOKOBAN_BERK_ROOT>). The header of the module says which stores exist and
which survive a run. One process at a time per directory; a second opener is
refused with the directory named.

The L<BerkeleyDB> module is a recommendation of the distribution, not a
prerequisite: this module is loaded only when the caller turns the branch on.

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
