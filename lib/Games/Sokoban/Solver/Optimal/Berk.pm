package Games::Sokoban::Solver::Optimal::Berk;

# BerkeleyDB-backed twin of Games::Sokoban::Solver::Optimal: the same solve() contract,
# the same search, but EVERY search structure -- the deadlock cache, the move cache, the
# positions with their cost and parent, and the cost-ordered open list -- lives in one
# isolated per-level DB_PRIVATE env instead of in RAM. Only the .brk data files touch
# disk; the memory pool ($CACHE, bytes, at most 3 GB) is the RAM ceiling, so an optimal
# solve can run far past what RAM alone allows; the deadlock and move caches stay in the
# level's directory after a TIMEOUT and the next run on the level starts from them.
# $MAX_GB (GiB) caps the RAM of the whole machine and aborts with a MEMCAP stop. Use
# this module when Optimal would not fit in memory; Optimal otherwise.
#
# This is a STORAGE twin: it may differ from Optimal in WHERE the search structures
# live, never in which nodes get searched or in what solve() returns. It is
# Games::Sokoban::SolverBerk 3.2 of the Sokoban project with the same storage cut away
# that Optimal lost (the database writes, the SQL log, the statistics); $LastStatus names
# a stop and $ON_IMPROVED reports every improvement, as in Optimal. The notes below are
# the project's, kept because they say why the disk shapes are what they are.
#
# Synced to v2.0 (DIAL) on 2026-09-01 -- the ordering IS a change to which nodes get
# searched, so the twin carries the whole regime; see Solver.pm's v2.0 note for the
# design and the measurements. The disk shapes of the RAM structures:
#   @Bucket + $CurMin  ->  bucket.brk, a BTREE keyed pack('N',cost).pack('N',seq):
#                          big-endian keys make BerkeleyDB's lexicographic order the
#                          numeric cost order, so a cursor on the FIRST record is the
#                          cheapest waiting position and its key carries $CurMin.
#                          Duplicates of a relaxed node are allowed, as in RAM.
#   the %Seen low bit  ->  expanded.brk, a membership DB. NOT a flag inside the Pozice
#                          record: that would be a read-modify-write of a variable-
#                          length record per expansion -- the same trade the 1.x
#                          Inheap note settled. A difference in WHERE, which the
#                          contract allows.
#   trim_tail()        ->  g_bq_trim, one ranged cursor sweep from pack('N',$Bestlen).
#   scalar @{$Bucket[$CurMin]}
#                      ->  %BucketCnt, a KEPT count instead of a measured one: info()'s
#                          last column would otherwise mean walking one cost's whole
#                          range with a cursor, millions of records, every printout.
# The 1.x FIFO heap.brk + inheap.brk pair has no reader any more; g_init deletes the
# files from kept dirs. v1.7's one-env-per-game layout is unchanged.
# v2.1 (2026-09-01) carries the baseline's LEVEL PROFILE: one solve_level row per cost
# level the dial enters, width from %BucketCnt. See record_level().
# v3.1 (2026-09-06) carries the baseline's BAND: FIFO queues an unseen child only within
# $BAND boxes of the record's box track (Solver.pm, "THE BAND", explains it). Again WHICH
# NODES ARE SEARCHED, so the twin must carry it. The band's own state (%BandMemo,
# @BandCfg) stays in RAM: the memo is capped ($BAND_MEMO_MAX) and the track is a few
# hundred bit strings, both small beside the mpool. $MAX_RESTARTS went with 3.1.
# v3.2 (2026-09-07) carries the baseline's change to it: when the heap runs dry under a
# band that dropped children, the band is DROPPED and the same record's surroundings are
# searched unrestricted (3.1 widened it one box at a time); an improvement brings it back.
# v3.3 (2026-09-17, the baseline's OVERRUN -- DIAL and ASTAR past $LIMIT while the level
# profile says the proof is near) is NOT carried: a stopping rule, not a change to which
# nodes are searched, and this twin's runs are the open-ended ones anyway.
# v3.0 (2026-09-02) carries the baseline's PORTFOLIO -- the three modes DIAL/ASTAR/FIFO.
# WHICH NODES ARE SEARCHED is not a storage difference, so the twin carries the whole
# regime, exactly as it had to carry v1.8's queueing verdict and v2.0's ordering. Two
# things map onto the seam and are worth stating before the code:
#   * FIFO NEEDS NO NEW DATABASE. bucket.brk is a BTREE keyed pack('NN', cost, seq), so
#     inserting everything at cost 0 makes the cursor's order the INSERTION order -- which
#     is precisely a FIFO. g_bq_reset() is already "empty the open list", i.e. the
#     compaction. Nothing on disk changes shape.
#   * expanded.brk CARRIES THE OPPOSITE MEANING IN FIFO. In the bucket modes it is the
#     EXPANDED set (the baseline's low %Seen bit); in FIFO it is the QUEUED set, set at
#     the enqueue and CLEARED at the pop -- which is why Games::Berkeley needed g_exp_del,
#     the one operation that store had never had.
our $VERSION = '0.01';
use v5.42;
use feature 'keyword_all', 'keyword_any', 'declared_refs', 'refaliasing';
use experimental ('keyword_any', 'keyword_all', 'refaliasing', 'declared_refs');
use warnings FATAL => ('uninitialized');
no warnings('once', 'recursion');
use Carp        ('confess');
use Time::HiRes ('tv_interval', 'gettimeofday');
use Storable    ('thaw', 'dclone');
use List::Util  ('max');
use Compress::Zlib;
use Term::ANSIColor;
use Games::Sokoban::Solver::Berkeley ();
use Games::Sokoban::Solver::Console ('backline', 'backlinen', 'podil');
use Games::Sokoban::Solver::Data   ();
use Games::Sokoban::Solver::Memory ();

# $LIMIT seconds (0 = none), $CACHE the pool in bytes, $MAX_GB the whole machine's RAM
# ceiling in GiB (0 or undef = off): the search stops as MEMCAP, returned as TIMEOUT and
# named in $LastStatus.
our ($LIMIT, $CACHE, $MAX_GB);

# What stopped the last solve() when it returned TIMEOUT: 'TIMEOUT', 'MEMCAP' or 'IGNORE'.
our $LastStatus = '';

# Called with ($path, $seconds_into_the_run) at every improvement, if set; @Track keeps
# them (seq, cas, sollen, pushes, counter, n_open, nstart, path).
our $ON_IMPROVED;
our @Track;

# THE RACE SIGNAL and $QUIET, the same two things Optimal carries: a driver that races
# modes sets $RACE_FLAG (a shared hash, id -> true) and $RACE_GID, and a loser notices at
# its 4096-pop checkpoint and leaves with 'IGNORE'. $QUIET: 0 everything, 1 no progress
# line, 2 no durable line either (the red OUT OF MEMORY line is never muted).
our ($RACE_FLAG, $RACE_GID);
our $QUIET = 0;
sub race_lost() {$RACE_FLAG && $RACE_GID && $RACE_FLAG->{$RACE_GID}}
my (
    %Game,   @Goal,    @Target,   %Cm,   %Cmk,      @Cg,       %Pis,
    %InvPis, @Baggage, %Priority, @Maze, $Has_hole, $Has_wall, $Has_corridor,
    $Hole,   $Wall,    $Corridor, $Blok, $BlokVec,  $W
   );
my ($Nbox, %Sols, %SolReal, %Bags, $corridors, $holes, $pu);

# No @Bucket/%Seen/%Parent/%Tahy/%MemBad here: every one of those lives in the per-game
# BerkeleyDB env (see the storage seam). $N_Open/$MaxOpen/$CurMin stay -- counters and
# one integer, not data structures. $CurMin is fed by the popped key's cost (the BTree
# hands the minimum over, nobody walks buckets here) and read by info() as the live
# lower bound, exactly as in the baseline.
my ($Bestbet, $Bestlen, @Buf, $N_Open, $O_Open, $MaxOpen, $CurMin);

# FIFO's "a betterment landed" flag. Its open list needs no variable here: the queue on
# disk IS the heap (see the v3.0 note in the header).
my ($Improved);

# ASTAR: cell -> shortest push distance from that cell to ANY goal, built once per game in
# initvars and only when the mode asks for it. Identical to the baseline's, including the
# two corrections that are easy to lose: a cell with no row in `steps` gets 0, and so does
# every GOAL -- without `$MinSteps[$_] = 0 foreach @Goal` the estimate charges a box that
# has already arrived, stops being a lower bound, and 37928 comes back 78 against 77.
my (@MinSteps);

# THE PORTFOLIO, mirrored from the baseline (Solver.pm v3.0, 2026-09-02) -- what the three
# modes are and why there are three is documented there and not repeated here.
#   'DIAL'   cost-ordered buckets; a popped cost is final, the proof lands at
#            $CurMin >= $Bestlen, and solve_level's width is a level's whole population.
#   'ASTAR'  the same ordered by f = g + h; an expanded node must be RE-OPENABLE, which
#            on this seam means exp_del.
#   'FIFO'   the 1.8 regime: insertion order, SPFA relaxation with the re-queue verdict,
#            restart() as frontier compaction. The mode this twin most wants, because the
#            games that need a database at all are the ones where the proof is out of
#            reach and MINING a shorter path is the whole ambition.
our $MODE = 'DIAL';

# $MODE resolved ONCE in solve(), as $PERSIST is in the baseline: this module runs under
# `warnings FATAL => uninitialized` and the branch must never sit in the child loop.
my ($Fifo, $H_on) = (0, 0);

# FIFO's own contract, identical to the baseline's. $nStart is the only writer of
# solve_stats.nstart; the bucket modes leave it 0.
my $nStart           = 0;
my $RESTART_MIN_OPEN = 100_000;
my $RESTART_RATIO    = 0.5;

# THE BAND, identical to the baseline's (Solver.pm, "THE BAND", explains it): FIFO queues
# an unseen child only within $Band_cur boxes of the record's box track (the box
# configurations its solution passes through); a heap that ran dry with drops is no proof,
# so the band is dropped and the same record is searched around unrestricted, and an
# improvement brings it back at $BAND. $BAND = 0 = no band (the pre-3.1 FIFO).
our $BAND = 2;
my $BAND_MEMO_MAX = 4_000_000;
my ($Band_cur, $Band_dropped, $Band_total, $Cw, $Band_zero, %BandMemo, @BandCfg);

# What the LAST PRINTED info() line said, so the next one can decide whether that line is
# worth keeping (USER 2026-09-01). $O_Open was always this; the record and the dial's
# level joined it when the separate "FOUND:" line went away -- see info().
my ($O_Bestbet, $O_CurMin);

# The level the dial last entered; the pop in hledej() compares the cost it got against
# this one and notes when the dial has moved on. See record_level().
my ($Level_at);

# $N_Open BROKEN DOWN BY COST -- what the baseline reads straight off the open list as
# scalar @{$Bucket[$CurMin]}, and what this twin cannot: the queue is a BTREE keyed
# (cost, seq), so counting the entries of one cost means walking that whole range with a
# cursor, and one cost level can hold millions of positions -- a per-printout sweep at
# info()'s 6s cadence. So the count is KEPT instead of measured, in exactly the three
# places $N_Open itself is kept honest: bucket_add (+1), the pop in hledej (-1) and
# trim_tail (the whole range >= $Bestlen goes at once). Every insert goes through
# bucket_add, so it is exact by construction; the hash holds one small integer per cost
# level ever used, a few hundred at most. Display only -- nothing reads it but info().
my (%BucketCnt);
my ($bc, $counter, $timer, $Probed, $Cas, $Gameid);

# The frontier's effective branching factor, reported by info() as $Pushed/$Expanded --
# how many children of an average parent actually END UP ON THE HEAP (USER 2026-08-31;
# the same column in all four solvers). Neither existing counter answers it: $bc counts
# CANDIDATES, before the bound and the deadlock battery, and $counter counts every pop,
# including those dropped without being expanded. restart()'s own direct pushes are
# deliberately not in $Pushed -- those are not children of anything. Read it against 1:
# above 1 the frontier grows, below 1 it drains, and here the heap is a database, so the
# same ratio is also the disk it is costing.
my ($Pushed,     $Expanded);
my ($PaintId,    @Blk,    @Vis, @Dist, $Poradi);
my ($PaintId_fr, @Vis_fr, @Buf_fr);    # dedicated state for paint_fr/is_frozen (boxes merged into @Vis_fr)
my ($PocketMin,  %FrozenMemo);         # is_frozen memoization: paint()'s pocket-min + verdict cache (small, RAM-only)

# The corridor and hole pattern tables, read once per process from the distribution's
# data directory.
$corridors = Games::Sokoban::Solver::Data::load('corridor_pattern.stor');
$holes     = Games::Sokoban::Solver::Data::load('hole_pattern.stor');
$LIMIT     = 30;

# --- storage seam ------------------------------------------------------------
# EVERY search structure lives in the isolated per-game DB_PRIVATE env (g_*): the
# persistent pair Bad + Tahy, the trajectory scratch Seen/Parent (a Pozice DB), the
# cost-ordered Bucket queue and the Expanded membership DB. Only the .brk data files
# touch disk; RAM is bounded by the mpool.
#
# There is no RAM mode here on purpose. This module used to carry $BERK/$SPILL toggles
# whose "off" settings reproduced, respectively, Solver.pm with $PERSIST=0 and Solver.pm
# with $PERSIST=1 -- i.e. a second implementation of code that already exists next door,
# kept alive only to be its own A/B reference. Solver.pm IS the reference (and
# ai/smoke_solverberk.pl compares against it), so the toggles were dead weight and a
# standing risk of the two halves drifting apart. Removed 2026-07-16.
#
#   $CACHE  -> per-game mpool ceiling in bytes = the RAM cap for the offloaded state
#              (disk grows unbounded, RAM does not). Default 512 MB, at most 3 GB.
#   $MAX_GB -> if set, abort the search (MEMCAP) once TOTAL system RAM in use exceeds
#              this many GiB (Memory::used_gb(), one kernel call) -- a safety net so a
#              run dies cleanly with its best-so-far instead of taking the machine down.
$CACHE //= 536870912;    # 512 MB

# The level's own env (<root>/Optimal/G<id>): a run that times out leaves its Bad and
# Tahy waiting there for the next one. The third argument asks for the run scratch
# (Pozice + Bucket + Expanded), which g_init opens empty and g_close deletes -- those
# belong to one run, the two above to the level. A reset of the scratch (bq_reset,
# seen_reset) throws the files away and opens new ones, never truncate(): on a Hash
# that re-walks every page the file ever held, and a killed run had left 17 GB of them.
sub bad_init  ($g) {Games::Sokoban::Solver::Berkeley::g_init($g, $CACHE, 1)}
sub bad_close ($s) {Games::Sokoban::Solver::Berkeley::g_close($s)}
sub setbad    ($p) {Games::Sokoban::Solver::Berkeley::g_setbad($p)}
sub isbad     ($p) {Games::Sokoban::Solver::Berkeley::g_isbad($p)}

# Uniform "arrayref or undef", matching Solver.pm's tahy_get contract.
sub tahy_get ($p)     {Games::Sokoban::Solver::Berkeley::g_tahy_get($p)}
sub tahy_set ($p, $k) {Games::Sokoban::Solver::Berkeley::g_tahy_set($p, $k)}

# Seen/Parent: a node's best sollen + its parent. seen_get returns the sollen or undef;
# node_set writes sollen+parent together.
sub seen_has   ($p)           {Games::Sokoban::Solver::Berkeley::g_pos_present($p)}
sub seen_get   ($p)           {Games::Sokoban::Solver::Berkeley::g_pos_getsol($p)}
sub parent_get ($p)           {Games::Sokoban::Solver::Berkeley::g_pos_getparent($p)}
sub node_set   ($p, $par, $s) {Games::Sokoban::Solver::Berkeley::g_pos_set($p, $par, $s)}

# The cost-ordered open list and the expanded set (the disk shapes of the
# baseline's @Bucket and the %Seen low bit -- see the header). bq_pop returns
# (cost, position) or the empty list when the queue is drained.
sub bq_pop ()    {Games::Sokoban::Solver::Berkeley::g_bq_pop()}
sub bq_trim ($b) {Games::Sokoban::Solver::Berkeley::g_bq_trim($b)}
sub bq_reset ()  {%BucketCnt = (); Games::Sokoban::Solver::Berkeley::g_bq_reset()}
sub exp_set ($p) {Games::Sokoban::Solver::Berkeley::g_exp_set($p)}
sub exp_has ($p) {Games::Sokoban::Solver::Berkeley::g_exp_has($p)}
sub exp_del ($p) {Games::Sokoban::Solver::Berkeley::g_exp_del($p)}
sub seen_reset () {Games::Sokoban::Solver::Berkeley::g_pos_reset()}

# Insert $p at cost $g, keeping $N_Open/$MaxOpen honest. The only place the open
# list grows. No membership test: a duplicate of a relaxed node is allowed and
# recognized at pop time, exactly as in the baseline.
sub bucket_add ($p, $g) {
    my $f = $H_on ? $g + odhad($p) : $g;    # ASTAR orders by f, DIAL by g

    # THE DIAL DESCENDS TO MEET AN INSERT BELOW IT, as in the baseline: our estimate is
    # admissible but not consistent, so under ASTAR f can fall, and clamping such an
    # insert into the bucket being emptied would leave a node with a TRUE f below the
    # bound still waiting when the proof is declared. Cannot happen in DIAL.
    $CurMin = $f if $f < $CurMin;
    Games::Sokoban::Solver::Berkeley::g_bq_add($p, $f);
    ++$N_Open;
    ++$BucketCnt{$f};    # the same count, split by cost, for info()'s last column
    ++$Pushed;           # numerator of info()'s children-per-parent
    $MaxOpen = $N_Open if $N_Open > $MaxOpen;
}

# FIFO's enqueue -- the disk shape of the baseline's heap_add. Everything goes in at cost
# 0, so the BTree's key order is the INSERTION order and the cursor pops oldest-first;
# expanded.brk is the QUEUED set here, which is what makes the membership test (and the
# clear at the pop) possible at all.
sub queue_add ($p) {
    return if exp_has($p);
    Games::Sokoban::Solver::Berkeley::g_bq_add($p, 0);
    exp_set($p);
    ++$N_Open;
    ++$Pushed;    # numerator of info()'s children-per-parent
    $MaxOpen = $N_Open if $N_Open > $MaxOpen;
}

# ASTAR: the estimate of a packed position -- the sum over its boxes of the shortest push
# distance to any goal. Identical to the baseline's; nothing is stored per node.
sub odhad ($p) {
    my (undef, @boxes) = unpack($pu, $p);
    my $h = 0;
    $h += $MinSteps[$_] // 0 foreach @boxes;
    return $h;
}

# Free everything queued at cost >= the just-tightened $Bestlen; one ranged
# cursor sweep in the env, counted so $N_Open stays honest. Runs per improvement.
sub trim_tail () {
    $N_Open -= bq_trim($Bestlen);
    delete @BucketCnt{ grep {$_ >= $Bestlen} keys %BucketCnt };    # the sweep took those levels whole
}

# THE LEVEL PROFILE: the moment the dial enters a cost level, noted when it has really
# moved on. (In the Sokoban project this wrote one row per level into a table, with the
# level's width from %BucketCnt -- in DIAL the level's complete population, under ASTAR a
# snapshot, since the estimate is not consistent and the dial can descend; a level was
# recorded on its first arrival only. FIFO has no levels.)
sub record_level () {
    $Level_at = $CurMin;
}

sub clearvars() {
    ($Band_cur, $Band_dropped, $Band_total) = (0, 0, 0);
    %BandMemo     = ();
    @BandCfg      = ();
    $Bestbet      = undef;
    $Bestlen      = undef;
    $bc           = undef;
    $counter      = undef;
    $timer        = undef;
    $CurMin       = 0;
    $Probed       = 0;
    $Pushed       = undef;
    $Expanded     = undef;
    $Cas          = undef;
    $Gameid       = undef;
    $Blok         = undef;
    $BlokVec      = undef;
    $Corridor     = undef;
    $Has_corridor = undef;
    $Has_hole     = undef;
    $Has_wall     = undef;
    $Hole         = undef;
    $Nbox         = undef;
    $W            = undef;
    $Wall         = undef;
    $PaintId      = undef;
    $PaintId_fr   = undef;
    $PocketMin    = undef;
    %FrozenMemo   = ();
    $Poradi       = undef;
    @Vis          = ();
    @Blk          = ();
    @Dist         = ();
    @Vis_fr       = ();
    %Bags         = ();
    @Cg           = ();
    %Cm           = ();
    %Cmk          = ();
    %Game         = ();
    %Priority     = ();
    %Pis          = ();
    %InvPis       = ();
    %Sols         = ();
    @Target       = ();

    # Bucket/Expanded/Seen/Parent/Tahy/Bad are not RAM structures here -- they live in
    # the per-game env, which bad_init() (re)opens and bad_close() disposes of.
    $Improved = 0;
    @MinSteps = ();
    @Baggage  = ();
    @Buf      = ();
    @Buf_fr   = ();
    @Goal     = ();
    @Maze     = ();
} ## end sub clearvars

sub initvars ($gameid, $gm) {
    clearvars();
    bad_init($gameid);                                                # opens the per-game env; every seam call below needs it
    %Game = %{ thaw(uncompress($gm)); };
    my $maze = $Game{'code'};
    $maze =~ tr/,//d;
    $maze =~ tr/45678/00233/;
    @Maze         = split(//a, $maze, 0);
    $Game{'maze'} = &dclone(\@Maze);
    @Goal         = @{ $Game{'goal'}; };
    @Target       = ();
    $Target[$_]   = 1 foreach @Goal;                                  # cell-indexed goal flag (was %Target)
    %Cm           = %{ $Game{'cm'};  };
    %Cmk          = %{ $Game{'cmk'}; };
    @Cg           = ();
    $Cg[$_]       = $Game{'cg'}{$_} foreach keys %{ $Game{'cg'} };    # cell-indexed walk graph (was %Cg)
    @Baggage      = @{ $Game{'baggage'}; };
    $W            = $Game{'w'};

    # Parser already chose the position pack template ('C*' or 'n*') and packed
    # %Sols with it -- reuse it for every pack/unpack of a (man,@baggage) tuple.
    $pu        = $Game{'vzp'};
    $Cw        = ($pu =~ /^n/) ? 2 : 1;                                   # bytes per cell in a packed position (band keys)
    $Band_zero = "\0" x int(($Game{'w'} * $Game{'h'} + 7) / 8);           # one bit per cell of the board
    %Pis       = (-1, 'l', 1, 'r', $W, 'd', -$W, 'u');
    %InvPis    = reverse %Pis;
    $Nbox      = scalar @Baggage;
    %Priority  = %{ $Game{'order'}; };
    ($Has_hole, $Has_wall, $Has_corridor) = @Game{ 'has_hole', 'has_wall', 'has_corridor' };
    ($Blok, $BlokVec)                     = _blok_both($Game{'blok'});    # arrays (cold callers) + vecs (tahy hot path)

    # ASTAR: the per-cell push-distance floor, built only when the mode asks for it.
    # 'Inf' marks an unreachable goal in the blob and must not enter the minimum.
    @MinSteps = ();
    if ($H_on) {
        my $steps = $Game{'steps'};
        for my $cell (keys %{$steps}) {
            my $best;
            for my $g (values %{ $steps->{$cell} }) {
                next       if $g eq 'Inf';
                $best = $g if !defined $best or $g < $best;
            }
            $MinSteps[$cell] = $best // 0;
        }
        $MinSteps[$_] = 0 foreach @Goal;    # a box already home needs no push; see the declaration
    }
    $Hole     = &dclone($Game{'hole'})     if $Has_hole;
    $Wall     = &dclone($Game{'walls'})    if $Has_wall;
    $Corridor = &dclone($Game{'corridor'}) if $Has_corridor;
    bq_reset();                             # the env is open by now (bad_init above)
    seen_reset();
    $Bestbet = undef;
    $Bestlen = 'Inf';
    %Sols    = %{ $Game{'sols'} };

    # Stop only at a REAL (tailless) solution; a checkpoint box-on-P entry carries a
    # move-string tail and is expanded like any other node (see Solver.pm).
    %SolReal     = ();
    $SolReal{$_} = 1 foreach grep {$Sols{$_} !~ /[A-Za-z]/} keys %Sols;
    $PaintId     = 0;
    $PaintId_fr  = 0;
    $Poradi      = 0;
    @Blk         = (0) x scalar @Maze;
    @Vis         = (0) x scalar @Maze;
    @Dist        = (0) x scalar @Maze;
    @Vis_fr      = (0) x scalar @Maze;
} ## end sub initvars

# blok loader (dual-read REMOVED 2026-08-06, memory project_blok_vec_bench):
# the blob carries TRIMMED BIT VECTORS (new Parser; tools/update_block.pl
# converted the whole DB). Build both runtime forms once at load: vecs for
# is_bad's hot tahy() gear, arrays for the cold callers that do not maintain
# a box vector. An array pattern now dies LOUDLY -- it can only mean a
# pre-conversion blob (an old backup), which would otherwise compute garbage
# silently.
sub _blok_both ($src) {
    my (%arr, %vec);
    foreach my $bx (keys %{ $src // {} }) {
        my $row = $src->{$bx};
        foreach my $t (keys %$row) {
            my (@as, @vs);
            foreach my $p (@{ $row->{$t} }) {
                die "array blok pattern (pre-2026-08-06 blob? run tools/update_block.pl)" if ref $p;
                push @as, [grep {vec($p, $_, 1)} 0 .. 8 * length($p) - 1];
                push @vs, $p;
            }
            $arr{$bx}{$t} = \@as;
            $vec{$bx}{$t} = \@vs;
        }
    }
    return (\%arr, \%vec);
} ## end sub _blok_both

sub paint($man, @baggage) {
    ++$PaintId;
    $Blk[$_]    = $PaintId for @baggage;
    $Vis[$man]  = $PaintId;
    $Dist[$man] = 1;
    $Buf[0]     = $man;
    my $bt   = 1;
    my $pmin = $man;    # canonical id of man's reachable region -> is_frozen memo key (free during the flood)
    for (my $bh = 0; $bh < $bt; ++$bh) {
        my $x = $Buf[$bh];
        my $d = $Dist[$x] + 1;
        foreach my $t (@{ $Cg[$x] }) {
            next if $Vis[$t] == $PaintId || $Blk[$t] == $PaintId;    # @Vis first (Firstbet v2.4 #2)
            $Vis[$t]    = $PaintId;
            $Dist[$t]   = $d;
            $Buf[$bt++] = $t;
            $pmin       = $t if $t < $pmin;
        }
    }
    $PocketMin = $pmin;
} ## end sub paint

# Reachability-only painter for is_frozen() / goal-corral check, with its own
# globals so it never disturbs @Vis/@Blk/$PaintId used by paint()/tahy().
# No distance tracking needed -- callers only check reachability.
sub paint_fr($man, @baggage) {
    ++$PaintId_fr;
    $Vis_fr[$_]   = $PaintId_fr for @baggage;    # boxes as Vis-walls: flood skips them, one-compare
    $Vis_fr[$man] = $PaintId_fr;                 # inner test (Firstbet v2.5 merge)
    $Buf_fr[0]    = $man;
    my $bt = 1;
    for (my $bh = 0; $bh < $bt; ++$bh) {
        my $x = $Buf_fr[$bh];
        foreach my $t (@{ $Cg[$x] }) {
            next if $Vis_fr[$t] == $PaintId_fr;
            $Vis_fr[$t] = $PaintId_fr;
            $Buf_fr[$bt++] = $t;
        }
    }
} ## end sub paint_fr

# Detect a frozen (permanently immovable) box cluster among @nomove -- boxes
# that already had no legal push in tahy()'s main loop. Boxes in the cluster
# may unfreeze each other's neighbours as the man's reachable area changes
# with them as walls, so iterate to a fixed point.
# Returns ('frozen', ()) if any frozen box is off-goal (true deadlock);
# ('', @frozen) if all frozen boxes sit on goals (caller should still check
# whether the frozen wall encloses an open goal -- goal-corral);
# ('', ()) if nothing stays frozen.
sub is_frozen ($man, @nomove) {

    # Memoize the branch 0/1 verdict on (pocket-min, sorted nomove). $PocketMin (from
    # paint()'s last flood in tahy) canonically ids the man's reachable region: a cell
    # reachable under all-boxes-walls is reachable under frozen-only-walls too, so
    # (pocket-min, nomove) determines the man's paint_fr component -> the whole verdict.
    # Branch 2 (all frozen on goals) is NOT cached: the caller's goal-corral check needs
    # a FRESH @Vis_fr, so it must re-flood -- fall through and recompute. (RAM cache; small.)
    my $key = $PocketMin . '|' . join(',', sort {$a <=> $b} @nomove);
    if (defined(my $v = $FrozenMemo{$key})) {
        return ('frozen', ()) if $v == 1;
        return ('',       ()) if $v == 0;
    }
    my %frozen = map(($_, 1), @nomove);
    while (1) {
        my @still_frozen;
        paint_fr($man, keys %frozen);
        foreach my $bx (keys %frozen) {
            my $movable = 0;
            foreach my $t (@{ $Cmk{$bx} }) {
                next if exists $frozen{$t};
                my $stance = $Cm{$bx}{$t};
                next if exists $frozen{$stance};    # merge: a frozen box on the stance blocks it (was @Blk_fr)
                next unless $Vis_fr[$stance] == $PaintId_fr;
                $movable = 1;
                last;
            }
            push @still_frozen, $bx unless $movable;
        }
        last if @still_frozen == scalar keys %frozen;
        %frozen = map(($_, 1), @still_frozen);
    } ## end while (1)
    unless (%frozen) {$FrozenMemo{$key} = 0; return ('', ())}
    for (keys %frozen) {
        unless ($Target[$_]) {$FrozenMemo{$key} = 1; return ('frozen', ())}
    }
    return ('', keys %frozen);    # branch 2: on-goal, not cached (goal-corral needs @Vis_fr)
} ## end sub is_frozen

sub is_bad ($bx, $t, $t_bag, $vb = undef) {

    # blok check, two gears (synced with Firstbet v2.10): tahy() maintains the
    # child box BIT VECTOR $vb and pays one string AND + eq per pattern
    # (':5.42' enables 'bitwise', so string AND is the DOTTED &. operator; a
    # trimmed pattern vec is safe on both sides of a length mismatch because
    # &. truncates to the shorter operand). Without $vb: the old array scan.
    if (defined $vb) {
        my $bvs = $BlokVec->{$bx} && $BlokVec->{$bx}{$t};
        if ($bvs) {
            foreach my $pv (@$bvs) {
                return 1 if ($vb &. $pv) eq $pv;
            }
        }
    }
    else {
        my $blok = $Blok->{$bx} && $Blok->{$bx}{$t};
        if ($blok) {
            foreach my $bl (@$blok) {
                return 1 if CORE::all {exists $t_bag->{$_};} @$bl;
            }
        }
    }
    if ($Has_wall) {
        if (defined(my $wall = $Wall->{$t})) {
            foreach my $w (@$wall) {
                my $n = 0;
                foreach my $s (@{ $w->[1] }) {
                    ++$n if exists $t_bag->{$s};
                }
                return 1 if $n > $w->[0];
            }
        }
    }
    if ($Has_corridor) {
        if (defined(my $cor = $Corridor->{$bx} && $Corridor->{$bx}{$t})) {
            if ($cor->[2] =~ /^0+$/a) {
                my $n = 0;
                foreach my $s (@{ $cor->[0]; }) {
                    ++$n if exists $t_bag->{$s};
                }
                return 1 if $n > 1;
            }
            else {
                $Maze[$_] =~ tr/03/47/ foreach keys %$t_bag;
                my $str = join('', @Maze[@{ $cor->[0]; }]);
                $Maze[$_] =~ tr/47/03/ foreach keys %$t_bag;
                confess("is_bad: a corridor shape the table does not know: '$cor->[2]' ($cor->[1], cells @{ $cor->[0] })")
                    unless exists $corridors->{ $cor->[2] };
                return 1 unless ($corridors->{ $cor->[2] }{ $cor->[1] } // {})->{$str};
            }
        } ## end if (defined(my $cor = ...))
    } ## end if ($Has_corridor)
    if ($Has_hole) {
        if (defined(my $hole = $Hole->{$bx} && $Hole->{$bx}{$t})) {
            $Maze[$_] =~ tr/03/47/ foreach keys %$t_bag;
            my $str = join('', @Maze[@{ $hole->[0]; }]);
            $Maze[$_] =~ tr/47/03/ foreach keys %$t_bag;
            die "UNKONWN Hole pattern $$hole[1]" unless exists $holes->{ $hole->[1] };
            return 1                             unless $holes->{ $hole->[1] }{$str};
        }
    }
    return '';
} ## end sub is_bad

# Marks $pozice bad and propagates that knowledge both ways through the
# already-cached search tree, instead of leaving it as an isolated fact:
#   - downward: if $pozice itself was already expanded (has a %Tahy entry),
#     every one of its cached children is equally unreachable/pointless --
#     nothing reachable from a deadlock can ever be used -- so mark them bad
#     too (recursively, since some of THEM may have been expanded as well).
#   - upward: $pozice was one of $Parent{$pozice}'s cached candidate moves.
#     Remove it from that parent's %Tahy entry. If that empties the parent's
#     move list, the parent has no surviving move left either -- it's bad
#     too, discovered only now, possibly many moves after it was first
#     proposed as a candidate.
sub set_bad ($pozice) {
    return if isbad($pozice);
    setbad $pozice;
    if (my $th = tahy_get($pozice)) {
        foreach my ($child, $step)(@$th) {
            next if isbad($child);
            set_bad($child);
        }
    }
    my $parent = parent_get($pozice);
    my $th;
    if (defined $parent && length $parent && ($th = tahy_get($parent))) {
        my @kept;
        for (my $i = 0; $i < @$th; $i += 2) {
            push @kept, $th->[$i], $th->[$i + 1] unless $th->[$i] eq $pozice;
        }
        if (@kept < @$th) {

            # Persist the trimmed move list back (a fresh put under Berkeley; an
            # in-place replacement under RAM). Both backings see the change.
            tahy_set($parent, \@kept);
            set_bad($parent) unless @kept;
        }
    }
} ## end sub set_bad

sub tahy ($pozice) {
    if (my $cached = tahy_get($pozice)) {
        return @$cached;
    }
    my ($man, @baggage) = unpack($pu, $pozice);
    my ($step, $value, $s, $child, @tahy, @nomove);
    %Bags = map(($_, 1), @baggage);

    # $vb = the box set as a bit vector, mutated in LOCKSTEP with %Bags below,
    # so is_bad's hot blok test is one string AND per pattern (synced with
    # Firstbet v2.10). Built once per position, amortized over all candidates.
    my $vb = '';
    vec($vb, $_, 1) = 1 foreach @baggage;
    paint($man, @baggage);
    @tahy = ();
    foreach my $bx (@baggage) {
        my $movable = 0;

        # Reuse %Bags as the child box-set instead of a fresh $t_bag hash per candidate (drop
        # the pushed box, add the target around is_bad(), restore both; %Bags is full again
        # after the loop for the goal-corral grep). (Firstbet v2.4 #4.)
        delete $Bags{$bx};
        vec($vb, $bx, 1) = 0;
        foreach my $t (@{ $Cmk{$bx}; }) {
            next if exists $Bags{$t};
            $s = $Cm{$bx}{$t};
            next unless $Vis[$s] == $PaintId;
            ++$movable;
            $step = $Dist[$s];
            my @nb = grep($_ != $bx, @baggage);
            my $i  = 0;
            ++$i while $i < @nb && $nb[$i] < $t;
            splice(@nb, $i, 0, $t);
            $child = pack($pu, $bx, @nb);

            if (isbad($child)) {
                next;
            }
            $Bags{$t} = 1;
            vec($vb, $t, 1) = 1;
            if (is_bad($bx, $t, \%Bags, $vb)) {
                set_bad($child);
            }
            else {
                push @tahy, $child, $step;
            }
            delete $Bags{$t};
            vec($vb, $t, 1) = 0;
        } ## end foreach my $t (@{ $Cmk{$bx}...})
        $Bags{$bx} = 1;
        vec($vb, $bx, 1) = 1;
        push @nomove, $bx unless $movable;
    } ## end foreach my $bx (@baggage)

    # Frozen-cluster / goal-corral deadlock check -- can reject this position
    # even when @tahy is non-empty, since a permanently stuck subset of boxes
    # dooms the position regardless of what other boxes can still do.
    if (@nomove) {
        my ($frozen_bad, @frozen_set) = is_frozen($man, @nomove);
        if ($frozen_bad) {
            set_bad($pozice);
            return ();
        }
        if (@frozen_set) {
            my @open = grep {!exists $Bags{$_}} @Goal;
            if (@open) {

                # NO repaint: is_frozen()'s last fixed-point paint_fr($man, keys %frozen) IS
                # paint_fr($man, @frozen_set) and nothing repaints @Vis_fr in between; reuse it.
                # (Firstbet v2.6, +12.3%.)
                for my $g (@open) {
                    if ($Vis_fr[$g] != $PaintId_fr) {
                        set_bad($pozice);
                        return ();
                    }
                }
            }
        } ## end if (@frozen_set)
    } ## end if (@nomove)
    if (@tahy) {
        tahy_set($pozice, [@tahy]);
        return @tahy;
    }
    else {
        set_bad($pozice);
        return ();
    }
} ## end sub tahy

sub cesta ($m, $target, $baggage) {
    my ($bh, $bt, $x, $p, $d, @buf, %path);
    %path     = ($m, '');
    $path{$_} = undef foreach (@{ $baggage; });
    $buf[0]   = $m;
    ($bh, $bt) = (0, 1);
    while ($bh != $bt) {
        $x = $buf[$bh++];
        $p = $path{$x};
        foreach my $t (@{ $Cg[$x]; }) {
            if (not exists $path{$t}) {
                $path{$t} = $p . $Pis{ $t - $x };
                return $path{$t} if $t == $target;
                $buf[$bt++] = $t;
            }
        }
    }
    die 'NO PATH';
} ## end sub cesta

sub get_path (@postup) {
    my ($father, $fm, @sb, $sm, @fb, $source, $target, %fh, %sh, $path, $move, $man);
    $father = shift @postup;
    $path   = '';
    foreach my $son (@postup) {
        ($fm, @fb) = unpack($pu, $father);
        ($sm, @sb) = unpack($pu, $son);
        %fh = map(($_, 1), @fb);
        %sh = map(($_, 1), @sb);
        ($source) = grep((!$sh{$_}), @fb);
        confess("SOURCE @fb  |  @sb") unless defined $source;
        ($target) = grep((!$fh{$_}), @sb);
        confess("TARGET @fb  |  @sb") unless defined $target;
        $move = uc $Pis{ $target - $source };
        $man  = $Cm{$source}{$target};
        confess("$source -> $target") unless defined $man;

        if ($fm == $man) {
            $path .= $move;
        }
        else {
            $path .= cesta($fm, $man, \@fb) . $move;
        }
        $father = $son;
    } ## end foreach my $son (@postup)
    return $path;
} ## end sub get_path

# The end-of-search line, coloured by outcome -- the same scheme Firstbet has carried
# since 2026-08-31 (USER 2026-09-02). Green proved it, yellow spent its whole budget, and
# RED is everything else: MEMCAP tore the run out on memory, UNSOLVABLE is a tripwire
# saying the search exhausted a state space no real game exhausts. Neither is a clock
# running out, and both used to look exactly like one. Durable line, hence backlinen.
sub barva ($reason, $ending) {
    state $colour = { 'SOLVED', 'bright_green', 'TIMEOUT', 'bright_yellow' };
    backlinen(colored($ending, $colour->{$reason} // 'bright_red')) if $QUIET < 2;
}

# Periodic progress printout, throttled and callable from anywhere in this
# module (not just hledej()'s own loop) -- specifically so a long bublej()
# cascade (measured up to ~1.85M nodes / 9s for one top-level call, see
# project_bublej_cascade_timing) still shows visible progress instead of
# looking hung for the whole time it has hledej() blocked. $Probed gates the
# (non-free, at this call volume) time() check itself to once every 10000
# calls; only once that passes do we check whether 6 real seconds have
# actually elapsed since the last printout. Purely cosmetic -- info() never
# aborts anything; $LIMIT enforcement lives solely in hledej()'s own loop.
sub info() {
    return if ++$Probed % 10000;
    return unless time() - $Cas > 6;
    my $doba = tv_interval($timer);

    # THE TWO LINES WORTH KEEPING (USER 2026-09-01). backline() overwrites its predecessor,
    # which is right for a progress line and wrong for the two moments that carry a fact:
    #   * a newline BEFORE the print leaves the line that still showed the OLD record
    #     standing -- that is what the separate "FOUND: n" say() used to announce, now said
    #     by the line itself, with its clock and counters beside it;
    #   * a newline AFTER it keeps the FIRST line of a new $CurMin, whose bucket count is
    #     the widest that level will ever show (once the dial stands in a bucket, nothing
    #     can be inserted into it -- every insert lands at least one move above).
    print {*STDERR} "\n" if !$QUIET and $Bestlen != $O_Bestbet;
    if    ($QUIET) { }    # no progress line: a threaded caller's workers would only interleave them
    elsif ($Fifo) {

        # FIFO has no ordered frontier, so the last two columns have nothing to say: there
        # is no lower bound to print and no bucket to count. Nine columns, as in 1.8.
        backline(
            sprintf '%10d ... %12d %9d %6d %9s %5.2f %12.2f %12.0f %12.0f %8d',
            $Gameid, $counter, $N_Open, $N_Open - $O_Open, podil($N_Open, $MaxOpen, 2),
            ($Expanded ? $Pushed / $Expanded : 0),    # children per parent that reach the heap
            $doba,
            $bc / $doba,
            $counter / $doba, $Bestlen
        );
    }
    else {
        print {*STDERR} "\n" if $CurMin != $O_CurMin;
        backline(
            sprintf '%10d ... %12d %9d %6d %9s %5.2f %12.2f %12.0f %12.0f %8d %5d %9d',
            $Gameid, $counter, $N_Open, $N_Open - $O_Open, podil($N_Open, $MaxOpen, 2),
            ($Expanded ? $Pushed / $Expanded : 0),    # children per parent that reach a bucket
            $doba,
            $bc / $doba,
            $counter / $doba, $Bestlen,
            $CurMin,                                  # live lower bound -- nothing shorter than this exists
            $BucketCnt{$CurMin} // 0                  # how much is still waiting AT that bound
        );
    }
    ($O_Open, $O_Bestbet, $O_CurMin) = ($N_Open, $Bestlen, $CurMin);
    $Cas = time();
} ## end sub info

# Walks %Parent from $pozice back to the root, returning the full
# root-to-$pozice sequence. Used both to feed restart() at seed time and to
# build the final move string at the end of solve().
sub parent_postup ($pozice) {
    my @postup = ($pozice);
    my $p      = $pozice;

    # A chain that meets itself has no stop at all ('' at the root is the only
    # one), so the loop would unshift until the machine dies -- and a truncated
    # chain would put a WRONG path into bestbet. A tripwire since 2026-09-10,
    # when restart() stopped building such a chain; see the baseline.
    my %on;
    while (($p = parent_get($p))) {    # '' at the root -> stops
        confess(
            sprintf(
                'parent_postup: the parent chain closes into a cycle on game %s after %d nodes',
                $Gameid // '?',
                scalar @postup
            )
            )
            if exists $on{$p};
        $on{$p} = undef;
        unshift @postup, $p;
    }
    return @postup;
} ## end sub parent_postup

# Pure conversion, no side effects on %Seen/%Parent/@Heap: replays a move
# string (e.g. firstbet.path -- lowercase = walk, uppercase = push) from the
# game's start position and returns the sequence of "pozice" after each
# completed push (root first, final position last). Validates every step
# against %Cg (walls) and the live box layout, confess()ing on mismatch
# rather than silently producing a wrong sequence.
sub cesta_na_pozice ($path) {
    my @baggage = @Baggage;
    my %bag_at  = map(($_, 1), @baggage);
    my $man     = $Game{'player'};
    my @postup  = (pack($pu, $man, @baggage));
    for my $ch (split //, $path) {
        my $d = $InvPis{ lc $ch };
        confess("cesta_na_pozice: unknown move char '$ch'") unless defined $d;
        my $target = $man + $d;
        confess("cesta_na_pozice: $man has no neighbour $target (wall?)")
            unless grep {$_ == $target} @{ $Cg[$man] };
        if ($ch eq lc $ch) {
            confess("cesta_na_pozice: walk into occupied cell $target") if $bag_at{$target};
            $man = $target;
            next;
        }
        confess("cesta_na_pozice: no box to push at $target") unless $bag_at{$target};
        my $new_t = $target + $d;
        confess("cesta_na_pozice: push target $new_t has no path (wall?)")
            unless grep {$_ == $new_t} @{ $Cg[$target] };
        confess("cesta_na_pozice: push target $new_t already occupied") if $bag_at{$new_t};
        delete $bag_at{$target};
        $bag_at{$new_t} = 1;
        $man            = $target;
        @baggage        = sort {$a <=> $b} keys %bag_at;
        push @postup, pack($pu, $man, @baggage);
    } ## end for my $ch (split //, $path)
    return @postup;
} ## end sub cesta_na_pozice

# Thread a known root-to-solution sequence into an EMPTY search. In DIAL and ASTAR that
# is all it is -- the SEED THREADER, called once from solve(); see the baseline for the
# completeness argument (the root goes into the queue at cost 0, so nothing reachable is
# cut off, and a path node holding a non-minimal cost is relaxed and staled before its own
# key ever reaches the cursor). In FIFO it is ALSO the COMPACTION, called again after
# every improvement want_restart() approves -- and note that bq_reset() here empties
# bucket.brk and expanded.brk TOGETHER, which is exactly right in both readings of that
# store: the expanded set and the queued set are both discarded with the frontier.
# The caller must set $Bestbet/$Bestlen (to $postup[-1] and its cost) beforehand.
sub restart (@postup) {
    ++$nStart if $Fifo;
    bq_reset();
    seen_reset();
    my $root = $postup[0];
    node_set($root, '', 0);
    $N_Open = 0;
    $O_Open = $Fifo ? 1 : 0;
    $CurMin = 0;
    my $pushed = $Pushed;    # the enqueues below count path nodes; put back at the end
    $Fifo ? queue_add($root) : bucket_add($root, 0);

    for my $i (0 .. $#postup - 1) {
        my $pozice      = $postup[$i];
        my $next_pozice = $postup[$i + 1];
        my $sol         = seen_get($pozice);
        my $next_sollen;

        # Only the step cost onto the next path node is needed here.
        foreach my ($child, $step)(tahy($pozice)) {
            next unless $child eq $next_pozice;
            $next_sollen = $sol + $step;
            last;
        }
        confess("restart: $next_pozice is not a child of its predecessor in \@postup")
            unless defined $next_sollen;

        # A path that comes back to a position it has already been in must not
        # rewire that position's parent: the chain from the later node runs back
        # through the earlier one and %Parent closes into a CYCLE, which
        # parent_postup() then walks for ever. Keep the FIRST arrival, which is
        # also the cheaper one. See the baseline for the whole story (2026-09-10).
        next if seen_has($next_pozice);
        node_set($next_pozice, $pozice, $next_sollen);
        unless (exists $SolReal{$next_pozice}) {
            $Fifo ? queue_add($next_pozice) : bucket_add($next_pozice, $next_sollen);
        }
    } ## end for my $i (0 .. $#postup...)
    $MaxOpen = $N_Open;

    # Threaded path nodes are not children of anything; keep the children-per-parent
    # metric clean (the enqueues above counted them). Put back, NOT zeroed: a zero here
    # wiped the whole numerator while $Expanded kept the whole solve, so after a FIFO
    # compaction info() showed a ratio under 1 on a frontier that was growing (USER
    # 2026-09-05).
    $Pushed = $pushed;

    # The band is a property of the record just threaded: rebuilt here, at the width
    # solve() has chosen ($BAND after an improvement, 0 = none after an exhaustion).
    # $Band_dropped describes the FRONTIER, not the band: zeroed here, where the frontier
    # was just discarded, and nowhere else (band_build() used to zero it, and the rebuild
    # WITHOUT a restart in hledej_fifo then passed a dry heap off as a proof -- game 7265
    # SOLVED at 55 against an optimum of 49; baseline 2026-09-06).
    $Band_dropped = 0;
    band_build(@postup) if $Fifo and $Band_cur;
} ## end sub restart

# THE BAND, byte for byte the baseline's (Solver.pm 3.2): positions are the same packed
# strings here, so the box part of a position is the same key and the track's
# configurations the same bit strings. RAM state on purpose -- see the v3.1 header note.
sub band_build (@postup) {
    %BandMemo = ();    # verdicts and witnesses were about the OLD band
    @BandCfg  = ();
    for my $p (@postup) {
        my $k = substr($p, $Cw);
        next if exists $BandMemo{$k};
        push @BandCfg, band_bits($p);
        $BandMemo{$k} = pack('Cn', 0, $#BandCfg);    # on the track: distance 0, its own witness
    }
    return;
}

sub band_bits ($p) {
    my $b = $Band_zero;
    my @c = unpack($pu, $p);
    shift @c;    # the player
    vec($b, $_, 1) = 1 for @c;
    return $b;
}

sub in_band ($child, $parent) {
    my $k = substr($child, $Cw);
    my $m = $BandMemo{$k};
    return length $m ? 1 : 0 if defined $m;
    my $cb = band_bits($child);
    my $pm = $BandMemo{ substr($parent, $Cw) };
    if (defined $pm and length $pm) {
        my $tp = unpack('xn', $pm);
        my $d  = $Nbox - unpack('%32b*', $cb &. $BandCfg[$tp]);
        if ($d <= $Band_cur) {
            $BandMemo{$k} = pack('Cn', $d, $tp);
            return 1;
        }
    }
    my ($best, $bt) = ($Nbox + 1, 0);
    for my $t (0 .. $#BandCfg) {
        my $d = $Nbox - unpack('%32b*', $cb &. $BandCfg[$t]);
        next unless $d < $best;
        ($best, $bt) = ($d, $t);
        last if $d == 0;
    }
    if ($best <= $Band_cur) {
        $BandMemo{$k} = pack('Cn', $best, $bt);
        return 1;
    }
    $BandMemo{$k} = '' if keys %BandMemo < $BAND_MEMO_MAX;
    return 0;
} ## end sub in_band

# FIFO ONLY: is the open list worth throwing away? Identical to the baseline's -- large
# enough ($RESTART_MIN_OPEN) and still mostly unexplored ($RESTART_RATIO of its peak).
sub want_restart () {
    return
           $RESTART_MIN_OPEN
        && $N_Open > $RESTART_MIN_OPEN
        && $N_Open / $MaxOpen > $RESTART_RATIO;
}

# A betterment the moment it is found: the path is built, kept in @Track and handed to
# $ON_IMPROVED, so a caller has every improvement before the solve ends.
sub save_improvement () {
    my $cas  = tv_interval($timer);
    my $path = get_path(parent_postup($Bestbet));
    push @Track, {
        'seq'     => scalar(@Track) + 1,
        'cas'     => $cas,
        'sollen'  => length $path,
        'pushes'  => ($path =~ tr/UDRL//),
        'counter' => $counter,
        'n_open'  => $N_Open,
        'nstart'  => $nStart,                # FIFO's restarts so far; 0 in the bucket modes
        'path'    => $path,
    };
    $ON_IMPROVED->($path, $cas) if $ON_IMPROVED;
} ## end sub save_improvement

# DIAL's bublej -- identical in contract to Games::Sokoban::Solver::bublej();
# see that module for the whole argument. The relaxation cascade pushes a
# cheaper arrival through continuations already on record (the threaded seed
# path, this game env's own tahy.brk -- which on a kept dir carries EVERY
# position any previous run of the optimal line ever expanded, so the cascade
# rides far here). No re-queue verdict (a relaxed waiting node MUST get its
# lower-bucket copy every time), no unwinding; an expanded node stops the walk
# by itself, its recorded cost being final.
#
# THAT LAST ONE HOLDS ONLY IN THE COST ORDER. Under ASTAR a popped cost is not final and
# an expanded node must be RE-OPENED -- and here that takes an explicit exp_del, because
# the expanded flag lives in its own database. In the RAM baseline the same thing happens
# implicitly: writing $Seen{$child} = $sollen * 2 clears the low bit as a side effect.
# This is the one place where the seam does NOT hide the difference, so it is spelled out.
sub bublej ($child, $pozice, $sollen) {
    node_set($child, $pozice, $sollen);
    exp_del($child) if $H_on;
    if (exists $SolReal{$child}) {
        if ($sollen < $Bestlen) {
            $Bestbet = $child;
            $Bestlen = $sollen;
            save_improvement();
            trim_tail();
        }

        # A terminal is never queued -- its cost IS $Bestlen and the queue never
        # reaches it.
        return;
    }
    bucket_add($child, $sollen);
    my $th = tahy_get($child) or return;
    foreach my ($grand, $step)(@$th) {
        info();
        my $sol = $sollen + $step;
        next if $sol >= $Bestlen;
        next if !$H_on and exp_has($grand);    # cost order: expanded = final
        my $gs = seen_get($grand);
        next unless defined $gs;               # the cascade never discovers
        next unless $gs > $sol;                # recurse only into a real improvement
        next if isbad($grand);
        bublej($grand, $child, $sol);
    }
    return;
} ## end sub bublej

# DIAL and ASTAR: take the cheapest waiting position, always -- the BTree cursor hands it
# over together with its ORDERING KEY, which feeds $CurMin, the live lower bound. The
# proof lands the moment that key reaches $Bestlen (everything behind it in the key order
# is dearer) or the queue drains entirely. Under ASTAR the key is f = g + h, which with an
# admissible h says the same thing about g. FIFO has its own loop below.
sub hledej () {
    while (1) {
        ++$counter;
        info();
        return 'TIMEOUT' if $LIMIT and tv_interval($timer) > $LIMIT and $N_Open / $MaxOpen > 0.7;

        # The race signal and the $MAX_GB safety net -- sampled every 4096 pops.
        unless ($counter & 4095) {
            return 'IGNORE' if race_lost();
            return 'MEMCAP' if $MAX_GB and Games::Sokoban::Solver::Memory::used_gb() > $MAX_GB;
        }

        # THE POPPED KEY IS THE ORDERING KEY, NOT THE COST. In DIAL the two are the same
        # thing; under ASTAR the key is f = g + h and the node's own cost g has to be read
        # from the record. Keeping them apart matters twice below: every child cost is
        # g + step, and the staleness test compares against the KEY.
        my ($key, $pozice) = bq_pop();
        return 'SOLVED' unless defined $pozice;    # queue drained: the whole space is expanded
        return 'SOLVED' if $key >= $Bestlen;       # nothing cheaper than the record remains

        # The level profile, BEFORE the two decrements: the baseline records a level while
        # the position it is about to pop still sits in the bucket, and %BucketCnt only
        # matches that if it is read before this pop is subtracted from it. Only on a level
        # never recorded -- under ASTAR the dial can descend and re-enter one.
        $CurMin = $key;
        record_level() if $key > $Level_at;
        --$N_Open;
        --$BucketCnt{$key};                   # every popped entry was counted in by bucket_add
        next if exp_has($pozice);             # already expanded -- a stale duplicate
        my $sol = seen_get($pozice) // -1;    # the position's own COST g

        # Relaxed while waiting: the cheaper copy did the work, and this entry's key no
        # longer matches what the node now costs. Valid in both modes only because no
        # insert is clamped (see bucket_add).
        next if ($H_on ? $sol + odhad($pozice) : $sol) != $key;
        next if isbad($pozice);
        exp_set($pozice);    # cheapest-first: this cost is FINAL
        ++$Expanded;         # a real parent: denominator of info()'s children-per-parent
        foreach my ($child, $step)(tahy($pozice)) {
            ++$bc;
            my $sollen = $sol + $step;
            next if $sollen >= $Bestlen;
            next if isbad($child);
            my $cs = seen_get($child);
            if (!defined $cs) {
                node_set($child, $pozice, $sollen);
                if (exists $SolReal{$child}) {

                    # Terminals are generated in cost order, so every one that gets
                    # past the $Bestlen test above IS an improvement. Never queued.
                    $Bestbet = $child;
                    $Bestlen = $sollen;
                    save_improvement();
                    trim_tail();
                    next;
                }
                bucket_add($child, $sollen);
            }
            elsif ($cs > $sollen and ($H_on or !exp_has($child))) {

                # A cheaper route to a node still waiting in a dearer key (or, under
                # ASTAR, to one already expanded -- bublej re-opens it with exp_del):
                # bublej() relaxes it, queues its copy at the better cost, and
                # pushes the saving onward through whatever continuations are on
                # record, reporting any terminal it improves on the way. An
                # EXPANDED child cannot be improved: its cost was the minimum of
                # the whole frontier once.
                bublej($child, $pozice, $sollen);
            }
        } ## end foreach my ($child, $step)(...)
    } ## end while (1)
} ## end sub hledej

# FIFO's cascade (v1.8), the disk twin of the baseline's bublej_fifo. Same two things
# separate it from the bucket modes' bublej above -- it RETURNS A VERDICT (is $child still
# worth queueing at all: only a child nobody has seen could make re-popping it worth
# anything, and this walk passes that very test) and it may ABANDON the walk when a
# restart is about to discard the work anyway.
#
# One thing the seam gives away free: the queued flag lives in its own database, so
# node_set() cannot disturb it. The RAM baseline has to preserve it by hand
# ($Seen{$child} = $sollen * 2 + ($Seen{$child} & 1)); here there is nothing to preserve.
sub bublej_fifo ($child, $pozice, $sollen) {
    node_set($child, $pozice, $sollen);
    if (exists $SolReal{$child}) {
        if ($sollen < $Bestlen) {
            $Bestbet  = $child;
            $Bestlen  = $sollen;
            $Improved = 1;
        }

        # A terminal's own cost IS $Bestlen by construction, so hledej_fifo() would pop it
        # and drop it again on `$sol >= $Bestlen` every single time.
        return 0;
    }

    # Never expanded -> nothing seen below it, and nothing but a real expansion will ever
    # generate its children: the cascade dead-ends here and only the queue can carry it on.
    my $th   = tahy_get($child) or return 1;
    my $need = 0;
    foreach my ($grand, $step)(@$th) {
        if ($Improved and want_restart()) {
            $need = 1;
            last;
        }
        info();
        my $sol = $sollen + $step;
        next if $sol >= $Bestlen;
        next if isbad($grand);
        my $gs = seen_get($grand);

        # A child nobody has seen is the one thing a re-expansion of $child could add,
        # because the cascade never discovers.
        if (!defined $gs) {
            $need = 1;
            next;
        }
        next unless $gs > $sol;    # recurse only into a real improvement
        queue_add($grand) if bublej_fifo($grand, $child, $sol);
    } ## end foreach my ($grand, $step)(...)
    return $need;
} ## end sub bublej_fifo

# FIFO's search loop (v1.8) over the database queue. The open list is unordered, so there
# is no bound to read off it and no early proof: 'SOLVED' means the queue GENUINELY RAN
# DRY. Note the pop CLEARS the queued flag -- in this mode expanded.brk is the queued set,
# which is the whole reason Games::Berkeley needed g_exp_del.
sub hledej_fifo () {
    while ($N_Open) {
        ++$counter;
        info();
        return 'TIMEOUT' if $LIMIT and tv_interval($timer) > $LIMIT and $N_Open > 0.7 * $MaxOpen;

        # The race signal and the $MAX_GB safety net -- sampled every 4096 pops.
        unless ($counter & 4095) {
            return 'IGNORE' if race_lost();
            return 'MEMCAP' if $MAX_GB and Games::Sokoban::Solver::Memory::used_gb() > $MAX_GB;
        }
        my (undef, $pozice) = bq_pop();
        last unless defined $pozice;    # the queue drained: same as $N_Open hitting 0
        exp_del($pozice);               # off the queue; the recorded cost is untouched
        --$N_Open;
        next if isbad($pozice);
        my $sol = seen_get($pozice) // -1;

        # NB: popped and NOT expanded -- no tahy is cached for it. This is precisely the
        # node bublej_fifo()'s cascade can dead-end on later, hence queue_add() there.
        next if $sol >= $Bestlen;
        ++$Expanded;    # a real parent: denominator of info()'s children-per-parent
        foreach my ($child, $step)(tahy($pozice)) {
            ++$bc;
            my $sollen = $sol + $step;
            next if $sollen >= $Bestlen;
            next if isbad($child);
            my $need;
            my $cs = seen_get($child);

            # THE BAND: an unseen child more than $Band_cur boxes off the record's track is
            # not queued and not recorded; counted, because a heap that ran dry with drops
            # is not a proof and solve() drops the band on that count.
            if ($Band_cur and !defined $cs and !in_band($child, $pozice)) {
                ++$Band_dropped;
                next;
            }
            if (!defined $cs) {
                node_set($child, $pozice, $sollen);
                $need = 1;    # nobody has expanded it: it must be queued
                if (exists $SolReal{$child}) {
                    $Bestbet  = $child;
                    $Bestlen  = $sollen;
                    $Improved = 1;
                    next;
                }
            }
            elsif ($cs > $sollen) {
                $need = bublej_fifo($child, $pozice, $sollen);
            }
            else {
                next;
            }
            queue_add($child) if $need;
            if ($Improved) {
                save_improvement();
                return 'IMPROVED' if want_restart();

                # The band follows the RECORD, not the restart (see the baseline).
                # The heap is KEPT, so $Band_dropped is NOT reset here: what the old band
                # dropped is still missing from this frontier (see restart()).
                band_build(parent_postup($Bestbet)) if $Band_cur;

                # Keep this open list and carry on with the tighter $Bestlen, which now
                # prunes it via the `>= $Bestlen` tests above.
                $Improved = 0;
            }
        } ## end foreach my ($child, $step)(...)
    } ## end while ($N_Open)
    return 'SOLVED';
} ## end sub hledej_fifo

# solve($gameid, $gm, $first_path): as Optimal's -- $gameid an integer the caller names
# the level by (the stores' directory is G<gameid>), $gm the Parser's analysis in its
# blob() form, $first_path a solution to start from (undef or '' = none).
sub solve ($gameid, $gm, $first_path = undef) {
    my ($pozice, $reason, $path, $plen, $steps, $doba, $ending, $status);

    # Resolve $MODE ONCE, before initvars can consult $H_on for the estimate tables. An
    # unknown mode dies here, loudly, rather than silently running as DIAL.
    confess("solve: unknown \$MODE '$MODE' (want DIAL, ASTAR or FIFO)")
        unless $MODE eq 'DIAL'
        or $MODE eq 'ASTAR'
        or $MODE eq 'FIFO';
    $Fifo = ($MODE eq 'FIFO')  ? 1 : 0;
    $H_on = ($MODE eq 'ASTAR') ? 1 : 0;
    initvars($gameid, $gm);
    $pozice = pack($pu, $Game{'player'}, @Baggage);
    node_set($pozice, '', 0);    # Seen=0, Parent='' (root); the queue is empty after initvars
    $N_Open = 0;
    $O_Open = 0
        ; # last-print open count; must be set here too, not only in restart(), or an unseeded solve that runs past info()'s 6s threshold reads it undef (FATAL under 'uninitialized')
    $MaxOpen  = 0;
    $CurMin   = 0;
    $Level_at = -1;                    # no level recorded yet (0 is a real level)
    $Pushed   = 0;                     # the enqueue increments it; zeroed before the root goes in
    $Fifo ? queue_add($pozice) : bucket_add($pozice, 0);
    $bc         = 0;
    $counter    = 0;
    $Pushed     = 0;                   # same reason as $O_Open above: info() divides by them
    $Expanded   = 0;
    $reason     = 'UNSOLVABLE';
    $timer      = [&gettimeofday()];
    $Gameid     = $gameid;
    $Cas        = time();
    @Track      = ();                  # per-solve: a second solve() must not inherit the first's trajectory
    $LastStatus = '';

    if (defined $first_path && length $first_path) {
        my @postup = cesta_na_pozice($first_path);
        $Bestbet = $postup[-1];
        $Bestlen = length($first_path);
        backlinen("START: $Bestlen") if $QUIET < 2;

        # The band exists only around a threaded record, and only in FIFO.
        $Band_cur = ($Fifo and $BAND and $BAND < $Nbox) ? $BAND : 0;
        restart(@postup);
    }

    # Seeding the search is not a restart. Reset AFTER restart(), which increments it
    # under FIFO.
    $nStart = 0;

    # info() compares against these to decide which of its lines to leave standing; set
    # AFTER the seed, so the very first line is not treated as a fresh record.
    ($O_Bestbet, $O_CurMin) = ($Bestlen, $CurMin);

    # DIAL and ASTAR: ONE call. hledej() reports every improvement itself and never
    # unwinds -- there are no restarts to unwind for.
    # FIFO: the restart loop, exactly as in the baseline. hledej_fifo() returns 'IMPROVED'
    # only when want_restart() approved compacting the frontier, and it has already
    # reported the betterment.
    if (!$Fifo) {
        $status = hledej();
    }
    else {
        while (1) {
            $Improved = 0;
            $status   = hledej_fifo();
            last if $status eq 'TIMEOUT' or $status eq 'MEMCAP' or $status eq 'IGNORE';
            if ($status eq 'SOLVED') {

                # A dry heap under a band that dropped children is NOT a proof: drop the
                # filter and search the same record's surroundings unrestricted (baseline
                # 3.2; the 3.1 ladder 3, 4, ... $Nbox is gone). An improvement puts the
                # band back at $BAND around the new record (below).
                last unless $Band_cur and $Band_dropped;
                $Band_total += $Band_dropped;
                backlinen(sprintf 'BAND %d exhausted: %d children dropped -> unrestricted', $Band_cur, $Band_dropped)
                    if $QUIET < 2;
                $Band_cur = 0;
                restart(parent_postup($Bestbet));
                next;
            }
            $Band_total += $Band_dropped;
            $Band_cur = ($BAND and $BAND < $Nbox) ? $BAND : 0;
            restart(parent_postup($Bestbet));
        } ## end while (1)
    } ## end else [ if (!$Fifo) ]
    $path  = undef;
    $doba  = tv_interval($timer);
    $plen  = 0;
    $steps = 0;
    if ($Bestbet) {

        # Populate the path whenever we have a $Bestbet at all, regardless of
        # how we got here -- a TIMEOUT'd run can still be carrying a real,
        # often better-than-the-seed solution; the caller (and a future
        # solve() call seeded from it) shouldn't lose that just because it
        # wasn't proven optimal this time.
        $path  = get_path(parent_postup($Bestbet));
        $plen  = length($path);
        $steps = $path =~ tr/UDRL//;
    }
    if ($status eq 'TIMEOUT' or $status eq 'MEMCAP' or $status eq 'IGNORE') {

        # The search was cut short (the clock, the $MAX_GB net, or another mode's proof in
        # a race) -- even a seeded/already-improved $Bestbet has NOT been proven optimal,
        # so this must NOT be reported SOLVED. All leave as TIMEOUT; the memory stop says
        # so loudly instead, and $LastStatus keeps the name.
        say {*STDERR}
            colored(
                sprintf('OUT OF MEMORY (used %.2f GiB > MAX_GB %.2f)', Games::Sokoban::Solver::Memory::used_gb(), $MAX_GB // 0),
                'bright_red')
            if $status eq 'MEMCAP';
        $reason = 'TIMEOUT';
    }
    elsif ($Bestbet) {

        # The search returned 'SOLVED': in DIAL/ASTAR the cheapest waiting position
        # reached $Bestlen (or the queue drained), in FIFO the queue genuinely ran dry.
        # Either way $Bestbet is provably the best reachable from this start.
        $reason = 'SOLVED';
    }

    # else: exhausted with no $Bestbet at all -- $reason stays 'UNSOLVABLE'.
    $ending = sprintf '%8d %3d %4d %-10s %6d %6d %12.4f %8.0f %8.0f',
        $gameid, $Game{'nbox'}, $Game{'ncell'}, $reason, $plen, $steps, $doba, $bc / $doba, $counter / $doba;
    barva($reason, $ending);
    bad_close($reason eq 'SOLVED' ? 1 : 0);

    # Why the run ended, by name: a MEMCAP or IGNORE stop returns as TIMEOUT (see above)
    # but must not be laundered -- the console line is gone by morning.
    $LastStatus = ($status eq 'MEMCAP' or $status eq 'IGNORE') ? $status : $reason;
    backlinen(
        sprintf 'BAND %d: %d children dropped, memo %d, track %d',
        $BAND,
        $Band_total + $Band_dropped,
        scalar keys %BandMemo,
        scalar @BandCfg
        )
        if $Fifo
        and $BAND
        and $QUIET < 2;
    $reason = 'IGNORE' if $status eq 'IGNORE';
    return ($reason, $path, $doba, $bc, $counter);
} ## end sub solve
1;
__END__

=head1 NAME

Games::Sokoban::Solver::Optimal::Berk - the optimal solver with its whole search on disk through BerkeleyDB

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Berkeley ();
    use Games::Sokoban::Solver::Optimal::Berk ();

    $Games::Sokoban::Solver::Berkeley::ROOT      = '/var/tmp/soko-solver';
    $Games::Sokoban::Solver::Optimal::Berk::CACHE = 512 * 1024 * 1024;    # the memory pool, bytes, at most 3 GB
    $Games::Sokoban::Solver::Optimal::Berk::LIMIT = 3600;
    my ($reason, $path, $seconds, $candidates, $pops)
        = Games::Sokoban::Solver::Optimal::Berk::solve($label, $game_blob, $seed);

=head1 DESCRIPTION

The same C<solve> contract and the same search as L<Games::Sokoban::Solver::Optimal>,
with every search structure -- the deadlock cache, the move cache, the
positions with their cost and parent, the cost-ordered open list -- in one
BerkeleyDB environment of the level's own under the root directory of
L<Games::Sokoban::Solver::Berkeley>, so that a solve can run far past what
memory alone allows. The memory pool C<$CACHE> is the RAM ceiling. After a
TIMEOUT the deadlock and move caches stay in the level's directory and the
next run on the same level starts from them; a proof removes the directory.

This is a STORAGE twin: it differs from Optimal in where the structures live,
never in which positions are searched or in what C<solve> returns (the
distribution's gate holds the two to the same proved path). It is
Games::Sokoban::SolverBerk 3.2 of the Sokoban project with the storage cut
Optimal had. The BerkeleyDB module must be installed; L<Games::Sokoban::Solver>
loads this module only when asked for it.

=head1 INTERFACE

C<solve($label, $game_blob, $seed)> and the run control of
L<Games::Sokoban::Solver::Optimal/INTERFACE> (C<$LIMIT $MODE $BAND $MAX_GB
$QUIET $RACE_FLAG $RACE_GID $ON_IMPROVED $LastStatus @Track>), plus
C<$CACHE>, the pool in bytes. One process at a time per level directory: a
second is refused by a lock file.

=head1 CAVEATS

The module keeps the pool size in 32 bits, so C<$CACHE> is at most 3 GB
(L<Games::Sokoban::Solver::Berkeley> refuses more). The label is the name of
the directory, so two levels with one label would share a store: the
distribution's labels are a hash of the level.

=head1 SEE ALSO

L<Games::Sokoban::Solver::Optimal>, L<Games::Sokoban::Solver::Berkeley>,
L<Games::Sokoban::Solver>.

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
