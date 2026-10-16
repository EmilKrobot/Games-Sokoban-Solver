#!/usr/bin/env perl
# The Firstbet twin on BerkeleyDB against Firstbet itself, on the project's
# stored analyses under a fixed hash seed (the shape of the project's
# ai/eq_berk_new.pl, THE gate of the storage twin): the twin goes to disk but
# must SEARCH exactly as the baseline, so on every (game, mode) both solve, the
# path written again from its pushes, the verdict and the number of positions
# must agree; a structural verdict (NOCP, GIVEUP, UNSOLVABLE) must be the same
# on both sides; TIMEOUT / MEMCAP are skipped (the twin does more work per
# position, so the clock cuts it elsewhere). Every solved path is replayed.
# Then a WARM run: the twin on one pair with a limit of a fraction of a second
# (its caches stay in the directory) and again with the full limit must solve
# with the baseline's path -- the stores inherited from a cut run are sound.
#
#   PERL_HASH_SEED=0 PERL_PERTURB_KEYS=0
#   perl xt/eq_firstbet_berk.pl [--limit S] [--gameids L] [--modes M,M] [--spoil]
#
# Default games 1 76 582 2614, limit 15 s, all ten modes; the stores live in a
# scratch directory of their own that is removed at the end. --spoil: our
# PUSH_SCORE against the baseline's MOVE_SCORE on game 1 must MISMATCH.
# Run it in ONE process at a time (two on one store directory is a crash, which
# the lock file now refuses). PERL5LIB must be empty.
use v5.42;
no warnings 'once';    # the twin's package variables are set once each
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long ();
use File::Temp   ();
use Time::HiRes  ();
use Games::Sokoban::Solver::Path   ();
use Games::Sokoban::Solver::Replay ();
use Games::Sokoban::Solver::Firstbet ();
STDOUT->autoflush(1);

my %opt = ('limit' => 15, 'gameids' => '', 'modes' => '', 'spoil' => 0);
Getopt::Long::GetOptions(\%opt, 'limit=f', 'gameids=s', 'modes=s', 'spoil!')
    or die "usage: eq_firstbet_berk.pl [--limit S] [--gameids L] [--modes M,M] [--spoil]\n";
Gate::need_fixed_hash_seed();
die "the BerkeleyDB module is not installed\n" unless eval { require BerkeleyDB; 1 };
require Games::Sokoban::Solver::Berkeley;
require Games::Sokoban::Solver::Firstbet::Berk;

my $root = File::Temp::tempdir('eq_firstbet_berk-XXXXXX', 'TMPDIR' => 1, 'CLEANUP' => 1);
$Games::Sokoban::Solver::Berkeley::ROOT = $root;
my $base = 'Games::Sokoban::Solver::Firstbet';
my $twin = 'Games::Sokoban::Solver::Firstbet::Berk';
for my $pkg ($base, $twin) {
    no strict 'refs';
    ${"${pkg}::QUIET"}  = 2;
    ${"${pkg}::MAX_GB"} = 0;
}
$Games::Sokoban::Solver::Firstbet::Berk::CACHE          = 16 * 1024 * 1024;    # a gate walks a few thousand positions
$Games::Sokoban::Solver::Firstbet::Berk::STORE_PER_MODE = 1;

my @modes = length $opt{'modes'} ? split /,/, $opt{'modes'} : qw(PUSH_SCORE MOVE_SCORE PUSH_ASSIGN MOVE_SUM ROUTE FLOW ORDER BACKWARD CONVEYOR FEATURE);
my @ids   = length $opt{'gameids'} ? grep { /\A\d+\z/ } split /[,\s]+/, $opt{'gameids'} : (1, 76, 582, 2614);
my $db    = Gate::db('Sokoban');
my %n     = ('ok' => 0, 'mismatch' => 0, 'skip' => 0, 'unplayable' => 0, 'died' => 0, 'slow' => 0);
my $failed = 0;
my %died;

sub blob_of ($gameid) {
    my ($blob, $code) = $db->selectrow_array("SELECT game, code FROM game_blob WHERE gameid = ? AND source = 'PARSER'", undef, $gameid);
    die "game $gameid: no stored analysis\n" unless defined $blob;
    return ($blob, $code);
}

sub qsolve ($pkg, @args) {
    my $t0 = Time::HiRes::time();
    my @r  = do {
        local *STDERR;
        open STDERR, '>', \my $junk;
        no strict 'refs';
        eval { &{"${pkg}::solve"}(@args) };
    };
    unless (@r) { $died{"$args[0] $args[3] $pkg"} = (split /\n/, "$@")[0] // 'died without a word'; @r = ('DIE', undef, 0, 0) }
    return (@r, Time::HiRes::time() - $t0);
}

sub rebuilt ($code, $path) {
    return eval { Games::Sokoban::Solver::Path::rebuilt(Games::Sokoban::Solver::Path::level($code), 'path' => $path // '') };
}

# One pair compared; the twin's wall time is watched too: a run far over the
# limit means a watchdog was stepped over.
sub compare ($gameid, $mode, $code, $a, $b) {
    my ($ar, $ap, undef, $an)      = @$a;
    my ($br, $bp, undef, $bn, $bw) = @$b;
    if ($bw > 3 * $opt{'limit'} + 10) { ++$n{'slow'}; printf "SLOW     g=%-6d %-11s the twin took %.0f s at a limit of %s\n", $gameid, $mode, $bw, $opt{'limit'} }
    for my $side (['base', $ar, $ap], ['twin', $br, $bp]) {
        my ($who, $reason, $path) = @$side;
        next unless $reason eq 'SOLVED';
        my $err = Games::Sokoban::Solver::Replay::check($code, $path // '');
        $err //= 'rebuilt refuses it' unless defined rebuilt($code, $path);
        next unless defined $err;
        ++$n{'unplayable'};
        printf "UNPLAYABLE g=%-6d %-11s %s: %s\n", $gameid, $mode, $who, $err;
    }
    if ($ar ne 'SOLVED' or $br ne 'SOLVED') {
        return 'skip' if $ar eq $br and $ar ne 'DIE';
        return 'skip' if $ar =~ /\A(?:TIMEOUT|MEMCAP)\z/ and $br =~ /\A(?:TIMEOUT|MEMCAP)\z/;
        printf "REASON   g=%-6d %-11s base=%-9s twin=%s\n", $gameid, $mode, $ar, $br;
        return 'mismatch';
    }
    my ($ka, $kb) = (join('|', rebuilt($code, $ap) // '-', $an), join('|', rebuilt($code, $bp) // '-', $bn));
    return 'ok' if $ka eq $kb;
    printf "MISMATCH g=%-6d %-11s base=[len %d, %d positions] twin=[len %d, %d positions]%s\n", $gameid, $mode,
        length($ap), $an, length($bp), $bn, (($ap // '') eq ($bp // '') ? '' : ' -- the paths differ');
    return 'mismatch';
}

if ($opt{'spoil'}) {
    my ($blob, $code) = blob_of(1);
    my @a = qsolve($base, 1, $blob, $opt{'limit'}, 'MOVE_SCORE');
    my @b = qsolve($twin, 1, $blob, $opt{'limit'}, 'PUSH_SCORE');
    Games::Sokoban::Solver::Berkeley::fb_sweep([1], [1]);
    my %before = %n;
    my $verdict = compare(1, 'PUSH_SCORE/MOVE_SCORE', $code, \@a, \@b);
    %n = %before;
    if ($verdict eq 'mismatch') { say "spoil: the twin's PUSH_SCORE against the baseline's MOVE_SCORE on game 1 is reported -- the gate fires" }
    else                        { say "spoil: NOT CAUGHT ($verdict)"; $failed = 1 }
}

my @warm_candidates;    # (game, mode, the twin's seconds, its path): solved pairs that took over a second
for my $gameid (@ids) {
    my ($blob, $code) = blob_of($gameid);
    for my $mode (@modes) {
        my @a = qsolve($base, $gameid, $blob, $opt{'limit'}, $mode);
        Games::Sokoban::Solver::Berkeley::fb_sweep([$gameid], [$gameid]);    # the twin starts COLD: a kept cache would change its search
        my @b = qsolve($twin, $gameid, $blob, $opt{'limit'}, $mode);
        my $verdict = compare($gameid, $mode, $code, \@a, \@b);
        ++$n{$verdict};
        push @warm_candidates, [$gameid, $mode, $b[4], $b[1]] if $verdict eq 'ok' and $b[4] > 1 and $mode ne 'BACKWARD';
        printf {*STDERR} "\r%d %-11s %-9s %-9s %s   ", $gameid, $mode, $a[0], $b[0], $verdict;
    }
    Games::Sokoban::Solver::Berkeley::fb_sweep([$gameid], [$gameid]);
}
print {*STDERR} "\n";

# THE WARM RUN: a pair the twin solved in over a second, cut at a tenth of that
# (so the first run really is cut), then the full limit on the stores it left --
# the twin's one property the baseline cannot have. The warm run must SOLVE and
# its path must play; it need not be the cold run's path: a deadlock cache and
# a move cache inherited from the cut run change the search (which is why the
# pairs above are run cold, with a sweep between them). BACKWARD is left out:
# its store is scratch of one search and inherits nothing.
if (@warm_candidates) {
    my ($gameid, $mode, $secs, $path) = @{ $warm_candidates[0] };
    my ($blob, $code) = blob_of($gameid);
    Games::Sokoban::Solver::Berkeley::fb_sweep([$gameid], [$gameid]);
    my @cut  = qsolve($twin, $gameid, $blob, $secs / 10, $mode);
    my $kept = -f "$root/Firstbet/G${gameid}_$mode/tahy.brk" ? 1 : 0;
    my @warm = qsolve($twin, $gameid, $blob, $opt{'limit'}, $mode);
    my $plays = ($warm[0] eq 'SOLVED' and !defined Games::Sokoban::Solver::Replay::check($code, $warm[1] // '') and defined rebuilt($code, $warm[1])) ? 1 : 0;
    printf "warm: game %d %s -- the cut run (limit %.2f s) ended %s in %.2f s, the caches %s, the warm run %s in %.2f s (cold: %.2f s), its path %s, %s the cold one\n",
        $gameid, $mode, $secs / 10, $cut[0], $cut[4], ($kept ? 'stayed' : 'were NOT kept'), $warm[0], $warm[4], $secs,
        ($plays ? 'plays' : 'does NOT play'), (($warm[1] // '') eq ($path // '') ? 'the same as' : 'another than');
    $failed = 1 unless $kept and $plays;
    say 'warm: the cut run was not cut (it solved) -- the inheritance was not exercised' if $cut[0] eq 'SOLVED';
    Games::Sokoban::Solver::Berkeley::fb_sweep([$gameid], [$gameid]);
}
else { say 'warm: NOT TESTED -- no pair the twin solved in over a second'; $failed = 1 }

$n{'died'} = scalar keys %died;
say "DIED $_: $died{$_}" for sort keys %died;
$failed = 1 if $n{'mismatch'} or $n{'unplayable'} or $n{'died'} or $n{'slow'};
exit Gate::verdict($failed, %n);
