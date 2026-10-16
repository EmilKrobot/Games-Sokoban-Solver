#!/usr/bin/env perl
# The optimal solver's BerkeleyDB twin against the optimal solver itself (the
# shape of the project's ai/smoke_solverberk.pl): a STORAGE twin must return the
# SAME proved path in every mode where both prove. Three small games the project
# proved, from the stored first solution as the seed, in DIAL, ASTAR and FIFO;
# then game 1 at a few seconds -- too large to prove -- must return a path no
# longer than its seed and leave its two caches in the level's directory, with
# none of the run state. The stores live in a scratch directory of their own.
#
#   PERL_HASH_SEED=0 PERL_PERTURB_KEYS=0
#   perl xt/smoke_optimal_berk.pl [--limit S] [--gameids L] [--spoil]
#
# Default games 7985 2066 14637, limit 60 s. --spoil: the twin in FIFO with
# the band off against the solver with it on, on game 7265: the proved path
# may be the same but candidates or pops must differ.
# PERL5LIB must be empty; one process at a time.
use v5.42;
no warnings 'once';    # the twin's package variables are set once each
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long                    ();
use File::Temp                      ();
use Games::Sokoban::Solver::Replay  ();
use Games::Sokoban::Solver::Optimal ();
STDOUT->autoflush(1);
my %opt = ('limit' => 60, 'gameids' => '', 'spoil' => 0);
Getopt::Long::GetOptions(\%opt, 'limit=f', 'gameids=s', 'spoil!')
    or die "usage: smoke_optimal_berk.pl [--limit S] [--gameids L] [--spoil]\n";
Gate::need_fixed_hash_seed();
die "the BerkeleyDB module is not installed\n" unless eval {require BerkeleyDB; 1};
require Games::Sokoban::Solver::Berkeley;
require Games::Sokoban::Solver::Optimal::Berk;
my $root = File::Temp::tempdir('smoke_optimal_berk-XXXXXX', 'TMPDIR' => 1, 'CLEANUP' => 1);
$Games::Sokoban::Solver::Berkeley::ROOT = $root;
my $ram  = 'Games::Sokoban::Solver::Optimal';
my $disk = 'Games::Sokoban::Solver::Optimal::Berk';

for my $pkg ($ram, $disk) {
    no strict 'refs';
    ${"${pkg}::QUIET"}  = 2;
    ${"${pkg}::MAX_GB"} = 0;
    ${"${pkg}::LIMIT"}  = $opt{'limit'};
}
$Games::Sokoban::Solver::Optimal::Berk::CACHE = 64 * 1024 * 1024;
my $db  = Gate::db('Sokoban');
my @ids = length $opt{'gameids'} ? grep {/\A\d+\z/} split /[,\s]+/, $opt{'gameids'} : (7985, 2066, 14637);
my ($n, $failed) = (0, 0);
sub check ($cond, $what) {++$n; say(($cond ? 'ok   ' : 'NOT OK ') . "$n - $what"); $failed = 1 unless $cond; return $cond}

sub game_of ($gameid) {
    my ($blob, $code, $seed) = $db->selectrow_array(
"SELECT g.game, g.code, f.path FROM game_blob g JOIN firstbet f USING (gameid) WHERE g.gameid = ? AND g.source = 'PARSER'",
        undef, $gameid
    );
    die "game $gameid: no stored analysis or first solution\n" unless defined $blob and defined $seed;
    return ($blob, $code, $seed);
}

sub qsolve ($pkg, $mode, @args) {
    no strict 'refs';
    ${"${pkg}::MODE"} = $mode;
    my @r = do {
        local *STDERR;
        open STDERR, '>', \my $junk;
        eval {&{"${pkg}::solve"}(@args)};
    };
    return @r ? @r : ('DIE: ' . ((split /\n/, "$@")[0] // '?'), undef, 0, 0, 0);
}
if ($opt{'spoil'}) {
    my ($blob, $code, $seed) = game_of(7265);
    my @a = qsolve($ram, 'FIFO', 7265, $blob, $seed);
    $Games::Sokoban::Solver::Optimal::Berk::BAND = 0;
    my @b = qsolve($disk, 'FIFO', 7265, $blob, $seed);
    $Games::Sokoban::Solver::Optimal::Berk::BAND = 2;
    my $differ = ($a[1] // '') ne ($b[1] // '') || $a[3] != $b[3] || $a[4] != $b[4];
    if ($differ) {
        say
"spoil: the twin without the band against the solver with it on game 7265 is reported ($a[3]/$a[4] against $b[3]/$b[4] candidates/pops) -- the gate fires";
    }
    else {say 'spoil: NOT CAUGHT'; $failed = 1}
}
for my $mode ('DIAL', 'ASTAR', 'FIFO') {
    for my $gameid (@ids) {
        my ($blob, $code, $seed) = game_of($gameid);
        my ($ra, $pa, undef, $bca, $cnta) = qsolve($ram,  $mode, $gameid, $blob, $seed);
        my ($rb, $pb, undef, $bcb, $cntb) = qsolve($disk, $mode, $gameid, $blob, $seed);
        check($ra eq 'SOLVED' && $rb eq 'SOLVED', "$mode game $gameid: proved both ways ($ra / $rb)");
        check(defined $pa && defined $pb && $pa eq $pb,
            "$mode game $gameid: the twin's path is the solver's" . (defined $pa ? ' (len ' . length($pa) . ')' : ''));

        # The candidates are the search's own and must agree; the pops are counted
        # one apart by construction (the twin counts the pop that finds the queue at
        # the record, the solver returns before it), so they are shown, not held.
        check($bca == $bcb, "$mode game $gameid: the same candidates ($bca against $bcb; pops $cnta / $cntb)");
        check(!defined Games::Sokoban::Solver::Replay::check($code, $pb // ''), "$mode game $gameid: the twin's path plays");
        check(!-d "$root/Optimal/G$gameid", "$mode game $gameid: the proof removed the level's directory");
    } ## end for my $gameid (@ids)
} ## end for my $mode ('DIAL', 'ASTAR'...)

# game 1: too large to prove in seconds -- no worse than the seed, the caches kept
{
    my ($blob, $code, $seed) = game_of(1);
    local $Games::Sokoban::Solver::Optimal::Berk::LIMIT = 5;
    my ($rb, $pb) = qsolve($disk, 'DIAL', 1, $blob, $seed);
    check($rb eq 'TIMEOUT', "game 1 at 5 s: TIMEOUT ($rb), named $Games::Sokoban::Solver::Optimal::Berk::LastStatus");
    check(defined $pb && length($pb) <= length($seed),                      'game 1: a path no longer than the seed');
    check(!defined Games::Sokoban::Solver::Replay::check($code, $pb // ''), 'game 1: the path plays');
    check(
        -f "$root/Optimal/G1/bad.brk" && -f "$root/Optimal/G1/tahy.brk",
        'game 1: the deadlock and move caches stay for the next run'
    );
    check(!-f "$root/Optimal/G1/pozice.brk" && !-f "$root/Optimal/G1/bucket.brk" && !-f "$root/Optimal/G1/expanded.brk",
        'game 1: the run state is gone');
}
say $failed ? "\nFAILED" : "\nALL PASS";
exit($failed ? 1 : 0);
