#!/usr/bin/env perl
# The optimal solver of the distribution against its original in the Sokoban
# project, both in ONE process under a fixed hash seed: the copy cut the
# original's storage away (the database writes, the BerkeleyDB seam, the SQL
# log, the statistics) and must SEARCH exactly as before.
#
# For every (game, mode) pair both are run from the same seed (the stored
# firstbet path) with the same limit:
#   * where BOTH prove (SOLVED): the same path, the same number of candidates
#     and pops;
#   * on every pair: the lengths of the improvements, in order, equal as far as
#     the shorter run got (the clock may cut one earlier than the other);
#   * no proved length of either may exceed the optimum the project's bestbet
#     holds where that is proved (the property of ai/band_vs_proof.pl);
#   * the copy's $ON_IMPROVED is called once per entry of its @Track;
#   * every proved path replays by Replay::check; a dying solve is DIE;
#   * the copy loads no BerkeleyDB module and the original creates no files
#     (its $PERSIST is forced off, its writes go to a scratch SQL log).
# TIMEOUT counters are never compared: the copy, which writes nothing, is
# faster, so the clock cuts it elsewhere.
#
#   PERL_HASH_SEED=0 PERL_PERTURB_KEYS=0
#   perl xt/eq_optimal.pl [--limit S] [--gameids L] [--modes M,M] [--spoil]
#
# Default: games 7985 2066 14637 37928 41519 27701 3413 7265 1 (the set of the
# project's mode gate), the three modes, 60 s -- about an hour and a half with
# the overrun, the author's run; in a session --gameids 7985,2066,14637
# --limit 30. --spoil: the copy with $BAND = 0 against the original's band 2 in
# FIFO on game 7265 -- the gate must report a difference.
# PERL5LIB must be empty.
use v5.42;
no warnings 'once';    # the original's package variables are set once each
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long ();
use File::Temp   ();
use Games::Sokoban::Solver::Optimal ();
use Games::Sokoban::Solver::Replay  ();
STDOUT->autoflush(1);

my %opt = ('limit' => 60, 'gameids' => '', 'modes' => 'DIAL,ASTAR,FIFO', 'spoil' => 0);
Getopt::Long::GetOptions(\%opt, 'limit=f', 'gameids=s', 'modes=s', 'spoil!')
    or die "usage: eq_optimal.pl [--limit S] [--gameids L] [--modes M,M] [--spoil]\n";
Gate::need_fixed_hash_seed();

# The original, from the Sokoban tree, with every write turned into a line of a
# scratch SQL log and its caches in RAM. By its FILE: the original's package is
# Games::Sokoban::Solver, the name of this distribution's facade, so `require
# Games::Sokoban::Solver` would find the facade in this tree's lib first.
my @berk = grep { m{Berkeley|DBI|Zapis|SokDB} } keys %INC;    # what the COPY loaded, before the original comes
my $baseline = Gate::baseline_lib() . '/Games/Sokoban/Solver.pm';
require $baseline;
die "the original was not loaded from the Sokoban tree\n" unless $INC{$baseline} and defined &Games::Sokoban::Solver::hledej;
my $log = File::Temp->new('SUFFIX' => '.sql');
$Games::Sokoban::Solver::PERSIST = 0;
$Games::Sokoban::Solver::LOG     = "$log";

my $ours   = 'Games::Sokoban::Solver::Optimal';
my $theirs = 'Games::Sokoban::Solver';
for my $pkg ($ours, $theirs) {
    no strict 'refs';
    ${"${pkg}::QUIET"}  = 2;
    ${"${pkg}::MAX_GB"} = 0;
    ${"${pkg}::LIMIT"}  = $opt{'limit'};
}

my $db  = Gate::db('Sokoban');
my @ids = length $opt{'gameids'} ? grep { /\A\d+\z/ } split /[,\s]+/, $opt{'gameids'} : (7985, 2066, 14637, 37928, 41519, 27701, 3413, 7265, 1);
my @modes = split /,/, $opt{'modes'};
my %n = ('ok' => 0, 'mismatch' => 0, 'skip' => 0, 'prefix_differ' => 0, 'over_optimum' => 0, 'unplayable' => 0, 'died' => 0);
my $failed = 0;

sub game_of ($gameid) {
    my ($blob, $code, $seed, $optimum) = $db->selectrow_array(<<'SQL', undef, $gameid);
        SELECT g.game, g.code, f.path, CASE WHEN b.status = 'SOLVED' THEN b.sollen END
          FROM game_blob g JOIN firstbet f USING (gameid) LEFT JOIN bestbet b USING (gameid)
         WHERE g.gameid = ? AND g.source = 'PARSER'
SQL
    die "game $gameid: no stored analysis or first solution\n" unless defined $blob and defined $seed;
    return ($blob, $code, $seed, $optimum);
}

my %died;
sub qsolve ($pkg, $mode, $gameid, $blob, $seed) {
    no strict 'refs';
    ${"${pkg}::MODE"} = $mode;
    @{"${pkg}::Track"} = ();
    my @r = do {
        local *STDERR;
        open STDERR, '>', \my $junk;
        eval { &{"${pkg}::solve"}($gameid, $blob, $seed) };
    };
    unless (@r) { $died{"$gameid $mode $pkg"} = (split /\n/, "$@")[0] // 'died without a word'; return ('DIE', undef, 0, 0, 0, []) }
    return (@r, [map { $_->{'sollen'} } @{"${pkg}::Track"}]);
}

# One pair compared; returns a verdict and prints the differences.
sub compare ($gameid, $mode, $code, $optimum, $a, $b, $what_b = 'orig') {
    my ($ar, $ap, undef, $abc, $acnt, $atrack) = @$a;
    my ($br, $bp, undef, $bbc, $bcnt, $btrack) = @$b;
    my $verdict = 'ok';
    for my $side (['ours', $ar, $ap], [$what_b, $br, $bp]) {
        my ($who, $reason, $path) = @$side;
        next unless $reason eq 'SOLVED';
        if (defined(my $err = Games::Sokoban::Solver::Replay::check($code, $path // ''))) {
            ++$n{'unplayable'}; printf "UNPLAYABLE g=%-6d %-5s %s: %s\n", $gameid, $mode, $who, $err;
        }
        if (defined $optimum and length($path // '') > $optimum) {
            ++$n{'over_optimum'}; printf "OVER OPTIMUM g=%-6d %-5s %s: proved %d, stored optimum %d\n", $gameid, $mode, $who, length $path, $optimum;
        }
    }
    my $common = @$atrack < @$btrack ? scalar @$atrack : scalar @$btrack;
    if (join(',', @$atrack[0 .. $common - 1]) ne join(',', @$btrack[0 .. $common - 1])) {
        ++$n{'prefix_differ'};
        printf "IMPROVEMENTS g=%-6d %-5s ours=[%s] %s=[%s]\n", $gameid, $mode, join(',', @$atrack), $what_b, join(',', @$btrack);
        $verdict = 'mismatch';
    }
    if ($ar eq 'SOLVED' and $br eq 'SOLVED') {
        my ($ka, $kb) = ("$ap|$abc|$acnt", "$bp|$bbc|$bcnt");
        if ($ka ne $kb) {
            printf "MISMATCH g=%-6d %-5s ours=[len %d, %d candidates, %d pops] %s=[len %d, %d, %d]%s\n", $gameid, $mode,
                length $ap, $abc, $acnt, $what_b, length $bp, $bbc, $bcnt, ($ap eq $bp ? '' : ' -- the paths differ');
            $verdict = 'mismatch';
        }
    }
    elsif ($ar ne $br and !($ar =~ /\A(?:TIMEOUT|SOLVED)\z/ and $br =~ /\A(?:TIMEOUT|SOLVED)\z/)) {
        printf "REASON   g=%-6d %-5s ours=%s %s=%s\n", $gameid, $mode, $ar, $what_b, $br;
        $verdict = 'mismatch';
    }
    elsif ($ar ne 'SOLVED' or $br ne 'SOLVED') { $verdict = 'skip' if $verdict eq 'ok' }
    return $verdict;
}

if ($opt{'spoil'}) {
    my %before = %n;    # what the spoiled pair reports is not a finding of the run
    my ($blob, $code, $seed, $optimum) = game_of(7265);
    $Games::Sokoban::Solver::Optimal::BAND = 0;
    my @a = qsolve($ours, 'FIFO', 7265, $blob, $seed);
    $Games::Sokoban::Solver::Optimal::BAND = 2;
    my @b = qsolve($theirs, 'FIFO', 7265, $blob, $seed);
    my $verdict = compare(7265, 'FIFO', $code, $optimum, \@a, \@b, 'band2');
    if ($verdict eq 'mismatch') { say 'spoil: the copy without the band against the original with it on game 7265 is reported -- the gate fires' }
    else                        { say "spoil: NOT CAUGHT ($verdict)"; $failed = 1 }
    %n = %before;
}

# $ON_IMPROVED is called once per improvement: counted in DIAL on game 7265, whose
# stored first solution (79 moves) is longer than its optimum (49), so a run of the
# given limit betters it at least once -- a run with no improvement tested nothing.
{
    my ($blob, $code, $seed) = game_of(7265);
    my $calls = 0;
    $Games::Sokoban::Solver::Optimal::ON_IMPROVED = sub ($path, $cas) { ++$calls; die "ON_IMPROVED: no path\n" unless length $path };
    my @a = qsolve($ours, 'DIAL', 7265, $blob, $seed);
    $Games::Sokoban::Solver::Optimal::ON_IMPROVED = undef;
    my $track = scalar @{ $a[5] };
    if    ($calls == 0)      { say "ON_IMPROVED: never called on game 7265 ($a[0]) -- the check tested nothing"; $failed = 1 }
    elsif ($calls == $track) { say "ON_IMPROVED: called $calls time(s) on game 7265, one per improvement" }
    else                     { say "ON_IMPROVED: called $calls time(s), \@Track has $track"; $failed = 1 }
}

for my $gameid (@ids) {
    my ($blob, $code, $seed, $optimum) = game_of($gameid);
    for my $mode (@modes) {
        my @a = qsolve($ours,   $mode, $gameid, $blob, $seed);
        my @b = qsolve($theirs, $mode, $gameid, $blob, $seed);
        my $verdict = compare($gameid, $mode, $code, $optimum, \@a, \@b);
        ++$n{$verdict};
        printf {*STDERR} "\r%d %-5s %-8s %-8s %s   ", $gameid, $mode, $a[0], $b[0], $verdict;
    }
}
print {*STDERR} "\n";
$n{'died'} = scalar keys %died;
say "DIED $_: $died{$_}" for sort keys %died;
if (@berk) { say "the copy loaded a storage module: @berk"; $failed = 1 }
$failed = 1 if $n{'mismatch'} or $n{'prefix_differ'} or $n{'over_optimum'} or $n{'unplayable'} or $n{'died'};
exit Gate::verdict($failed, %n);
