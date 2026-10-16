# Optimal: the three modes prove the optimum of the brute-force oracle on the
# micro levels, with a long seed and with none; the improvements are reported;
# a limit of nothing returns TIMEOUT with the seed; the stop is named.
use v5.42;
use Test::More;
use lib 't/lib';
use BruteForce                      ();
use Games::Sokoban::Solver::Level   ();
use Games::Sokoban::Solver::Code    ();
use Games::Sokoban::Solver::Parser  ();
use Games::Sokoban::Solver::Replay  ();
use Games::Sokoban::Solver::Optimal ();
$Games::Sokoban::Solver::Optimal::QUIET = 2;
$Games::Sokoban::Solver::Optimal::LIMIT = 30;
open my $fh, '<', 't/data/micro.xsb' or die $!;
my $text = do {local $/; <$fh>};
close $fh;
my @levels = Games::Sokoban::Solver::Level::read($text);

# A deliberately long solution of a level: one with MORE PUSHES than the
# optimum (a detour in the walk alone would not do -- the solver reads its
# seed as the positions after each push and thinks in those, so a seed that
# only walks more threads the very same positions and is bettered by nothing).
sub long_seed ($code, $optimum) {
    my $seed = BruteForce::longer($code, $optimum, length($optimum) + 12);
    return undef unless defined $seed;
    die "the long seed does not play" if defined Games::Sokoban::Solver::Replay::check($code, $seed);
    return $seed;
}
for my $level (@levels) {
    my ($code0, $code1) = Games::Sokoban::Solver::Level::normalize($level->{'rows'});
    my %code = Games::Sokoban::Solver::Code::prepare($code1);
    next if !@{ $code{'baggage'} };    # solved by the opening: nothing to search
    my %game = Games::Sokoban::Solver::Parser::parse(\%code);
    my $blob = Games::Sokoban::Solver::Parser::blob(\%game);
    my $best = BruteForce::solve($code{'code'});
    ok(defined $best, "$level->{'title'}: the oracle solves the reduced level");
    my $seed = long_seed($code{'code'}, $best);

    for my $mode ('DIAL', 'ASTAR', 'FIFO') {
        $Games::Sokoban::Solver::Optimal::MODE = $mode;
        for my $start ([undef, 'no seed'], [$seed, 'a long seed']) {
            my ($given, $what) = @$start;
            next if $what eq 'a long seed' and !defined $given;
            my @calls;
            $Games::Sokoban::Solver::Optimal::ON_IMPROVED = sub ($path, $cas) {push @calls, $path};
            my ($reason, $path, $secs, $bc, $pops) = Games::Sokoban::Solver::Optimal::solve(7, $blob, $given);
            my $tag = "$level->{'title'}, $mode, $what";
            is($reason,      'SOLVED',     "$tag: proved");
            is(length $path, length $best, "$tag: the optimum of the oracle (" . length($best) . ' moves)');
            is(Games::Sokoban::Solver::Replay::check($code{'code'}, $path), undef, "$tag: the path plays");
            ok($bc > 0 && $pops > 0, "$tag: candidates and pops counted");
            is($Games::Sokoban::Solver::Optimal::LastStatus, 'SOLVED', "$tag: the stop is named SOLVED");

            if (defined $given) {
                ok(@calls >= 1, "$tag: the seed was bettered, ON_IMPROVED called " . scalar(@calls) . ' time(s)');
                is(scalar @calls, scalar @Games::Sokoban::Solver::Optimal::Track, "$tag: once per entry of \@Track");
                is($calls[-1],    $path,                                          "$tag: the last improvement is the answer");
            }
            else {
                is(scalar @calls, scalar @Games::Sokoban::Solver::Optimal::Track, "$tag: ON_IMPROVED and \@Track agree");
            }
        } ## end for my $start ([undef, ...])
    } ## end for my $mode ('DIAL', 'ASTAR'...)
    $Games::Sokoban::Solver::Optimal::ON_IMPROVED = undef;
} ## end for my $level (@levels)

# An unknown mode is refused; a limit already spent returns the seed as TIMEOUT.
{
    my ($level) = grep {$_->{'title'} eq 'Three boxes in a room'} @levels;
    my ($code0, $code1) = Games::Sokoban::Solver::Level::normalize($level->{'rows'});
    my %code = Games::Sokoban::Solver::Code::prepare($code1);
    my %game = Games::Sokoban::Solver::Parser::parse(\%code);
    my $blob = Games::Sokoban::Solver::Parser::blob(\%game);
    my $best = BruteForce::solve($code{'code'});
    my $seed = long_seed($code{'code'}, $best) // $best;
    $Games::Sokoban::Solver::Optimal::MODE = 'FAST';
    ok(!eval {Games::Sokoban::Solver::Optimal::solve(7, $blob, $seed); 1}, 'an unknown mode is refused');
    like($@, qr/unknown \$MODE 'FAST'/, '... by name');
    $Games::Sokoban::Solver::Optimal::MODE  = 'DIAL';
    $Games::Sokoban::Solver::Optimal::LIMIT = 0.000001;
    my ($reason, $path) = Games::Sokoban::Solver::Optimal::solve(7, $blob, $seed);
    is($reason, 'TIMEOUT', 'a limit of a microsecond: TIMEOUT');
    ok(length($path) <= length($seed), 'with a path no longer than the seed');
    is($Games::Sokoban::Solver::Optimal::LastStatus, 'TIMEOUT', 'the stop is named TIMEOUT');
    $Games::Sokoban::Solver::Optimal::LIMIT = 30;

    # a race already lost: IGNORE, named
    my %flag = (7 => 1);
    ($Games::Sokoban::Solver::Optimal::RACE_FLAG, $Games::Sokoban::Solver::Optimal::RACE_GID) = (\%flag, 7);
    ($reason) = Games::Sokoban::Solver::Optimal::solve(7, $blob, $seed);
    ($Games::Sokoban::Solver::Optimal::RACE_FLAG, $Games::Sokoban::Solver::Optimal::RACE_GID) = (undef, undef);
    ok($reason eq 'IGNORE' || $reason eq 'SOLVED', "a race already lost: IGNORE, or SOLVED before the first check ($reason)");
    is($Games::Sokoban::Solver::Optimal::LastStatus, $reason, 'and the stop is named the same');
}

# The copy loads neither BerkeleyDB nor a database module.
is_deeply([grep {m{Berkeley|DBI|SokDB|Zapis}} sort keys %INC], [], 'no storage module loaded');
done_testing;
