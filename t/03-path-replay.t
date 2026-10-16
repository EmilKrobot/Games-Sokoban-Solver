# Two readings of a solution that share no code -- Path::rebuilt, which writes
# the path again from its pushes, and Replay::check, which plays it by the
# rules -- must agree on every string tried UP TO THE MOMENT THE LEVEL IS
# SOLVED: a string Replay accepts is one rebuilt lives on, a string Replay
# refuses before the last goal is covered is one rebuilt dies on. Letters AFTER
# the solution are the one place the two part by design: rebuilt drops them
# (a solution ends where the last goal is covered), Replay plays them and
# refuses an illegal one -- which is why the program prints the rebuilt path
# and checks THAT with Replay. The solutions come from the brute-force oracle
# in t/lib, which shares no code with either.
use v5.42;
use Test::More;
use lib 't/lib';
use BruteForce                     ();
use Games::Sokoban::Solver::Path   ();
use Games::Sokoban::Solver::Replay ();

sub rebuilt ($code, $path) {
    return Games::Sokoban::Solver::Path::rebuilt(Games::Sokoban::Solver::Path::level($code), 'path' => $path);
}

# Both readings of one string, as a pair: (what Replay said, what rebuilt gave
# or how it died).
sub both ($code, $path) {
    my $check = Games::Sokoban::Solver::Replay::check($code, $path);
    my $built = eval {rebuilt($code, $path)};
    my $died  = $@;
    return ($check, $built, $died);
}

# They must agree: accepted by both, or refused by both.
sub agree ($code, $path, $name) {
    my ($check, $built, $died) = both($code, $path);
    if (defined $check) {
        ok(!defined $built, "$name: Replay refuses ($check) and rebuilt dies") or diag("rebuilt gave '$built'");
        return (undef, $died);
    }
    ok(defined $built, "$name: Replay accepts and rebuilt lives") or diag("rebuilt died: $died");
    return ($built, undef);
}

# Three micro levels as the distribution stores them: rows of digits joined by
# commas (9 wall, 0 floor, 3 goal, 4 box, 5 player).
my %level = (
    'one box, a corner to walk round' => '9999999,9000009,9043009,9050009,9999999',
    'two boxes side by side'          => '999999,900009,904409,903359,999999',
    'two columns, no walls at all'    => '50,40,30',
);

# A wall step from the start, per level: the player's neighbour in that
# direction is a wall (or off the board).
my %wall_step = (
    'one box, a corner to walk round' => 'd',
    'two boxes side by side'          => 'd',
    'two columns, no walls at all'    => 'u',
);

# A harmless detour from the start: two steps that go and come back over floor.
my %detour = (
    'one box, a corner to walk round' => 'rl',
    'two boxes side by side'          => 'lr',
);
for my $name (sort keys %level) {
    my $code = $level{$name};
    my $sol  = BruteForce::solve($code);
    ok(defined $sol && length $sol, "$name: the oracle found a solution (" . ($sol // '') . ')');
    next unless defined $sol;
    my ($built) = agree($code, $sol, "$name: the oracle's solution");
    is(length($built // ''), length $sol, "$name: rebuilt is as long as the oracle's shortest solution");
    is(Games::Sokoban::Solver::Replay::check($code, $built // ''), undef, "$name: the rebuilt path replays too");

    # spoiled before the solution: each must be refused by both readings
    agree($code, 'X' . $sol,               "$name: a letter that is none");
    agree($code, $wall_step{$name} . $sol, "$name: a step into a wall or off the board");
    agree($code, substr($sol, 0, -1),      "$name: cut short, a goal still empty");

    # letters after the solution: dropped by rebuilt, played by Replay
    is(eval {rebuilt($code, $sol . 'X')}, $built, "$name: rebuilt drops what follows the solution, even a letter that is none");
    like(
        Games::Sokoban::Solver::Replay::check($code, $sol . 'X'),
        qr/bad move char/,
        "$name: ... while Replay plays on and refuses it"
    );
    if (my $detour = $detour{$name}) {
        my ($built2) = agree($code, $detour . $sol, "$name: a detour that goes and comes back");
        is(length($built2 // ''), length $sol, "$name: rebuilt drops the detour and is as long as the solution");
    }
} ## end for my $name (sort keys...)

# A push against another box, and a push against a wall.
{
    my $code = '999999,954439,999999';    # player, two boxes in a row, a goal, a wall
    agree($code, 'R', 'a push of a box into a box is refused by both');
    my $wall = '99999,95439,99999';       # player, box, goal, wall: R solves, RR pushes into the wall
    agree($wall, 'R', 'one box pushed onto its goal is accepted by both');
    is(rebuilt($wall, 'RR'), 'R', 'a second push after the solution is dropped by rebuilt');
    like(Games::Sokoban::Solver::Replay::check($wall, 'RR'), qr/illegal push/, '... while Replay refuses the push into the wall');
}

# The case of the letters is read off the board, not trusted.
{
    my $code = '99999,95439,99999';
    is(rebuilt($code, 'r'),                               'R',   'a lower-case letter that pushes comes back as a push');
    is(Games::Sokoban::Solver::Replay::check($code, 'r'), undef, '... and Replay accepts it as one');
}

# What the oracle says when there is nothing to solve or no way.
is(BruteForce::solve('99999,97599,99999'),    '',    'a level solved before the first step: the empty path');
is(BruteForce::solve('999999,954039,999999'), 'RR',  'a box two cells from its goal: the oracle finds RR');
is(BruteForce::solve('9999,9549,9939,9999'),  undef, 'a box in a corner: no solution');
done_testing;
