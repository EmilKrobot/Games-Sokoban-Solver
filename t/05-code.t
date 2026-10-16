# Code: the reduction of a level, the forced opening, the shrink, the refusal.
use v5.42;
use Test::More;
use Games::Sokoban::Solver::Level  ();
use Games::Sokoban::Solver::Code   ();
use Games::Sokoban::Solver::Replay ();
my $prepare = \&Games::Sokoban::Solver::Code::prepare;

# The player at the bottom of a dead-end corridor: the template walks him out
# (one step up) and walls the corridor; the row of wall that is left is shrunk.
{
    my %game = $prepare->('99999,93409,90009,99959,99999');
    is($game{'code'}, '99999,93429,92269,99999',
        'the corridor is walled and the empty row shrunk; avoid cells marked 2, the player on one 6');
    is($game{'firststep'}, 'u', 'the forced opening is the step out');
    is($game{'w'},         5,   'width');
    is_deeply($game{'goal'},    [6], 'the goal');
    is_deeply($game{'baggage'}, [7], 'the box');
    is($game{'has_hole'}, 0, 'no hole kept for the engines');
    ok(exists $game{'cg'}{11} && !exists $game{'cg'}{18}, 'the walk graph has the floor and not the walled corridor');

    # a solution of the reduced level, with the opening in front, plays on the original
    is(Games::Sokoban::Solver::Replay::check('99999,93409,90009,99959,99999', $game{'firststep'} . 'uL'),
        undef, 'opening + a solution of the reduced level replays on the original');
}

# Outer rows and columns of wall are shrunk away.
{
    my %game = $prepare->('9999999,9999999,9934599,9999999,9999999');
    is($game{'code'},      '99999,93469,99999', 'two rings of wall shrunk to one');
    is($game{'firststep'}, '',                  'no forced opening');
}

# A level without anything to reduce comes back as it is, the avoid cells marked.
{
    my %game = $prepare->('9999999,9300009,9900099,9900499,9900599,9999999');
    is(
        $game{'code'},
        '999999,930029,990029,990049,992269,999999',
        'the dead-end cells are avoid cells (2), the player on one is 6'
      );
    is(scalar @{ $game{'goal'} },    1, 'one goal');
    is(scalar @{ $game{'baggage'} }, 1, 'one box');
}

# The levels of the fixture file go through Level and Code; every cg neighbour is a cell.
{
    open my $fh, '<', 't/data/micro.xsb' or die $!;
    my $text = do {local $/; <$fh>};
    close $fh;
    for my $level (Games::Sokoban::Solver::Level::read($text)) {
        my ($code0, $code1) = Games::Sokoban::Solver::Level::normalize($level->{'rows'});
        my %game = $prepare->($code1);
        is(scalar @{ $game{'goal'} }, scalar @{ $game{'baggage'} }, "$level->{'title'}: as many goals as boxes");
        my $bad = 0;
        for my $cell (keys %{ $game{'cg'} }) {
            $bad += grep {!exists $game{'cells'}{$_}} @{ $game{'cg'}{$cell} };
        }
        is($bad, 0, "$level->{'title'}: every neighbour in cg is a cell");
    }
}

# A dead-end corridor the templates do not know is refused, with the board drawn.
{
    my $ok = eval {$prepare->('999999,930009,999909,999949,999959,999999'); 1};
    ok(!$ok, 'a corridor shape outside the templates is refused');
    like($@, qr/\AREFUSED: a dead-end corridor the templates do not know: '642 29'/, 'the sentence names the shape');
    like(
        $@,
        qr/\n#\.  -#\n####-#\n####\$#\n####\@#\n/,
        'the board is drawn after the sentence (avoid cells as -, the player as @)'
    );
}
done_testing;
