package Games::Sokoban::Solver::Replay;

# A solution played on its level, move by move, by the rules of the game and
# nothing else: the second reading of a path, sharing no code with the first
# (Games::Sokoban::Solver::Path, which rewrites a path from its pushes).
#
# The Sokoban project pairs the two in every gate that admits a solution: a
# path the rebuilding accepts must also play here, and the other way round.
# The program of this distribution does the same with the path it is about to
# print. Ported from the project's Games::Sokoban::Zapis::validate_path, itself
# a port of the replay in the project's web front end.
#
# Directions are read case-insensitively: a push is detected by a box standing
# on the target cell, not by the letter being a capital.
use v5.42;
our $VERSION = '0.01';
my %DELTA = ('u' => [-1, 0], 'd' => [1, 0], 'l' => [0, -1], 'r' => [0, 1]);

# digit cell code -> state name
my %OBR = (
    0 => 'sp',
    1 => 'empty',
    2 => 'avoid',
    3 => 'goal',
    4 => 'box',
    5 => 'player',
    6 => 'player_onavoid',
    7 => 'box_in',
    8 => 'player_in',
    9 => 'wall',
);

# What a step does to the cell the player leaves and the cell he enters: a pair
# [left, entered]; for a push a hash by what lies beyond the box, giving the
# triple [left, entered, beyond].
my %TRANSITIONS = (
    player => {
        sp     => ['sp', 'player'],
        goal   => ['sp', 'player_in'],
        avoid  => ['sp', 'player_onavoid'],
        box    => { sp => ['sp', 'player', 'box'], goal => ['sp', 'player', 'box_in'] },
        box_in => { sp => ['sp', 'player_in', 'box'], goal => ['sp', 'player_in', 'box_in'] },
    },
    player_in => {
        sp     => ['goal', 'player'],
        goal   => ['goal', 'player_in'],
        avoid  => ['goal', 'player_onavoid'],
        box    => { sp => ['goal', 'player', 'box'], goal => ['goal', 'player', 'box_in'] },
        box_in => { sp => ['goal', 'player_in', 'box'], goal => ['goal', 'player_in', 'box_in'] },
    },
    player_onavoid => {
        sp     => ['avoid', 'player'],
        goal   => ['avoid', 'player_in'],
        avoid  => ['avoid', 'player_onavoid'],
        box    => { sp => ['avoid', 'player', 'box'], goal => ['avoid', 'player', 'box_in'] },
        box_in => { sp => ['avoid', 'player_in', 'box'], goal => ['avoid', 'player_in', 'box_in'] },
    },
);

# Play $path against $code (comma-separated rows of digit cell codes). Returns
# an error string if any step is illegal or the final state is not solved, else
# undef (the path solves the level).
sub check ($code, $path) {
    my @rows = split(/,/a, $code, 0);
    my $h    = scalar @rows;
    my $w    = length $rows[0];
    my (@level, $pr, $pc, @goals);
    for my $r (0 .. $h - 1) {
        my @chars = split(//a, $rows[$r], 0);
        for my $c (0 .. $w - 1) {
            my $st = $OBR{ $chars[$c] };
            return "unknown cell code '$chars[$c]' at ($r,$c)" unless defined $st;
            $level[$r][$c] = $st;
            ($pr, $pc) = ($r, $c) if $st eq 'player' || $st eq 'player_onavoid' || $st eq 'player_in';
            push @goals, [$r, $c] if $st eq 'goal' || $st eq 'box_in' || $st eq 'player_in';
        }
    }
    return 'no player found' unless defined $pr;
    return 'no goals found'  unless @goals;
    for my $i (0 .. length($path) - 1) {
        my $ch  = substr($path, $i, 1);
        my $dir = lc $ch;
        my $d   = $DELTA{$dir};
        return "bad move char '$ch' at step $i" unless $d;
        my ($tr, $tc) = ($pr + $d->[0], $pc + $d->[1]);
        return "out of bounds at step $i" if $tr < 0 || $tr >= $h || $tc < 0 || $tc >= $w;
        my $cur = $level[$pr][$pc];
        my $tgt = $level[$tr][$tc];
        return "blocked by wall/empty at step $i" if $tgt eq 'wall' || $tgt eq 'empty';
        my $rule = $TRANSITIONS{$cur}{$tgt};
        return "no transition rule at step $i ($cur -> $tgt)" unless $rule;

        if (ref $rule eq 'ARRAY') {
            $level[$pr][$pc] = $rule->[0];
            $level[$tr][$tc] = $rule->[1];
        }
        else {
            my ($nr, $nc) = ($pr + 2 * $d->[0], $pc + 2 * $d->[1]);
            return "push out of bounds at step $i" if $nr < 0 || $nr >= $h || $nc < 0 || $nc >= $w;
            my $nxt      = $level[$nr][$nc];
            my $pushrule = $rule->{$nxt};
            return "illegal push (target occupied) at step $i" unless $pushrule;
            $level[$pr][$pc] = $pushrule->[0];
            $level[$tr][$tc] = $pushrule->[1];
            $level[$nr][$nc] = $pushrule->[2];
        }
        ($pr, $pc) = ($tr, $tc);
    } ## end for my $i (0 .. length(...))
    for my $g (@goals) {
        return "not solved (goal at $g->[0],$g->[1] not covered)" if $level[$g->[0]][$g->[1]] ne 'box_in';
    }
    return undef;
} ## end sub check
1;
__END__

=head1 NAME

Games::Sokoban::Solver::Replay - play a solution on its level, by the rules alone

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Replay ();

    my $error = Games::Sokoban::Solver::Replay::check($code, $path);
    die "not a solution: $error" if defined $error;

=head1 DESCRIPTION

A solution is a string of letters C<l r u d>, each a step of the player, in
upper case where the step pushes a box. This module plays such a string on a
level given as the distribution stores levels -- the rows of the board as
strings of digits, joined by commas (C<0> floor, C<1> a filler cell, C<2> a
cell boxes must avoid, C<3> a goal, C<4> a box, C<5> the player, C<6> the
player on such a cell, C<7> a box on a goal, C<8> the player on a goal, C<9> a
wall) -- and says whether it is a solution: every step legal, no box pushed
into a wall or another box, and at the end every goal under a box.

It shares no code with L<Games::Sokoban::Solver::Path>, which writes a path
again from its pushes and so checks it a second way; the two readings are
paired wherever a path is admitted, and a path must satisfy both.

The case of a letter is not trusted: whether a step pushes is read off the
board. A cell marked C<1> (filler) stops the player like a wall.

=head1 FUNCTIONS

=over 4

=item check CODE, PATH

Returns C<undef> when PATH solves the level CODE, otherwise a sentence saying
at which step and why it does not (a letter that is none, a step into a wall
or off the board, a box pushed against a wall or another box, a goal still
empty at the end).

=back

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
