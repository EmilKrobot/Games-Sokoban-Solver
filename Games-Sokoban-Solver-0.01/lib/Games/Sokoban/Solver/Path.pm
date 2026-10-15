package Games::Sokoban::Solver::Path;

# THE PATH OF A SOLUTION, WRITTEN AGAIN FROM ITS PUSHES.
#
# Whatever a search calls a position and however far one of its moves carries a
# box, a solution comes down to elementary steps of one kind: the player walks
# to a box and pushes it one cell. The push says where he had to stand; between
# two pushes he has to get from where the last one left him to where the next
# one needs him, and nothing else. So a path is its row of pushes, and the
# letters are written from that row and from nothing else:
#
#   1 the given path is played on the level and its pushes are taken down, one
#     after another, UNTIL EVERY GOAL IS UNDER A BOX -- there the solution ends,
#     whatever letters follow;
#   2 where the boxes stand, after some pushes, exactly as they stood before
#     them, and the player could simply have walked on from where he stood
#     then, the pushes between are left out -- IF the path gets shorter by it;
#   3 the pushes that stay are played from the start, the player walking a
#     SHORTEST way to each of them.
#
# Every engine calls rebuilt() on its finished path while the level is still in
# its memory, as the last thing before it says SOLVED, and so no engine can
# return a path that goes on after the game is solved, pushes a box away only
# to bring it back, or walks further between two pushes than it has to --
# whatever way it had of searching and of writing its letters down.
#
# Step 2 is counted, not assumed. The same boxes a second time are not always
# a waste: a player may push a box out of a narrow place, go through and push it
# back behind him, where the walk round is longer (608 of the 18 231 solutions
# of the Sokoban project's optimal solver do it, proved shortest ones among
# them). So every such stretch is an OFFER -- from the earlier moment the path
# may go on with the push that follows the later one, at the price of the walk
# there -- and what is written is the cheapest way through the path's own
# pushes with those offers in it. On equal price the path's own push is kept.
#
# The walk is breadth first with the neighbours taken left, right, down, up --
# the order of the level's walk graph (the Code module), so it is the very walk
# the Firstbet engine's and the optimal solver's cesta() take: a path those two
# built, with no such stretch in it, comes back letter for letter.
#
# Lineage: Games::Sokoban::Path 0.01 of the Sokoban project (2026-10-12), held
# there on every stored path of four tables to a second writing that shares no
# code with it.

use v5.42;
use warnings FATAL => 'uninitialized';
use Carp ();

our $VERSION = '0.01';

=head1 NAME

Games::Sokoban::Solver::Path - the path of a solution, written again from its pushes

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Path ();

    my $path = Games::Sokoban::Solver::Path::rebuilt(
        'path'   => $letters,        # as an engine wrote them
        'width'  => $width,          # cells in a row of the board
        'floor'  => \@floor_cells,   # every cell that is no wall
        'goals'  => \@goal_cells,
        'boxes'  => \@start_boxes,
        'player' => $start_cell,
    );

=head1 DESCRIPTION

A solution is stored as letters: C<l r u d> for a step of the player, in upper
case when the step pushes a box. A board is a rectangle of cells numbered row
by row from zero, so the neighbours of a cell are the cell number less one,
plus one, less the width and plus the width.

Underneath the letters a solution is a row of B<pushes>: a box goes from one
cell to the next. A push fixes where the player stands when he makes it (the
cell on the other side of the box), so the only freedom the letters have is
the way the player walks from one push to the next -- and the only right
answer to that is a shortest way.

=head1 FUNCTIONS

=over 4

=item rebuilt

Takes the named arguments of the synopsis and returns the path written again.
Three things are done to it. The pushes of the given path are taken down up to
the moment every goal is covered by a box; what follows is dropped. Where the
boxes stand after some pushes exactly as they stood before them, and the
player can walk from where he stood then to the push that comes next, the
pushes between are left out whenever that makes the path shorter (it need not:
pushing a box out of a narrow place, going through and pushing it back can be
shorter than the walk round). And the pushes that stay are each reached by a
shortest walk. The case of the given letters is not trusted; whether a step
pushes is read off the board.

The result is a solution of the same level made of pushes of the given path,
in their order, and it is never longer than the given path.

It dies, naming the letter, when the given path cannot be played (a letter
that is none, a step into a wall or off the board, a box pushed against a wall
or another box) and when the path ends with a goal still empty. An engine may
therefore use it as its replay check as well.

=item level

Takes a board as the distribution stores it -- the rows of the board as strings
of digits, joined by commas: C<9> a wall and C<1> a filler cell (neither can be
walked on), C<3> a goal, C<4> a box, C<5> the player, C<7> a box on a goal,
C<8> the player on a goal, C<6> the player on a cell boxes must avoid, anything
else plain floor -- and returns the five named arguments C<rebuilt> wants of a
level, everything but the path. For a caller that holds the stored board and
not an engine's tables:

    my $path = Games::Sokoban::Solver::Path::rebuilt(Games::Sokoban::Solver::Path::level($code), 'path' => $letters);

=back

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut

sub level ($code) {
    my @rows  = split(/,/a, $code, -1);
    my $cells = join('', @rows);
    my (@floor, @goals, @boxes, $player);
    for my $cell (0 .. length($cells) - 1) {
        my $digit = substr($cells, $cell, 1);
        push @floor, $cell if $digit ne '9' and $digit ne '1';
        push @goals, $cell if $digit eq '3' or $digit eq '7' or $digit eq '8';
        push @boxes, $cell if $digit eq '4' or $digit eq '7';
        $player = $cell    if $digit eq '5' or $digit eq '6' or $digit eq '8';
    }
    Carp::confess('the board has no player') unless defined $player;
    return ('width' => length $rows[0], 'floor' => \@floor, 'goals' => \@goals, 'boxes' => \@boxes, 'player' => $player);
}

# Every cell the player can walk to from $from over the free cells without a
# box: the cell each was reached from ($from from itself), breadth first, the
# neighbours taken left, right, down, up. With a $target the walk stops there.
sub reach ($free, $box, $width, $from, $target = -1) {
    my @came;
    $came[$from] = $from;
    my @queue = ($from);
    my $head  = 0;
    while ($head < @queue) {
        my $cell   = $queue[$head++];
        my $column = $cell % $width;
        for my $delta (-1, 1, $width, -$width) {
            next if $delta == -1 and $column == 0 or $delta == 1 and $column == $width - 1;    # no step round the edge of a row
            my $next = $cell + $delta;
            next if $next < 0 or !$free->[$next] or $box->[$next] or defined $came[$next];
            $came[$next] = $cell;
            return \@came if $next == $target;
            push @queue, $next;
        }
    }
    return \@came;
}

# The letters of a shortest walk from $from to $target, '' when the two are the
# same cell, undef when there is no way.
sub walk ($free, $box, $width, $from, $target) {
    return '' if $from == $target;
    my $came = reach($free, $box, $width, $from, $target);
    return undef unless defined $came->[$target];
    my %letter  = (-1 => 'l', 1 => 'r', $width => 'd', -$width => 'u');
    my $letters = '';
    for (my $at = $target; $at != $from; $at = $came->[$at]) {$letters .= $letter{ $at - $came->[$at] }}
    return scalar reverse $letters;
}

sub rebuilt (%level) {
    my ($path, $width, $start) = @level{ 'path', 'width', 'player' };
    my (@free, @goal, @box);
    $free[$_] = 1 for @{ $level{'floor'} };
    $goal[$_] = 1 for @{ $level{'goals'} };
    $box[$_]  = 1 for @{ $level{'boxes'} };
    my %delta = ('l' => -1, 'r' => 1, 'u' => -$width, 'd' => $width);

    # 1 -- the pushes of the path, until the game is solved; and where the
    # boxes stand alike. A position is a number of pushes made, 0 the start.
    my @pushes;
    my $man  = $start;
    my $open = grep {!$box[$_]} @{ $level{'goals'} };    # goals without a box
    Carp::confess('the level is solved before the first step') unless $open;
    my $layout = '';                                     # the boxes, a bit a cell
    vec($layout, $#free, 1) = 0;                         # as long as the board from the start: the same boxes, the same string
    vec($layout, $_, 1) = 1 for @{ $level{'boxes'} };
    my %alike = ($layout => [0]);                        # the boxes => the positions that have them
    my $twice = 0;
    for my $at (0 .. length($path) - 1) {
        my $letter = substr($path, $at, 1);
        my $delta  = $delta{ lc $letter } // Carp::confess("the path does not play: letter $at is '$letter'");
        my $column = $man % $width;
        my $to     = $man + $delta;
        Carp::confess("the path does not play: letter $at '$letter' steps into a wall")
            if $to < 0 or !$free[$to] or $delta == -1 and $column == 0 or $delta == 1 and $column == $width - 1;
        if ($box[$to]) {
            my $beyond = $to + $delta;
            Carp::confess("the path does not play: letter $at '$letter' pushes the box on cell $to against a wall or another box")
                if $beyond < 0 or !$free[$beyond] or $box[$beyond] or $delta == -1 and $to % $width == 0 or $delta == 1 and $to % $width == $width - 1;
            $box[$to]     = 0;
            $box[$beyond] = 1;
            vec($layout, $to,     1) = 0;
            vec($layout, $beyond, 1) = 1;
            ++$open if $goal[$to];
            --$open if $goal[$beyond];
            push @pushes, [$to, $beyond];
            if (my $positions = $alike{$layout}) {push @$positions, scalar @pushes; $twice = 1}
            else                                {$alike{$layout} = [scalar @pushes]}
        }
        $man = $to;
        last unless $open;
    }
    Carp::confess('the path does not solve the level: it ends with a goal still empty') if $open;

    # 2 -- the cheapest way through those pushes when a stretch between two
    # positions with the same boxes may be left out: from position p the path
    # goes on with its own push, or with the push that follows a later position
    # of the same boxes, if the player can walk there from where he stands at p.
    my @kept = (0 .. $#pushes);    # the pushes that stay, by their place in @pushes
    if ($twice) {
        my %later;                 # a position => the later ones with the same boxes
        for my $positions (grep {@$_ > 1} values %alike) {
            $later{ $positions->[$_] } = [@{$positions}[ $_ + 1 .. $#$positions ]] for 0 .. $#$positions - 1;
        }
        @box = ();
        $box[$_] = 1 for @{ $level{'boxes'} };
        $man = $start;
        my @price = (0);           # the steps to a position
        my @before;                # the position the push into a position was made from
        for my $position (0 .. $#pushes) {
            my @offers = grep {$_ < @pushes} @{ $later{$position} // [] };
            my $came   = @offers ? reach(\@free, \@box, $width, $man) : undef;
            for my $next ($position, @offers) {    # the push made: the path's own, or the one after a later position
                my ($from, $to) = @{ $pushes[$next] };
                my $stance = 2 * $from - $to;
                my $steps;
                if (!$came) {
                    $steps = length(walk(\@free, \@box, $width, $man, $stance)
                            // Carp::confess("the player cannot get from cell $man to the push of the box on cell $from"));
                }
                else {
                    unless (defined $came->[$stance]) {      # another part of the floor: no offer
                        Carp::confess("the player cannot get from cell $man to the push of the box on cell $from") if $next == $position;
                        next;
                    }
                    $steps = 0;
                    for (my $at = $stance; $at != $man; $at = $came->[$at]) {++$steps}
                }
                my $price = $price[$position] + $steps + 1;
                next if defined $price[ $next + 1 ] and ($price > $price[ $next + 1 ] or $price == $price[ $next + 1 ] and $next != $position);
                $price[ $next + 1 ]  = $price;
                $before[ $next + 1 ] = $position;
            }
            my ($from, $to) = @{ $pushes[$position] };
            $box[$from] = 0;
            $box[$to]   = 1;
            $man        = $from;
        } ## end for my $position (0 .. $#pushes)
        @kept = ();
        for (my $position = @pushes; $position > 0; $position = $before[$position]) {unshift @kept, $position - 1}
    } ## end if ($twice)

    # 3 -- the pushes that stay, from the start, a shortest walk to each
    @box = ();
    $box[$_] = 1 for @{ $level{'boxes'} };
    $man = $start;
    my %letter = (-1 => 'L', 1 => 'R', $width => 'D', -$width => 'U');
    my $out    = '';
    for my $push (@pushes[@kept]) {
        my ($from, $to) = @$push;
        my $steps = walk(\@free, \@box, $width, $man, 2 * $from - $to)
            // Carp::confess("the player cannot get from cell $man to the push of the box on cell $from");
        $out .= $steps . $letter{ $to - $from };
        $box[$from] = 0;
        $box[$to]   = 1;
        $man        = $from;
    }
    return $out;
} ## end sub rebuilt

1;
