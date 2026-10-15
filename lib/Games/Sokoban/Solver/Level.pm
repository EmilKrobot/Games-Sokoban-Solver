package Games::Sokoban::Solver::Level;

# A level as a text file has it, turned into the digits every other module
# reads -- and checked to be a level at all.
#
# The standard text of a level (XSB) draws the board with # for a wall, $ a
# box, . a goal, @ the player, * a box on a goal, + the player on a goal, and a
# space for floor; the rows need not be of one length. Here it becomes a
# rectangle of digits (0 floor, 3 goal, 4 box, 5 player, 7 box on goal,
# 8 player on goal, 9 wall), rows joined by commas, in two forms: code0 keeps
# the floor the player can never reach as 1, a filler that is drawn as floor
# but not walked on, so that the level can still be shown as its author drew
# it; code1 turns every unreachable cell into a wall, so that the solvers
# search only what matters. "Reach" is the player walking over every cell that
# is not a wall, boxes included -- the shape of the level, not a position of it.
#
# A level that is no level is refused with one sentence: a character that is
# none of the level's, not exactly one player, no box, boxes and goals of
# different numbers, every box already on a goal. A level whose reachable floor touches the edge of its rectangle
# -- an open level, which the text format allows -- gets a ring of walls around
# the whole rectangle first, since outside the rectangle there is nothing to
# walk on; the caller is told.
#
# Lineage: hra(), dummy() and player() of app/base/zdroj.pl in the Sokoban
# project, whose zdroj.code0/code1 columns this module reproduces byte for byte
# on every level of that project's collection.

use v5.42;
use Carp ();

our $VERSION = '0.01';

# A line of a level: the XSB characters only, with at least one wall. '-' and
# '_' are the floor variants some files use.
my $LEVEL_LINE = qr/\A[ #\$.\@*+\-_]*#[ #\$.\@*+\-_]*\z/;

# The levels of a text (a whole file): a list of hashes {index, title, rows},
# the rows as the file has them (floor variants made spaces, trailing blanks
# cut). A level is a maximal run of level lines; its title is the nearest
# non-blank line before it that is not a level line (a leading "Title:" is
# dropped), or a "Title:" line right after it, or "Level N".
sub read ($text) {
    my @lines = split /\r?\n/, $text;
    my (@levels, @rows, $pending);
    my $flush = sub {
        return unless @rows;
        push @levels, {'index' => scalar(@levels) + 1, 'title' => $pending // 'Level ' . (@levels + 1), 'rows' => [@rows], 'titled' => defined $pending};
        @rows    = ();
        $pending = undef;
    };
    for my $line (@lines) {
        (my $clean = $line) =~ s/\s+\z//;
        if ($clean =~ $LEVEL_LINE) {
            $clean =~ tr/\-_/  /;
            push @rows, $clean;
            next;
        }
        $flush->();
        next unless $clean =~ /\S/;
        if ($clean =~ /\ATitle:\s*(.*)\z/i) {
            my $title = $1;
            if (@levels and !$levels[-1]{'titled'}) { $levels[-1]{'title'} = $title; $levels[-1]{'titled'} = 1 }
            else                                    { $pending = $title }
            next;
        }
        $pending = $clean;
    }
    $flush->();
    delete $_->{'titled'} for @levels;
    return @levels;
}

# The rows of one level -> ($code0, $code1, \%info), or a death with one
# sentence beginning 'REFUSED:'. The rows are taken as they come: a row shorter
# than the widest is padded with floor on the right, trailing blanks are kept
# (read() cuts them; a caller that wants the author's rectangle keeps them).
sub normalize ($rows, $ringed = 0) {
    my @rows = map { my $r = $_; $r =~ tr/\-_/  /; $r } @$rows;
    Carp::croak('REFUSED: an empty level') unless @rows;
    for my $row (@rows) {
        if ($row =~ /([^ #\$.\@*+])/) { Carp::croak("REFUSED: the character '$1' is not part of a level") }
    }
    my $w = 0;
    for (@rows) { $w = length $_ if length $_ > $w }
    $_ .= ' ' x ($w - length $_) for @rows;
    my $h = scalar @rows;
    my @digits = map { tr/ .$@*+#/0345789/r } @rows;
    my $flat = join '', @digits;
    my $players = $flat =~ tr/58//;
    Carp::croak("REFUSED: $players players (there must be one)") if $players != 1;
    $flat =~ /[58]/;
    my $man = $-[0];

    # Every cell the player can reach, walking over anything that is not a wall.
    my @maze    = split //, $flat;
    my $last    = $#maze;
    my %visited = ($man => 1);
    my @heap    = ($man);
    my $rim     = 0;
    while (@heap) {
        my $x      = shift @heap;
        my $column = $x % $w;
        my $row    = int($x / $w);
        $rim = 1 if $row == 0 or $row == $h - 1 or $column == 0 or $column == $w - 1;
        for my $t ($x - 1, $x + 1, $x + $w, $x - $w) {
            next if $t < 0 or $t > $last;
            next if $t == $x - 1 and $column == 0 or $t == $x + 1 and $column == $w - 1;
            next if $maze[$t] eq '9';
            next if $visited{$t}++;
            push @heap, $t;
        }
    }

    # An open level: the reachable floor touches the edge of the rectangle.
    # Outside the rectangle there is nothing to walk on, so a ring of walls
    # round the whole of it changes nothing about the level and gives every
    # cell a neighbour on each side, which the modules after this one assume.
    if ($rim) {
        Carp::croak('REFUSED: the level is open even inside a ring of walls') if $ringed;
        my ($code0, $code1, $info) = normalize([('#' x ($w + 2)), (map { "#$_#" } @rows), ('#' x ($w + 2))], 1);
        $info->{'ring'} = 1;
        unshift @{ $info->{'notes'} }, 'the level touches the edge of its rectangle: a ring of walls was added';
        return ($code0, $code1, $info);
    }

    my @maze0 = @maze;
    my @maze1 = @maze;
    for my $i (0 .. $last) {
        next if $maze[$i] eq '9';
        next if $visited{$i};
        $maze0[$i] = '1' if $maze[$i] eq '0';
        $maze1[$i] = '9';
    }
    my $code0 = join ',', unpack("(a$w)*", join '', @maze0);
    my $code1 = join ',', unpack("(a$w)*", join '', @maze1);
    my $nbox  = $code1 =~ tr/47//;
    my $ncell = $code1 =~ tr/034578//;
    my $ngoal = $code1 =~ tr/387//;
    Carp::croak('REFUSED: no box at all') unless $nbox;
    Carp::croak("REFUSED: boxes and goals differ ($nbox boxes, $ngoal goals)") if $ngoal != $nbox;
    Carp::croak('REFUSED: every box is already on a goal (nothing to solve)') unless $flat =~ /4/;

    my @notes;
    push @notes, "only $ncell cells the player can reach: smaller than anything measured" if $ncell < 10;
    push @notes, "$ncell cells the player can reach: larger than anything measured (400)" if $ncell > 400;
    push @notes, "$nbox boxes: more than anything measured (30)"                           if $nbox > 30;
    return ($code0, $code1, {'w' => $w, 'h' => $h, 'nbox' => $nbox, 'ncell' => $ncell, 'ngoal' => $ngoal, 'ring' => 0, 'notes' => \@notes});
}

# The digits of a board back as the text of a level, one row per line.
sub as_text ($code) {
    return join("\n", map { tr/0123456789/   .$@@*+#/r } split /,/, $code, -1) . "\n";
}

1;

__END__

=head1 NAME

Games::Sokoban::Solver::Level - read levels from their text and turn them into digits

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Level ();

    my @levels = Games::Sokoban::Solver::Level::read($text_of_a_file);
    for my $level (@levels) {
        my ($code0, $code1, $info) = Games::Sokoban::Solver::Level::normalize($level->{'rows'});
        say "$level->{'title'}: $info->{'nbox'} boxes, $info->{'ncell'} cells";
    }
    print Games::Sokoban::Solver::Level::as_text($code1);

=head1 DESCRIPTION

The standard text of a Sokoban level draws the board with C<#> for a wall,
C<$> a box, C<.> a goal, C<@> the player, C<*> a box on a goal, C<+> the
player on a goal and a space (or C<-> or C<_>) for floor. A file holds any
number of levels, each a run of such lines, with titles between them.

This module reads such a file and turns each level into the form every other
module of the distribution works on: a rectangle of digits, the rows joined by
commas -- C<0> floor, C<3> goal, C<4> box, C<5> player, C<7> box on a goal,
C<8> player on a goal, C<9> wall -- in two versions. In B<code0> the floor the
player can never reach is C<1>, a filler drawn as floor but not walked on, so
that the level can still be shown as its author drew it. In B<code1> every
unreachable cell is a wall, so that the solvers see only what matters. The
player "reaches" every cell that is not a wall, boxes included: this is about
the shape of the level, not about a position of the game.

=head1 FUNCTIONS

=over 4

=item read TEXT

The levels in TEXT, as a list of hashes with C<index> (counted from 1),
C<title> and C<rows> (the lines of the level, floor variants made spaces,
trailing blanks cut). A level is a maximal run of level lines. Its title is
the nearest non-blank line before it that is not a level line, with a leading
C<Title:> dropped; a C<Title:> line right after a level names that level when
nothing before it did; otherwise the title is C<Level N>.

=item normalize ROWS

Takes an array reference of the rows of one level and returns
C<($code0, $code1, \%info)>, where C<%info> has C<w>, C<h>, C<nbox>, C<ncell>
(the cells the player can reach), C<ngoal>, C<ring> and C<notes> (an array
of sentences about the level: a size outside what the solvers were measured
on, or the ring).

A level whose reachable floor touches the edge of its rectangle is an open
level; a ring of walls is put round the whole rectangle first, and the first
note says so.

It dies with one sentence beginning C<REFUSED:> when the rows are no level:
a character that is not part of a level, not exactly one player, no box,
boxes and goals of different numbers, or every box already on a goal.

=item as_text CODE

The digits of a board back as the text of a level, one row per line, the
fillers and the cells boxes must avoid shown as floor.

=back

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
