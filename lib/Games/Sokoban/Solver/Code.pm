package Games::Sokoban::Solver::Code;

# THE LEVEL REDUCED TO WHAT THE SEARCH NEEDS, and the first record of it.
#
# A level as its author drew it carries things no search should pay for: rows of
# wall round the outside, floor the player can never reach, a box standing on a
# goal in a corner that can never move again, dead-end corridors with one
# entrance whose contents (a box, a goal, the player) have exactly one way to
# go. This module takes the digits of a level (Level's code1) and reduces it,
# repeating until nothing changes:
#
#   shrink      rows and columns of wall beyond the outermost wall go
#   dummy       floor the player cannot reach becomes wall
#   rohy        a box on a goal in a corner is a wall from now on
#   find_avoid  the cells a box can never be pushed from onto any goal are
#               marked (2, the player on one is 6): the solvers never put a
#               box there
#   holes       a dead-end corridor is drained by a template: its box pushed
#               out or in, the player walked out, the goal moved -- and the
#               moves that stand for it are written down as the FORCED OPENING
#               ($FirstStep), the letters every solution of the reduced level
#               must be prefixed with to play on the original one; a corridor
#               no template drains is kept as a 'hole' the engines treat as a
#               macro
#
# What comes out is the first record of the level (%Game as prepare() returns
# it): the digits, the goals and boxes, the player's walk graph cg, the avoid
# cells, the holes, the forced opening and the width. The Parser takes it from
# there.
#
# A level the templates cannot drain is REFUSED with one sentence and the board
# drawn, never let through broken: the Sokoban project read 43 000 levels this
# way and the templates cover every shape they had, but a new level can show a
# new one.
#
# Lineage: Games::Sokoban::Code 1.0 of the Sokoban project, whose
# game_blob.code_blob, game_blob.code and game_data.firststep this module
# reproduces on every level of that project's collection (xt/eq_code.pl).
use v5.42;
use warnings FATAL => 'uninitialized';
use Carp ();
use Storable ('dclone');
use Games::Sokoban::Solver::Data ();
our $VERSION = '0.01';
my ($Zmena, $W, $H, %Cells, @Maze, $Player, $Code, @Holes, %RealHole, $FirstStep, @Goal, @Baggage, %Game, %Avoid, %Cg);
my %Hole_templates = %{ Games::Sokoban::Solver::Data::load('hole_templates.stor') };

# A level this module cannot reduce: one sentence, the board as it stands, and
# the record of the corridor that stopped it.
sub _refuse ($why, $hole = undef) {
    my $board = join("\n", map {tr/0123456789/  \-.$@@*+#/r} split /,/, $Code, -1);
    my $where =
        $hole
        ? sprintf(
            "\n  corridor cells %s, contents '%s', direction %s, entry %s, after %s",
            join(' ', @{ $hole->{'hole'} }),
            $hole->{'ostr'}, $hole->{'smer'}, $hole->{'sentry'}, $hole->{'safter'}
        )
        : '';
    Carp::croak("REFUSED: $why$where\n$board\n");
}

sub apply ($key, $h) {
    state $revers = { 'd', 'u', 'u', 'd', 'l', 'r', 'r', 'l' };
    my ($step, $hole, $entry, $after) = @{ $Hole_templates{$key} };
    my $t = $h->{'smer'};
    my $T = uc $t;
    my $z = $revers->{$t};
    my $Z = uc $z;
    $step =~ s/t/$t/g;
    $step =~ s/T/$T/g;
    $step =~ s/z/$z/g;
    $step =~ s/Z/$Z/g;
    $FirstStep .= $step;
    $Maze[$h->{'entry'}] = $entry;
    $Maze[$h->{'after'}] = $after;

    foreach my $i (0 .. $#{$hole}) {
        $Maze[$h->{'hole'}[$i]] = $hole->[$i];
    }
    return;
} ## end sub apply

sub translines(@lines) {
    my @c;
    foreach $_ (@lines) {
        my $i = 0;
        $c[$i++] .= $_ foreach (split(//a, $_, 0));
    }
    return @c;
}

sub shrink(@lines) {
    my ($w, $h) = (length($lines[0]), scalar @lines);
    my $walls = '9' x $w;
    pop @lines   while @lines > 2 and $lines[-2] eq $walls;
    shift @lines while $lines[1] eq $walls;
    @lines = translines(@lines);
    $walls = '9' x length $lines[0];
    pop @lines   while @lines > 2 and $lines[-2] eq $walls;
    shift @lines while $lines[1] eq $walls;
    @lines = translines(@lines);
    return @lines;
}

sub init($code) {
    $Zmena   = 0;
    @Maze    = ();
    %Cells   = ();
    @Goal    = ();
    @Baggage = ();
    my @lines = split(/,/a, $code, 0);
    $Code = $code;
    ($W, $H) = (length($lines[0]), scalar @lines);
    my $data = $code =~ tr/,//dr;
    Carp::confess('level has no starting point') unless $data =~ /[568]/a;
    $Player = $-[0];
    @Maze   = split(//a, $data, 0);

    for (my $i = 0; $i <= $#Maze; ++$i) {
        my $p = $Maze[$i];
        next if $p == 9;
        push @Goal,    $i if $p =~ /[378]/aa;
        push @Baggage, $i if $p =~ /[47]/aa;
        $Cells{$i} = $p;
    }
    my @game = shrink(@lines);
    my ($w, $h) = (length($game[0]), scalar @game);
    if ($w != $W or $h != $H) {
        $code = join(',', @game);
        init($code);
    }
    %Cg = ();
    foreach my $x (keys %Cells) {
        foreach my $y ($x - 1, $x + 1, $x + $W, $x - $W) {
            push @{ $Cg{$x} }, $y if exists $Cells{$y};
        }
    }
} ## end sub init

sub dummy() {
    my $Zmena   = 0;
    my $pocet   = $#Maze;
    my $man     = $Player;
    my %visited = ($man => 1);
    my @heap    = $man;
    while (@heap) {
        my $x = shift @heap;
        foreach my $t ($x - 1, $x + 1, $x + $W, $x - $W) {
            next if ($t < 0 or $t > $pocet);
            next if $Maze[$t] == 9;
            next if $visited{$t}++;
            push @heap, $t;
        }
    }
    foreach my $i (0 .. $#Maze) {
        next if $Maze[$i] == 9;
        unless (exists $visited{$i}) {
            $Maze[$i] = 9;
            $Zmena = 1;
        }
    }
    if ($Zmena) {
        my $data = join('', @Maze);
        $data = join(',', unpack("(a$W)*", $data));
        init($data);
        dummy();
    }
} ## end sub dummy

sub rohy() {
    $Zmena = 0;
    foreach my $x (sort {$a <=> $b} @Goal) {
        next unless $Cells{$x} == 7;
        if ($Maze[$x - 1] == 9 and ($Maze[$x + $W] == 9 or $Maze[$x - $W] == 9)) {
            $Maze[$x] = 9;
            $Zmena = 1;
        }
        elsif ($Maze[$x + 1] == 9 and ($Maze[$x + $W] == 9 or $Maze[$x - $W] == 9)) {
            $Maze[$x] = 9;
            $Zmena = 1;
        }
    }
    if ($Zmena) {
        my $code = join(',', unpack("(a$W)*", join('', @Maze)));
        init($code);
        dummy();
        rohy();
    }
} ## end sub rohy

sub find_avoid {
    my ($pos, @buf);
    %Avoid = ();
    my @goal = ();
    foreach my $x (keys %Cells) {
        if ($Cells{$x} =~ /[378]/aa) {
            push @goal, $x;
        }
        else {
            $Avoid{$x} = 1;
        }
    }
    foreach my $g (@goal) {
        $buf[0] = $g;
        my (%visited) = ($g, 1);
        my ($bt)      = 1;
        for (my $bh = 0; $bh < $bt; ++$bh) {
            $pos = $buf[$bh];
            delete $Avoid{$pos};
            foreach my $next (@{ $Cg{$pos}; }) {
                my $s = $next * 2 - $pos;
                next unless exists $Cells{$s};
                next if $visited{$next}++;
                $buf[$bt++] = $next;
            }
        }
    } ## end foreach my $g (@goal)
    if (%Avoid) {
        foreach $_ (keys %Avoid) {
            $Maze[$_] =~ tr/05/26/;
        }
    }
    $Code = join(',', unpack("(a$W)*", join('', @Maze)));
} ## end sub find_avoid

sub holes() {
    @Holes = ();
    $Zmena = 0;
CELL: foreach my $x (sort {$a <=> $b} keys %Cells) {
        if ($Maze[$x - $W] == 9 and $Maze[$x - 1] == 9 and $Maze[$x + 1] == 9) {
            my $smer = 'd';
            my @hole = $x;
            my $y    = $x + $W;
            while ($Maze[$y + 1] == 9 and $Maze[$y - 1] == 9) {
                last if $Maze[$y] == 9;
                push @hole, $y;
                $y += $W;
            }
            unless ($Maze[$y] == 9) {
                push @Holes,
                    {
                        'hole'   => [@hole],
                        'entry'  => $y,
                        'after'  => $y + $W,
                        'sentry' => $Maze[$y],
                        'safter', $Maze[$y + $W],
                        'ostr' => join('', @Maze[@hole]),
                        'smer' => $smer
                    };
            }
        } ## end if ($Maze[$x - $W] == ...)
        if ($Maze[$x + $W] == 9 and $Maze[$x - 1] == 9 and $Maze[$x + 1] == 9) {
            my $smer = 'u';
            my @hole = $x;
            my $y    = $x - $W;
            while ($Maze[$y + 1] == 9 and $Maze[$y - 1] == 9) {
                last if $Maze[$y] == 9;
                push @hole, $y;
                $y -= $W;
            }
            unless ($Maze[$y] == 9) {
                push @Holes,
                    {
                        'hole'   => [@hole],
                        'entry'  => $y,
                        'after'  => $y - $W,
                        'sentry' => $Maze[$y],
                        'safter', $Maze[$y - $W],
                        'ostr' => join('', @Maze[@hole]),
                        'smer' => $smer
                    };
            }
        } ## end if ($Maze[$x + $W] == ...)
        if ($Maze[$x - 1] == 9 and $Maze[$x - $W] == 9 and $Maze[$x + $W] == 9) {
            my $smer = 'r';
            my @hole = $x;
            my $y    = $x + 1;
            while ($Maze[$y + $W] == 9 and $Maze[$y - $W] == 9) {
                last if $Maze[$y] == 9;
                push @hole, $y;
                $y += 1;
            }
            unless ($Maze[$y] == 9) {
                push @Holes,
                    {
                        'hole'   => [@hole],
                        'entry'  => $y,
                        'after'  => $y + 1,
                        'sentry' => $Maze[$y],
                        'safter', $Maze[$y + 1],
                        'ostr' => join('', @Maze[@hole]),
                        'smer' => $smer
                    };
            }
        } ## end if ($Maze[$x - 1] == 9...)
        if ($Maze[$x + 1] == 9 and $Maze[$x - $W] == 9 and $Maze[$x + $W] == 9) {
            my $smer = 'l';
            my @hole = $x;
            my $y    = $x - 1;
            while ($Maze[$y + $W] == 9 and $Maze[$y - $W] == 9) {
                last if $Maze[$y] == 9;
                push @hole, $y;
                $y -= 1;
            }
            unless ($Maze[$y] == 9) {
                push @Holes,
                    {
                        'hole'   => [@hole],
                        'entry'  => $y,
                        'after'  => $y - 1,
                        'sentry' => $Maze[$y],
                        'safter', $Maze[$y - 1],
                        'ostr' => join('', @Maze[@hole]),
                        'smer' => $smer
                    };
            }
        } ## end if ($Maze[$x + 1] == 9...)
    } ## end foreach my $x (sort {$a <=>...})
    if (@Holes) {
    HOLE: foreach my $h (@Holes) {
            my $ostr = $h->{'ostr'};
            my $key  = sprintf "%s %s%s", $ostr, $h->{'sentry'}, $h->{'safter'};
            next if $ostr eq '8';
            if (exists $Hole_templates{$key}) {
                apply($key, $h);
                $Zmena = 1;
                last HOLE;
            }
            if ($ostr =~ /^2[02]*/aa) {
                foreach my $x (@{ $h->{'hole'} }) {
                    last if $Maze[$x] != 2 and $Maze[$x] != 0;
                    $Maze[$x] = 9;
                    $Zmena = 1;
                }
                last HOLE if $Zmena;
            }
            elsif ($ostr =~ /^[38][038]*$/aa) {
                next HOLE if length $ostr < 5;
                $h->{'ostr'} =~ tr/8/3/;
                my $hstr = scalar reverse $h->{'ostr'};
                $RealHole{ $h->{'entry'} }{ $h->{'hole'}[-1] } = [[reverse @{ $h->{'hole'} }], $hstr];
                next HOLE;
            }
            elsif ($key =~ /^3[0347]* [^568].$/aa) {
                next HOLE if length $ostr < 5;
                $h->{'ostr'} =~ tr/47/03/;
                my $hstr = scalar reverse $h->{'ostr'};
                $RealHole{ $h->{'entry'} }{ $h->{'hole'}[-1] } = [[reverse @{ $h->{'hole'} }], $hstr];
                next HOLE;
            }
            elsif ($ostr =~ /^[6][02]*$/aa) {
                $Maze[$_] = 9 foreach (@{ $h->{'hole'} });
                $Zmena = 1;
                my $step = $h->{'smer'} x length($ostr);
                if ($h->{'sentry'} =~ /[023]/aa) {
                    $Maze[$h->{'entry'}] =~ tr/023/568/;
                    $FirstStep .= $step;
                }
                elsif ($h->{'sentry'} =~ /[47]/aa) {
                    if ($h->{'safter'} =~ /[03]/aa) {
                        $Maze[$h->{'entry'}] =~ tr/47/58/;
                        $Maze[$h->{'after'}] =~ tr/03/47/;
                        substr($step, -1, 1) = uc(substr($step, -1, 1));
                        $FirstStep .= $step;
                    }
                    else {
                        _refuse('the player in a dead-end corridor cannot get out: the box at its mouth cannot be pushed', $h);
                    }
                }
                else {
                    _refuse('the player in a dead-end corridor cannot get out', $h);
                }
                last HOLE;
            } ## end elsif ($ostr =~ /^[6][02]*$/aa)
            elsif ($ostr =~ /^6[023]/aa) {
                $Maze[$h->{'hole'}[0]] = 9;
                $Maze[$h->{'hole'}[1]] =~ tr/023/568/;
                $FirstStep .= $h->{'smer'};
                $Zmena = 1;
                last HOLE;
            }
            elsif ($ostr =~ /^6[47][03]/aa) {
                $Maze[$h->{'hole'}[0]] = 9;
                $Maze[$h->{'hole'}[1]] =~ tr/47/58/;
                $Maze[$h->{'hole'}[2]] =~ tr/03/47/;
                $FirstStep .= uc($h->{'smer'});
                $Zmena = 1;
                last HOLE;
            }
            elsif ($ostr eq '64') {
                if ($key =~ /[03]{2}$/aa) {
                    $Maze[$h->{'hole'}[0]] = 9;
                    $Maze[$h->{'hole'}[1]] = 9;
                    $Maze[$h->{'entry'}] =~ tr/03/58/;
                    $Maze[$h->{'after'}] =~ tr/03/47/;
                }
                else {
                    _refuse('the box in front of the player in a dead-end corridor cannot be pushed out', $h);
                }
                $FirstStep .= uc($h->{'smer'}) . uc($h->{'smer'});
                $Zmena = 1;
                last HOLE;
            }
            elsif ($ostr =~ /^8[47][03]*$/aa) {
                if ($key =~ /[03]{2}$/aa) {
                    $Maze[$h->{'hole'}[0]] = 3;
                    $Maze[$h->{'hole'}[1]] =~ tr/47/03/;
                    $Maze[$h->{'entry'}]   =~ tr/03/58/;
                    $Maze[$h->{'after'}]   =~ tr/03/47/;
                }
                else {
                    _refuse('the box in front of the player on a goal in a dead-end corridor cannot be pushed out', $h);
                }
                $FirstStep .= uc($h->{'smer'}) x length($ostr);
                $Zmena = 1;
                last HOLE;
            }
            elsif ($ostr eq '67') {
                if ($key =~ /[03]{2}$/aa) {
                    $Maze[$h->{'hole'}[0]] = 9;
                    $Maze[$h->{'hole'}[1]] = 3;
                    $Maze[$h->{'entry'}] =~ tr/03/58/;
                    $Maze[$h->{'after'}] =~ tr/03/47/;
                    $FirstStep .= uc($h->{'smer'}) . uc($h->{'smer'});
                    $Zmena = 1;
                    last HOLE;
                }
                else {
                    _refuse('the box on a goal in front of the player in a dead-end corridor cannot be pushed out', $h);
                }
            }
            else {
                _refuse("a dead-end corridor the templates do not know: '$key'", $h);
            }
        } ## end HOLE: foreach my $h (@Holes)
        if ($Zmena) {
            %RealHole = ();    # indices are stale after shrink() inside init()
            my $data = join(',', unpack("(a$W)*", join('', @Maze)));
            init($data);
            dummy();
            rohy();
            find_avoid();
            holes();
        }
    } ## end if (@Holes)
} ## end sub holes

sub prepare($code) {
    $code =~ tr/1/9/;
    $FirstStep = '';
    %RealHole  = ();
    init($code);
    dummy();
    rohy();
    find_avoid();
    holes();

    # Final sanity: a valid level must have nbox == ngoal and exactly one player.
    # Guards against a processing fault (a template dropping a goal) silently
    # emitting an unsolvable level -- Code must not let such a level through.
    my $nbox    = scalar @Baggage;
    my $ngoal   = scalar @Goal;
    my $nplayer = (join('', @Maze) =~ tr/568//);
    if ($nbox != $ngoal or $nplayer != 1) {
        _refuse(sprintf('broken level after the reduction: %d boxes, %d goals, %d players', $nbox, $ngoal, $nplayer));
    }
    %Game              = ();
    $Game{'goal'}      = dclone \@Goal;
    $Game{'baggage'}   = dclone \@Baggage;
    $Game{'code'}      = "$Code";
    $Game{'cg'}        = dclone \%Cg;
    $Game{'avoid'}     = dclone \%Avoid;
    $Game{'firststep'} = "$FirstStep";
    $Game{'w'}         = $W;
    $Game{'cells'}     = dclone \%Cells;
    $Game{'has_hole'}  = 0;

    if (%RealHole) {
        $Game{'has_hole'} = 1;
        $Game{'hole'}     = dclone \%RealHole;
    }
    return %Game;
} ## end sub prepare
1;
__END__

=head1 NAME

Games::Sokoban::Solver::Code - reduce a level to what the search needs

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Code ();

    my %game = Games::Sokoban::Solver::Code::prepare($code1);
    # $game{code}       the reduced board, rows of digits joined by commas
    # $game{firststep}  the forced opening, letters to put before any solution
    # $game{goal} $game{baggage} $game{cg} $game{avoid} $game{w} $game{cells}
    # $game{has_hole} $game{hole}

=head1 DESCRIPTION

A level as its author drew it carries things no search should pay for: rows of
wall round the outside, floor the player can never reach, a box standing on a
goal in a corner that can never move again, dead-end corridors with one
entrance whose contents have exactly one way to go. This module takes the
digits of a level (as L<Games::Sokoban::Solver::Level> gives them in its
C<code1>) and reduces it, repeating until nothing changes: the outer walls are
shrunk, unreachable floor is walled, a box on a goal in a corner becomes wall,
the cells from which a box can never reach any goal are marked (digit C<2>; the
player on one is C<6>) so that no engine ever puts a box there, and dead-end
corridors are drained by a table of templates -- the box pushed out, the
player walked out -- with the moves that stand for it written down as the
B<forced opening>.

The forced opening is the key to the result: the engines solve the REDUCED
level, and a solution of it plays on the original level only with the forced
opening's letters in front. The program of this distribution prints that
combination and replays it on the original board before printing.

A dead-end corridor the templates cannot drain, and a reduction that would
leave the numbers of boxes and goals apart, end in a refusal: one sentence
beginning C<REFUSED:>, the board drawn, and the corridor named. The templates
cover every shape the 43 000 levels of the Sokoban project had; a new level can
show a new one.

=head1 FUNCTIONS

=over 4

=item prepare CODE

Takes the digits of a level (rows joined by commas; a C<1> is read as a wall)
and returns the first record of it as a hash: C<code> (the reduced board),
C<firststep> (the forced opening, possibly empty), C<w>, C<goal> and
C<baggage> (array references of cell numbers), C<cg> (the player's walk graph:
cell to the neighbours he can step to), C<avoid> (the cells no box may enter),
C<cells> (every cell that is not a wall, with its digit), C<has_hole> and
C<hole> (the dead-end corridors kept for the engines' macros). Dies with a
sentence beginning C<REFUSED:> when the level cannot be reduced.

=back

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
