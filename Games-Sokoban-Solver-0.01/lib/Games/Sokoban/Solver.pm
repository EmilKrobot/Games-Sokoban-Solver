package Games::Sokoban::Solver;

use v5.42;

our $VERSION = '0.01';

1;

__END__

=head1 NAME

Games::Sokoban::Solver - solve Sokoban levels: a first solution by a race of search modes, then the shortest one

=head1 SYNOPSIS

    use Games::Sokoban::Solver ();

    my @levels = Games::Sokoban::Solver::read_levels($xsb_text);
    my $result = Games::Sokoban::Solver::solve_level(rows => $levels[0]{'rows'});
    say $result->{'path'};    # the solution in uUrRlLdD letters, or UNSOLVED

From the command line:

    soko-solver.pl levels.xsb

=head1 DESCRIPTION

This distribution is the solver pipeline of the Sokoban project of Jiri Broz,
packaged for use outside that project: a level in the standard text format is
read, reduced to what matters for the search, analysed, and then solved twice --
first by a race of twenty-seven search modes of four engines, the first to find
a solution winning, then by an optimal solver that looks for the shortest
solution and, where it can, proves it.

The modules of the distribution are being transplanted one by one; this
document grows with them.  Until the facade exists, the distribution installs
and tests but solves nothing yet.

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
