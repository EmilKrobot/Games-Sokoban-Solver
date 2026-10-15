package Games::Sokoban::Solver::Data;

# The data tables of the distribution, found beside this module.
#
# Four tables travel with the modules: the dead-end corridor templates Code
# applies, the hole and corridor deadlock patterns the first-solution engines
# test moves against, and the Festival engine's library of deadlock patterns.
# Each is a Storable file in network byte order under lib/Games/Sokoban/Solver/
# Data/, so it is installed wherever the modules are installed and found from
# here by the location of this very file -- no share directory, no
# configuration, no current working directory.

use v5.42;
use Carp           ();
use File::Basename ();
use Storable       ();

our $VERSION = '0.01';

my $DIR = File::Basename::dirname(__FILE__) . '/Data';

sub path ($name) {
    return "$DIR/$name";
}

sub load ($name) {
    my $file = path($name);
    Carp::croak("Games::Sokoban::Solver::Data: no table $file") unless -f $file;
    return Storable::retrieve($file);
}

1;

__END__

=head1 NAME

Games::Sokoban::Solver::Data - the data tables of the distribution

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Data ();

    my $holes = Games::Sokoban::Solver::Data::load('hole_pattern.stor');
    my $file  = Games::Sokoban::Solver::Data::path('fest_patterns.stor');

=head1 DESCRIPTION

Four tables travel with the modules of this distribution, each a L<Storable>
file in network byte order in the directory F<Data/> beside this module:

=over 4

=item F<hole_templates.stor>

The dead-end corridor templates that L<Games::Sokoban::Solver::Code> applies
when it reduces a level: how a corridor with one entrance is drained of its
boxes and goals before the search, and the forced moves that stand for it.

=item F<hole_pattern.stor>, F<corridor_pattern.stor>

The deadlock patterns of a hole (a one-entrance corridor) and of a corridor
with goals, tested by the first-solution engines against every move that puts
a box into one.

=item F<fest_patterns.stor>

The Festival engine's library of 116 push patterns and 60 pull patterns, as
the C original carries them.

=back

The files are found by the location of this module, so they work from the
distribution's own F<lib/>, from F<blib/> while building, and from the
installed library alike.

=head1 FUNCTIONS

=over 4

=item path NAME

The full path of the table NAME.

=item load NAME

The table NAME, read with L<Storable/retrieve>. Dies naming the file when it
does not exist or cannot be read.

=back

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
