package Games::Sokoban::Solver::Heap;

# The priority queue of the first-solution engines: positions queued with a
# weight, the smallest weight served first. A thin object over Array::Heap,
# whose heap operations are in C -- the queue is on the hot path of every
# forward search, and a pure-Perl heap would change the order among equal
# weights (which the engines are sensitive to) as well as the speed.
#
# Only what the engines call is here: new, add, next, peek, size.
#
# Lineage: Games::Numeric 2.11 (Pex) of the Sokoban project.

use v5.42;
use Array::Heap ('pop_heap', 'push_heap');

our $VERSION = '0.01';

sub new ($class) {
    return bless([], $class);
}

sub add ($self, $item, $weight) {
    &push_heap(\@$self, [$weight, $item]);
}

sub peek ($self) {
    return unless my $node = $self->[0];
    return ref $node ? $node->[1] : $node;
}

sub next ($self) {
    return unless my $node = &pop_heap(\@$self);
    return $node->[1];
}

sub size ($self) {
    return scalar @$self;
}

1;

__END__

=head1 NAME

Games::Sokoban::Solver::Heap - the priority queue of the first-solution engines

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Heap ();

    my $queue = Games::Sokoban::Solver::Heap->new;
    $queue->add($position, $score);      # queued with its weight
    my $best = $queue->peek;             # the item of the smallest weight, left in place
    my $next = $queue->next;             # ... taken out
    my $n    = $queue->size;

=head1 DESCRIPTION

A queue of items with weights, serving the smallest weight first, built on
L<Array::Heap>'s binary heap in C. The first-solution engines queue every
position they generate with its score and expand the best-scored one next;
that queue is on the hottest path of the search, which is why the heap is the
one prerequisite of this distribution outside the perl core.

Among equal weights the order is the heap's own, and the engines are sensitive
to it: a different heap would walk a different search.

=head1 METHODS

=over 4

=item new

An empty queue.

=item add ITEM, WEIGHT

Queue ITEM with WEIGHT.

=item peek

The item of the smallest weight, left in the queue; nothing when the queue is
empty.

=item next

The item of the smallest weight, taken out; nothing when the queue is empty.

=item size

How many items are queued.

=back

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
