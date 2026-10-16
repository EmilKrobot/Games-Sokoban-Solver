package Games::Sokoban::Solver::Munkres;

# assign($matrix) returns the minimum total cost of a 1:1 assignment of rows to
# columns; the matrix must be SQUARE (callers pad with a dummy value).
# assign($matrix, \@out) ALSO reports who was matched to whom: $out[$i] is the
# column assigned to row $i, the same convention as the original
# Algorithm::Munkres. The vector is free -- the solver holds the matching
# anyway. Callers that only want the value pass one argument and see no change.
# The input matrix is never modified.
#
# Beside assign() there is an INCREMENTAL pair, for the caller that asks the
# same assignment over and over with one row replaced -- a scorer ranking
# candidate moves, where the row is the box the move shifts:
#
#     my $ctx = Games::Sokoban::Solver::Munkres::context($base_matrix);
#     my $w   = Games::Sokoban::Solver::Munkres::with_row($ctx, $row, \@new_row);   # repeatable
#
# One augmentation instead of n, the changed row spliced in by reference instead
# of the matrix copied, and the caller NAMES the row instead of the solver
# comparing two matrices to find it. Every candidate is measured against the
# BASE, so the saving does not evaporate when consecutive candidates move
# different boxes. assign() itself is untouched by it, and so is every caller
# of it. Written for Festival's four compute_*_distance scorers, whose own
# Hungarian spent 8-12 % of the search on exactly this shape (measured
# 2026-08-22, of which over half was verify_hungarian_invariant, an assertion).
#
# METHOD: a zero-matching fast path (see below) over a shortest-augmenting-path
# solver with potentials (Jonker-Volgenant form of the Hungarian method) -- one
# augmentation per row, each O(n^2), no rescans of the whole tableau. Together
# they replaced the classic star/prime tableau this module ran from the start.
#
# MEASURED on the matrices the engine really sends (captured from live solves
# by a scratch profiler; sizes n=1..11, which is what the Sokoban project
# produces):
#   PUSH_ASSIGN's cost matrices   2.5x faster  -> 1.50x on the WHOLE engine
#   the filters' 0/BIG matrices   1.25x faster -> 1.01x, i.e. no regression
# The engine gate of the day (old core against new under a POSITION budget, so
# the faster core cannot simply walk further) showed every result unchanged.
#
# The first cut had no fast path and measured 3x SLOWER on the filters even
# while it was 2.3x faster on PUSH_ASSIGN -- the unit benchmark had missed it
# entirely by drawing only cost matrices, which never contain a zero.
#
# ONE behavioural caveat, and it is not a defect: the minimum COST is unique, so
# every caller that reads the return value is unaffected. The MATCHING that
# realises it need not be unique, so on a matrix with ties the vector can name a
# different (equally optimal) partner than the tableau used to. Callers that
# consume the vector can therefore pick a different equally-good option than
# before. That is the same tie-break nondeterminism the Sokoban project treats
# as deliberate elsewhere.
#
# Lineage: Games::Munkres 0.21 of the Sokoban project (2026-08-23).
use v5.42;
our $VERSION = '0.01';

# Rows and columns are numbered from 1 inside, with column 0 as the scratch slot
# the augmenting path starts from -- that is what lets the search run without a
# separate "unmatched" flag array. @u/@v are the row/column potentials, @p is
# column -> row (the matching itself), @way is the alternating tree's back-links.
sub assign ($rmat, $out = undef) {
    my $n = scalar @$rmat;
    @$out = () if $out;    # a reused arrayref must not keep a previous answer
    return 0 unless $n;

    # ZERO-MATCHING FAST PATH. Half of the Sokoban project's assignments are not
    # cost questions at all: the matching-deadlock filters build a 0/$BIG matrix
    # and ask only whether a perfect matching of the ZEROS exists (measured: 89 %
    # of their entries are 0). With every entry non-negative, a perfect matching
    # of zeros costs 0 and is therefore optimal outright -- one greedy O(n^2)
    # sweep settles it, with no potentials and no allocation. This is what the
    # old star/prime tableau got for free from its greedy starring step, and
    # losing it is why the augmenting-path core measured 3x SLOWER on PUSH_SCORE
    # even while it was 2.3x faster on PUSH_ASSIGN (2026-08-17).
    #
    # The sweep aborts the moment a row has no free zero -- greedy failing does
    # not prove there is no perfect zero matching, it just means the general
    # solver below has to answer. A negative entry also aborts it: then zero is
    # not necessarily the minimum and the whole argument collapses.
    # The row is scanned WHOLE even after its zero is found: the non-negativity
    # that licenses the shortcut has to hold for the entries we never pick, too.
FAST: {
        my (@rowof, @colused);
        for my $i (0 .. $n - 1) {
            my $row = $rmat->[$i];
            my $hit = -1;
            for my $j (0 .. $n - 1) {
                my $x = $row->[$j];
                last FAST if $x < 0;
                $hit = $j if $x == 0 && $hit < 0 && !$colused[$j];
            }
            last FAST if $hit < 0;
            $colused[$hit] = 1;
            $rowof[$i]     = $hit;
        }
        @$out = @rowof if $out;
        return 0;
    } ## end FAST:
    my $INF = 9**15;
    my @u   = (0) x ($n + 1);
    my @v   = (0) x ($n + 1);
    my @p   = (0) x ($n + 1);
    my @way = (0) x ($n + 1);
    for my $i (1 .. $n) {
        $p[0] = $i;
        my $j0   = 0;
        my @minv = ($INF) x ($n + 1);
        my @used = (0) x ($n + 1);

        # grow the alternating tree one column at a time, always taking the
        # cheapest reduced-cost edge out of it, until it reaches a free column
        do {
            $used[$j0] = 1;
            my $i0    = $p[$j0];
            my $row   = $rmat->[$i0 - 1];
            my $delta = $INF;
            my $j1    = 0;
            for my $j (1 .. $n) {
                next if $used[$j];
                my $cur = $row->[$j - 1] - $u[$i0] - $v[$j];
                if ($cur < $minv[$j]) {$minv[$j] = $cur; $way[$j] = $j0}
                if ($minv[$j] < $delta) {$delta = $minv[$j]; $j1 = $j}
            }

            # re-potentiate so the chosen edge becomes tight and every edge
            # already in the tree stays tight
            for my $j (0 .. $n) {
                if ($used[$j]) {$u[$p[$j]] += $delta; $v[$j] -= $delta}
                else           {$minv[$j] -= $delta}
            }
            $j0 = $j1;
        } while ($p[$j0] != 0);

        # walk the back-links home, flipping the path: every column on it takes
        # over the row of its predecessor
        do {
            my $j1 = $way[$j0];
            $p[$j0] = $p[$j1];
            $j0 = $j1;
        } while ($j0);
    } ## end for my $i (1 .. $n)
    my $value = 0;
    for my $j (1 .. $n) {
        my $i = $p[$j];
        $value += $rmat->[$i - 1][$j - 1];
        $out->[$i - 1] = $j - 1 if $out;    # row -> column, the documented direction
    }
    return $value;
} ## end sub assign

# ===========================================================================
# ONE ROW AT A TIME: the same problem asked again with a single row replaced
# ===========================================================================
#
# WHY THIS EXISTS. A scorer that asks "how good is each candidate move" solves
# the SAME assignment over and over, each time with exactly one row different:
# the row of the box the move shifts. Festival's own Hungarian carries machinery
# for that (a kept previous solution, and did_one_row_change to discover which
# row moved), and this module had none -- so it could serve Festival's
# check_matching_deadlock, where every call is a fresh feasibility question, but
# not its four per-move scorers.
#
# The version here is cheaper than the one it replaces, for two reasons that are
# about the INTERFACE rather than the algorithm:
#
#   * The caller SAYS which row changed. It always knew -- it wrote that row
#     itself a moment earlier. Festival spends an O(n^2) matrix comparison
#     rediscovering it (did_one_row_change), measured at 1.2-1.7 % of the search.
#   * Nothing copies the matrix. The changed row is spliced in as a REFERENCE
#     over the base rows, so the per-call cost is n pointer copies, not n^2
#     number copies. Festival rebuilds the whole matrix per candidate move.
#
# And every candidate is measured against the BASE, not against whichever
# candidate happened to come before it. That is the other half of Festival's
# problem: its kept solution is the last one solved, so two consecutive
# candidates differ in TWO rows (the previous move's row put back, the new one
# written) and its warm start falls through to a full solve whenever the moving
# box changes.
#
# THE METHOD. The solver keeps a dual-feasible potential (u on rows, v on
# columns, with u[i] + v[j] <= c[i][j] everywhere) and a matching whose edges are
# all tight. Replacing row r can only break feasibility in row r, so:
#
#   u[r] := min_j (c[r][j] - v[j])    -- feasible again, and row r's old edge
#   free the column that held row r      is dropped rather than repaired
#   one augmentation from row r          -- O(n^2), not the O(n^3) of a re-solve
#
# Every other row keeps its costs, its potential and its tight matched edge, so
# the partial matching stays optimal for the rows it covers; one augmenting path
# completes it. The result is the exact minimum, not an approximation of it.
# Build a reusable context from the base matrix: it solves it once and keeps
# the potentials and the matching. The matrix is held by reference and must not
# be modified by the caller afterwards -- with_row reads it for every row but r.
sub context ($rmat) {
    my $n = scalar @$rmat;
    my $c = { 'n' => $n, 'rows' => $rmat, 'u' => [], 'v' => [], 'p' => [], 'weight' => 0 };
    return $c unless $n;
    my @out;
    $c->{'weight'} = assign($rmat, \@out);

    # assign() does not hand its potentials back (its callers only ever wanted
    # the value), so they are rebuilt here from the matching it found. For the
    # zero-matching fast path that is exact and free: with every entry
    # non-negative and every matched edge costing 0, u = v = 0 is dual-feasible
    # and those edges are tight. Otherwise the base is solved again here, once,
    # keeping the state -- the cost of building a context, paid one time against
    # however many rows are then tried against it.
    my $zero = 1;
    for my $i (0 .. $n - 1) {
        $zero = 0, last if $rmat->[$i][$out[$i]] != 0;
    }
    if ($zero) {
        $c->{'u'}               = [(0) x ($n + 1)];
        $c->{'v'}               = [(0) x ($n + 1)];
        $c->{'p'}               = [(0) x ($n + 1)];
        $c->{'p'}[$out[$_] + 1] = $_ + 1 for 0 .. $n - 1;
        return $c;
    }
    (my $w, $c->{'u'}, $c->{'v'}, $c->{'p'}) = _solve_keeping_state($rmat, $n);
    $c->{'weight'} = $w;
    return $c;
} ## end sub context

# The base solve, in the form that keeps (u, v, p) instead of throwing them
# away. Same augmenting-path core as assign(); factored out rather than shared
# so assign() itself stays exactly as it was and as fast as it was.
sub _solve_keeping_state ($rows, $n) {
    my $INF = 9**15;
    my @u   = (0) x ($n + 1);
    my @v   = (0) x ($n + 1);
    my @p   = (0) x ($n + 1);
    my @way = (0) x ($n + 1);
    for my $i (1 .. $n) {
        _augment($rows, $n, \@u, \@v, \@p, \@way, $i, $INF);
    }
    my $value = 0;
    $value += $rows->[$p[$_] - 1][$_ - 1] for 1 .. $n;
    return ($value, \@u, \@v, \@p);
}

# One augmentation: bring row $i into the matching, growing the alternating
# tree from the scratch column 0 and re-potentiating so the chosen edge is
# always tight. This is the body assign() runs once per row.
sub _augment ($rows, $n, $u, $v, $p, $way, $i, $INF) {
    $p->[0] = $i;
    my $j0   = 0;
    my @minv = ($INF) x ($n + 1);
    my @used = (0) x ($n + 1);
    do {
        $used[$j0] = 1;
        my $i0    = $p->[$j0];
        my $row   = $rows->[$i0 - 1];
        my $delta = $INF;
        my $j1    = 0;
        for my $j (1 .. $n) {
            next if $used[$j];
            my $cur = $row->[$j - 1] - $u->[$i0] - $v->[$j];
            if ($cur < $minv[$j]) {$minv[$j] = $cur; $way->[$j] = $j0}
            if ($minv[$j] < $delta) {$delta = $minv[$j]; $j1 = $j}
        }
        for my $j (0 .. $n) {
            if ($used[$j]) {$u->[$p->[$j]] += $delta; $v->[$j] -= $delta}
            else           {$minv[$j] -= $delta}
        }
        $j0 = $j1;
    } while ($p->[$j0] != 0);
    do {
        my $j1 = $way->[$j0];
        $p->[$j0] = $p->[$j1];
        $j0 = $j1;
    } while ($j0);
    return;
} ## end sub _augment

# The minimum cost of the base problem with row $r (0-based) replaced by
# $newrow. The context is NOT modified, so the same context serves any number of
# candidate rows, each measured against the base.
sub with_row ($c, $r, $newrow, $out = undef) {
    my $n = $c->{'n'};
    @$out = () if $out;
    return 0 unless $n;

    # the changed row spliced in by reference: n pointer copies, not n*n numbers
    my @rows = @{ $c->{'rows'} };
    $rows[$r] = $newrow;
    my @u   = @{ $c->{'u'} };
    my @v   = @{ $c->{'v'} };
    my @p   = @{ $c->{'p'} };
    my @way = (0) x ($n + 1);
    my $INF = 9**15;

    # row r is the only one whose costs moved, so it is the only one whose
    # potential can have become infeasible -- push it back down to the tightest
    # value the column potentials still allow
    my $min = $INF;
    for my $j (1 .. $n) {
        my $cur = $newrow->[$j - 1] - $v[$j];
        $min = $cur if $cur < $min;
    }
    $u[$r + 1] = $min;

    # drop row r's old edge; its column becomes the free one the augmentation
    # will fill
    for my $j (1 .. $n) {
        if ($p[$j] == $r + 1) {$p[$j] = 0; last}
    }
    _augment(\@rows, $n, \@u, \@v, \@p, \@way, $r + 1, $INF);
    my $value = 0;
    for my $j (1 .. $n) {
        my $i = $p[$j];
        $value += $rows[$i - 1][$j - 1];
        $out->[$i - 1] = $j - 1 if $out;
    }
    return $value;
} ## end sub with_row
1;
__END__

=head1 NAME

Games::Sokoban::Solver::Munkres - the minimum-cost assignment of boxes to goals

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Munkres ();

    my $cost = Games::Sokoban::Solver::Munkres::assign(\@matrix);
    my $cost = Games::Sokoban::Solver::Munkres::assign(\@matrix, \my @column_of_row);

    my $ctx  = Games::Sokoban::Solver::Munkres::context(\@matrix);
    my $cost = Games::Sokoban::Solver::Munkres::with_row($ctx, $row, \@new_row);

=head1 DESCRIPTION

Given a square matrix of costs -- a row per box, a column per goal, the cost of
sending that box to that goal -- the Hungarian method finds the assignment of
every box to its own goal whose total cost is the least. The solvers of this
distribution use it in two shapes: as a score (how far are the boxes from the
goals, if each takes the goal that suits the whole best), and as a yes-or-no
question (is there any way at all to give every box a goal it can reach,
asked over a matrix of zeros and one huge number).

The method here is the shortest-augmenting-path form of the Hungarian
algorithm with potentials, one augmentation per row, with a greedy fast path
for the matrix of zeros that answers the yes-or-no question without any of
it. Beside the plain C<assign> there is an incremental pair for a caller that
asks the same problem again and again with one row changed: C<context> solves
the base once and keeps its potentials, C<with_row> measures a replaced row
against it in one augmentation.

The minimum cost is unique. The matching that realises it need not be, so on
ties the reported partner of a row may differ from one run to another.

=head1 FUNCTIONS

=over 4

=item assign MATRIX, [OUT]

The minimum total cost of a one-to-one assignment of the rows of the square
MATRIX (an array of arrays of numbers) to its columns. With an array
reference OUT, C<$out[$i]> is set to the column assigned to row C<$i>. The
matrix is not modified. An empty matrix costs 0.

=item context MATRIX

A context for C<with_row>: the base matrix solved once, with its potentials
and matching kept. The matrix is held by reference and must not be modified
afterwards.

=item with_row CONTEXT, ROW, NEWROW, [OUT]

The minimum cost of the base problem with row ROW (counted from 0) replaced by
the array reference NEWROW, as C<assign> would compute it, in one augmentation
instead of a full solve. The context is not modified, so any number of
candidate rows can be measured against the same base.

=back

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
