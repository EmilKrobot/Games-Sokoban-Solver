# Heap: the smallest weight first, always; Munkres: the minimum against brute
# force, in every shape the engines send, and the incremental pair against a
# fresh solve.
use v5.42;
use Test::More;
use Games::Sokoban::Solver::Heap ();
use Games::Sokoban::Solver::Munkres ();

srand(20261015);    # the same random matrices every run: a failure is reproducible

# ---- Heap ----------------------------------------------------------------
{
    my $q = Games::Sokoban::Solver::Heap->new;
    is($q->size, 0, 'a new queue is empty');
    is_deeply([$q->next], [], 'next on an empty queue returns nothing');
    is_deeply([$q->peek], [], 'peek on an empty queue returns nothing');

    my @weights = map { int(rand 50) } 1 .. 200;
    $q->add("item $_", $weights[$_]) for 0 .. $#weights;
    is($q->size, 200, '200 items queued');
    my ($min) = sort { $a <=> $b } @weights;
    like($q->peek, qr/\Aitem \d+\z/, 'peek returns an item');
    is($weights[ ($q->peek =~ /(\d+)/)[0] ], $min, 'peek returns an item of the smallest weight');
    is($q->size, 200, 'peek takes nothing out');

    my $last = -1;
    my $ok   = 1;
    while (my ($item) = $q->next) {
        my $w = $weights[ ($item =~ /(\d+)/)[0] ];
        $ok = 0 if $w < $last;
        $last = $w;
    }
    ok($ok, 'next serves the weights in non-decreasing order');
    is($q->size, 0, 'the queue is empty again');
}

# ---- Munkres: brute force over every permutation ---------------------------
sub permutations ($n) {
    return ([]) if $n == 0;
    my @out;
    for my $p (permutations($n - 1)) {
        for my $at (0 .. $n - 1) {
            my @q = @$p;
            splice @q, $at, 0, $n - 1;
            push @out, \@q;
        }
    }
    return @out;
}

my %perms = map { $_ => [permutations($_)] } 1 .. 6;

sub brute ($m) {
    my $n = scalar @$m;
    return 0 unless $n;
    my $best;
    for my $p (@{ $perms{$n} }) {
        my $cost = 0;
        $cost += $m->[$_][ $p->[$_] ] for 0 .. $n - 1;
        $best = $cost if !defined $best or $cost < $best;
    }
    return $best;
}

sub random_matrix ($n, $pick) {
    return [map { [map { $pick->() } 1 .. $n] } 1 .. $n];
}

is(Games::Sokoban::Solver::Munkres::assign([]), 0, 'an empty matrix costs 0');

my $BIG = 10**9;
my %shape = (
    'cost matrices 0..9'           => sub { int(rand 10) },
    'the filters: zeros and BIG'   => sub { rand() < 0.89 ? 0 : $BIG },
    'mixed small and large values' => sub { rand() < 0.5 ? int(rand 5) : 1000 + int(rand 1000) },
);
for my $name (sort keys %shape) {
    my ($bad, $badout) = (0, 0);
    for my $trial (1 .. 100) {
        my $n = 1 + int(rand 6);
        my $m = random_matrix($n, $shape{$name});
        my @out;
        my $got = Games::Sokoban::Solver::Munkres::assign($m, \@out);
        ++$bad unless $got == brute($m);

        # the reported matching is a permutation and realises the reported cost
        my %col  = map { $_ => 1 } @out;
        my $cost = 0;
        $cost += $m->[$_][ $out[$_] ] for 0 .. $n - 1;
        ++$badout unless @out == $n and keys %col == $n and $cost == $got;
    }
    is($bad,    0, "$name: the minimum equals brute force in 100 random matrices");
    is($badout, 0, "$name: the reported matching is a permutation realising the minimum");
}

# ---- Munkres: with_row against a fresh assign --------------------------------
{
    my $bad = 0;
    for my $trial (1 .. 300) {
        my $n    = 1 + int(rand 6);
        my $pick = rand() < 0.5 ? sub { int(rand 10) } : sub { rand() < 0.8 ? 0 : $BIG };
        my $m    = random_matrix($n, $pick);
        my $ctx  = Games::Sokoban::Solver::Munkres::context($m);
        my $r    = int(rand $n);
        my $row  = [map { $pick->() } 1 .. $n];
        my @fresh = map { [@$_] } @$m;
        $fresh[$r] = $row;
        my $want = Games::Sokoban::Solver::Munkres::assign(\@fresh);
        my @out;
        my $got = Games::Sokoban::Solver::Munkres::with_row($ctx, $r, $row, \@out);
        my $cost = 0;
        $cost += $fresh[$_][ $out[$_] ] for 0 .. $n - 1;
        ++$bad unless $got == $want and $cost == $got;
    }
    is($bad, 0, 'with_row equals a fresh assign on the changed matrix in 300 trials, and its matching realises the cost');
}

done_testing;
