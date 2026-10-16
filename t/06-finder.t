# Finder: the subsets iterator, a push dead by itself, the bloks of a pattern
# (against the strings the Sokoban project's pattern database holds for the
# same windows), the resume form, the deadline, and a level's table.
use v5.42;
use Test::More;
use Time::HiRes                    ();
use Games::Sokoban::Solver::Finder ();
my $F = 'Games::Sokoban::Solver::Finder';

# ---- _combinations ----------------------------------------------------------
{
    my $it = Games::Sokoban::Solver::Finder::_combinations([10, 20, 30, 40], 2);
    my @all;
    while (my $c = $it->()) {push @all, join(',', @$c)}
    is_deeply(\@all, ['10,20', '10,30', '10,40', '20,30', '20,40', '30,40'], 'the 6 pairs of 4, in index order');
    is($it->(), undef, 'and undef for good afterwards');
    $it = Games::Sokoban::Solver::Finder::_combinations([1, 2, 3], 3);
    is_deeply($it->(), [1, 2, 3], 'k = n: the one set');
    is($it->(),                                                      undef, 'then nothing');
    is(Games::Sokoban::Solver::Finder::_combinations([1, 2], 3)->(), undef, 'k > n: nothing at all');
    is_deeply(Games::Sokoban::Solver::Finder::_combinations([1, 2], 0)->(), [], 'k = 0: the empty set once');
}

# ---- pat_soluble ---------------------------------------------------------------
# The window: 5 wide, 6 tall, the pushed box at index 22 (fifth row, third
# column), the player below it at 27.
sub window (%cell) {
    my $p = '0' x 30;
    substr($p, $_, 1) = $cell{$_} for keys %cell;
    return $p;
}
ok($F->can('pat_soluble')->(window(22 => '4', 27 => '5')), 'open floor: the box leaves the window');
ok(
    !$F->can('pat_soluble')->(window(17 => '9', 21 => '9', 23 => '9', 22 => '4', 27 => '5')),
    'walls above, left and right of the box, the player below: dead by itself'
  );
ok($F->can('pat_soluble')->(window(17 => '9', 21 => '9', 23 => '9', 22 => '7', 27 => '5')),
    'the same box on a goal: not a deadlock');
ok($F->can('pat_soluble')->(window(16 => '9', 17 => '3', 21 => '9', 23 => '9', 22 => '4', 27 => '5', 12 => '9')),
    'a goal above the box, the row behind it walled: the one push onto the goal solves it');

# ---- blok_task against the project's pattern database --------------------------
# Five windows and the blok strings Patterns.sqlite3 holds for them, complete to
# the size 'lim' of each; every set is cells of the window (0-29).
my @stored = (
    ['000000990929909992299949999599', 2, '8;13;2,3;3,4'],
    ['000002299099922999290042999599', 2, '20;21'],
    ['000002999099992922299240099599', 3, '23;24'],
    ['000000002929999992292942929529', 3, ''],
    ['999999992299209990099970999803', 6, '17;13,23'],
    ['999999992299909299000040099500', 5, '20;21;18,23;13,19,23;18,24,28,29;13,19,24,28,29'],
    ['000000000000000099990043300500', 6, '21;23;20,25,26;24,28,29'],
);
for my $s (@stored) {
    my ($pattern, $lim, $blok) = @$s;
    my $r = Games::Sokoban::Solver::Finder::blok_task($pattern, $lim, 1, '');
    is($r->[0], $pattern, "$pattern: the row names its pattern");
    is($r->[1], $lim,     "$pattern: every size to $lim finished");
    is($r->[2], $blok,    "$pattern: the bloks of the database");
    ok($r->[3] > 0 && $r->[4] >= 0, "$pattern: candidates counted, time taken");
}

# The resume form: sizes 1..2, then 3..lim from the string so far, equals one run.
{
    my ($pattern, $lim, $blok) = @{ $stored[5] };
    my $a = Games::Sokoban::Solver::Finder::blok_task($pattern, 2,    1, '');
    my $b = Games::Sokoban::Solver::Finder::blok_task($pattern, $lim, 3, $a->[2]);
    is($b->[1], $lim,  'the second task finished the sizes left');
    is($b->[2], $blok, 'two tasks in a row give what one gives');
    is(Games::Sokoban::Solver::Finder::blok_task($pattern, 2, 1, '')->[2],
        '20;21;18,23', 'the first task holds the small sets only');
}

# ---- the deadline --------------------------------------------------------------------
{
    my ($pattern, $lim, $blok) = @{ $stored[6] };    # 24 free cells, about a second
    my %full = map {$_ => 1} split /;/, $blok;
    my $r    = Games::Sokoban::Solver::Finder::blok_task($pattern, $lim, 1, '', Time::HiRes::time() - 1);
    is($r->[1], 0,  'a deadline already past: no size finished');
    is($r->[2], '', 'and no blok recorded');
    $r = Games::Sokoban::Solver::Finder::blok_task($pattern, $lim, 1, '', Time::HiRes::time() + 0.05);
    cmp_ok($r->[1], '<', $lim, 'a short deadline cuts the pattern before its last size');
    my @extra = grep {!$full{$_}} split /;/, $r->[2];
    is_deeply(\@extra, [], 'every set found under the cut is a set of the complete table');
}

# ---- blok_table ---------------------------------------------------------------------
{
    my %patlist = map {$_->[0] => 1} @stored;
    my ($bloks, $report) = Games::Sokoban::Solver::Finder::blok_table(\%patlist, 'nbox' => 3);
    is(scalar keys %$bloks,       scalar @stored, 'one string per pattern');
    is(scalar @$report,           scalar @stored, 'one report row per pattern');
    is($bloks->{ $stored[6][0] }, '21;23',        'with 3 boxes only sets of 1 and 2 are asked for');
    is($bloks->{ $stored[0][0] }, '8;13;2,3;3,4', 'a pattern complete at size 2 is complete here');
    is_deeply([map {$_->[1]} @$report], [(2) x 7], 'kmax = nbox - 1 everywhere (every window has more free cells)');
    is_deeply([map {$_->[2]} @$report], [(2) x 7], 'and every pattern finished');
    ok(!exists $bloks->{'no such pattern'}, 'nothing invented');
    ($bloks, $report) = Games::Sokoban::Solver::Finder::blok_table({ $stored[6][0] => 1 }, 'nbox' => 7);
    is($bloks->{ $stored[6][0] }, $stored[6][2], 'with 7 boxes the table of sizes 1..6, in two passes, equals the one task');
    is($report->[0][2],           6,             'k_done 6');
    ($bloks, $report) =
        Games::Sokoban::Solver::Finder::blok_table({ $stored[6][0] => 1 }, 'nbox' => 7, 'kmax_of' => { $stored[6][0] => 2 });
    is($bloks->{ $stored[6][0] }, '21;23', 'kmax_of overrides');
    ($bloks, $report) = Games::Sokoban::Solver::Finder::blok_table(\%patlist, 'nbox' => 7, 'deadline' => Time::HiRes::time() - 1);
    is_deeply([map {$_->[2]} @$report], [(0) x 7],  'a deadline past: nothing done ...');
    is_deeply([values %$bloks],         [('') x 7], '... and every string empty, none missing');
    my $ok = eval {Games::Sokoban::Solver::Finder::blok_table(\%patlist); 1};
    like($@, qr/nbox is needed/, 'nbox is required');
}
done_testing;
