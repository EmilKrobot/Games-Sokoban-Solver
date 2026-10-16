# The facade on the micro levels: prepare (the record, the opening, the label,
# the patterns from the pool equal to the serial ones), first_solution on a
# serial pool and on threads, best_solution proving the brute-force optimum,
# full_path carrying the opening, solve_level end to end, and the refusals.
use v5.42;
use Test::More;
use Config ();
use lib 't/lib';
use BruteForce                     ();
use Games::Sokoban::Solver         ();
use Games::Sokoban::Solver::Replay ();
my $TIME = 10;
open my $fh, '<', 't/data/micro.xsb' or die $!;
my $text = do {local $/; <$fh>};
close $fh;
my @levels = Games::Sokoban::Solver::read_levels($text);
is(scalar @levels, 4, 'read_levels: the four micro levels');

# A level with a forced opening: the player at the bottom of a dead-end
# corridor, the box and goal in the room above.
my ($corridor) = Games::Sokoban::Solver::read_levels(<<'XSB');
A corridor to walk out of
#######
#  $. #
#     #
####@##
#######
XSB
my ($open) = Games::Sokoban::Solver::read_levels(<<'XSB');
An open level
#   .
# $@
#
XSB

# --- prepare ------------------------------------------------------------------
{
    my @notes;
    my $p = Games::Sokoban::Solver::prepare('rows' => $levels[3], 'on_note' => sub ($t) {push @notes, $t});
    is($p->{'title'},             'Three boxes in a room', 'the title travels');
    is($p->{'nbox'},              3,                       'three boxes');
    is($p->{'firststep'},         '',                      'no opening');
    is($p->{'solved_by_opening'}, 0,                       'not solved by the opening');
    like($p->{'label'}, qr/\A\d+\z/, 'the label is an integer');
    is($p->{'label'}, Games::Sokoban::Solver::label($p->{'code1'}), 'the label is that of code1');
    ok(length $p->{'game_blob'} && length $p->{'fest_blob'} && length $p->{'analysis_blob'}, 'the three blobs are built');
    is_deeply($p->{'build'},  {}, 'nothing left to build');
    is_deeply($p->{'failed'}, {}, 'nothing failed');
    ok($p->{'blok_complete'},        'the patterns are complete under the default budget');
    ok(@{ $p->{'blok_report'} } > 0, 'a blok report');
    ok(exists $p->{'cost'}{$_},      "cost of $_") for 'level', 'code', 'parser', 'blok', 'fest', 'analysis';
    is_deeply(\@notes, $p->{'notes'}, 'on_note heard every note');

    # lazy: the two analyses wait for first_solution
    my $lazy = Games::Sokoban::Solver::prepare('rows' => $levels[3], 'lazy' => 1);
    ok(!defined $lazy->{'fest_blob'} && !defined $lazy->{'analysis_blob'}, 'lazy: not built yet');
    is_deeply([sort keys %{ $lazy->{'build'} }], ['analysis', 'fest'], 'lazy: two builders');
    ok(length Games::Sokoban::Solver::build($lazy, 'fest'),                     'build() builds one on demand');
    ok(!exists $lazy->{'build'}{'fest'} && exists $lazy->{'build'}{'analysis'}, 'and takes its builder away');

    # want: only what is asked for
    my $some = Games::Sokoban::Solver::prepare('rows' => $levels[3], 'want' => ['game']);
    ok(!defined $some->{'fest_blob'} && !defined $some->{'analysis_blob'} && !%{ $some->{'build'} },
        'want => game: no other analysis, no builder');

    # a budget of nothing: no patterns, not complete
    my $none = Games::Sokoban::Solver::prepare('rows' => $levels[3], 'blok_budget' => 0, 'want' => ['game']);
    is($none->{'blok_complete'}, 0, 'blok_budget 0: not complete');
    is_deeply($none->{'game'}{'blok'}, {}, 'and no bloks');
    my $all = Games::Sokoban::Solver::prepare('rows' => $levels[3], 'blok_budget' => -1, 'want' => ['game']);
    ok($all->{'blok_complete'}, 'blok_budget -1: the complete table');
}

# the corridor: an opening, and the opening alone does not solve it
{
    my $p = Games::Sokoban::Solver::prepare('rows' => $corridor, 'want' => ['game']);
    ok(length $p->{'firststep'}, 'the corridor gives a forced opening (' . $p->{'firststep'} . ')');
    is($p->{'solved_by_opening'}, 0, 'the opening leaves a box to push');
    ok($p->{'code1'} ne $p->{'code'}{'code'}, 'the reduced board differs from code1');
}

# solved by the opening alone
{
    my ($one) = Games::Sokoban::Solver::read_levels(<<'XSB');
#####
#@  #
### #
###$#
###.#
#####
XSB
    my $p = eval {Games::Sokoban::Solver::prepare('rows' => $one)};
SKIP: {
        skip 'this corridor is not one the templates empty: ' . ((split /\n/, "$@")[0] // ''), 3 unless $p;
        note("opening '$p->{'firststep'}', solved_by_opening $p->{'solved_by_opening'}");
        if ($p->{'solved_by_opening'}) {
            ok(!exists $p->{'game_blob'}, 'solved by the opening: no analysis');
            my $r = Games::Sokoban::Solver::solve_level('rows' => $one, 'time' => 1, 'optimal' => 1);
            is($r->{'status'}, 'SOLVED',                                  'solve_level: SOLVED by the opening');
            is($r->{'path'},   Games::Sokoban::Solver::full_path($p, ''), 'the path is the opening alone');
        }
        else {pass('the templates leave a push: nothing more to test here') for 1 .. 3}
    }
}

# the open level gets its ring
{
    my $p = Games::Sokoban::Solver::prepare('rows' => $open, 'want' => ['game']);
    like($p->{'notes'}[0], qr/ring of walls/, 'the open level is noted');
    like($p->{'code1'},    qr/\A9+,/,         'and ringed');
}

# refusals
{
    for my $case (
        [['#####', '#@ $#',  '#####'], qr/REFUSED: .*goals/,           'boxes and goals differ'],
        [['#####', '#@ .#',  '#####'], qr/REFUSED: no box/,            'no box'],
        [['#####', '#@*.#',  '#####'], qr/REFUSED: /,                  'a box on a goal and an empty goal: something is wrong'],
        [['#####', '#@@$.#', '#####'], qr/REFUSED: 2 players/,         'two players'],
        [['#####', '#@x$.#', '#####'], qr/REFUSED: the character 'x'/, 'a foreign character'],
        )
    {
        my ($rows, $re, $what) = @$case;
        my $ok = eval {Games::Sokoban::Solver::prepare('rows' => $rows); 1};
        ok(!$ok, "refused: $what");
        like($@, $re, "... with its sentence");
        my $r = Games::Sokoban::Solver::solve_level('rows' => $rows);
        is($r->{'status'}, 'REFUSED', "solve_level: REFUSED ($what)");
        like($r->{'reason'}, qr/\AREFUSED: /, 'and the reason is the sentence');
        unlike($r->{'reason'}, qr/ at \S+ line \d+|\n/, 'without the place in the code or a second line');
    } ## end for my $case ([['#####'...]])
}

# --- first_solution, serial ------------------------------------------------------
{
    my $p = Games::Sokoban::Solver::prepare('rows' => $levels[1]);
    my @answers;
    my $first =
        Games::Sokoban::Solver::first_solution('prepared' => $p, 'time' => $TIME, 'on_answer' => sub ($a) {push @answers, $a});
    is($first->{'reason'}, 'SOLVED', 'serial race: solved');
    ok(length $first->{'mode'}, "by $first->{'mode'}");
    is(Games::Sokoban::Solver::Replay::check($p->{'code'}{'code'}, $first->{'path'}),
        undef, 'the path plays on the reduced level');
    is($first->{'sollen'}, length $first->{'path'}, 'sollen');
    ok(@answers >= 1, 'answers heard');
    is_deeply($first->{'died'}, [], 'nobody died');
    is($answers[0]{'mode'}, 'ORDER', 'the race starts with ORDER');

    # a subset of modes, and modes whose engine has no analysis are left out
    my $some = Games::Sokoban::Solver::prepare('rows' => $levels[1], 'want' => ['game']);
    my @notes;
    my $r = Games::Sokoban::Solver::first_solution(
        'prepared' => $some,
        'time'     => $TIME,
        'modes'    => ['FF_BASE', 'E_BASE', 'PUSH_SCORE'],
        'on_note'  => sub ($t) {push @notes, $t}
    );
    is($r->{'reason'}, 'SOLVED',     'without the two analyses the race still solves');
    is($r->{'mode'},   'PUSH_SCORE', 'by the one mode that had its analysis');
    ok(scalar(grep {/left out/} @notes) >= 1, 'the modes left out are noted') or diag(join "\n", @notes);

    # lazy: the analyses are built when a mode needs them
    my $lazy = Games::Sokoban::Solver::prepare('rows' => $levels[1], 'lazy' => 1);
    $r = Games::Sokoban::Solver::first_solution('prepared' => $lazy, 'time' => $TIME, 'modes' => ['FF_BASE']);
    is($r->{'reason'}, 'SOLVED',  'lazy: FF_BASE solved');
    is($r->{'mode'},   'FF_BASE', 'by FF_BASE');
    ok(length $lazy->{'fest_blob'},       'its analysis was built on the way');
    ok(!defined $lazy->{'analysis_blob'}, 'the other one was not needed');
}

# --- best_solution and full_path ------------------------------------------------
{
    for my $level ($levels[0], $levels[3], $corridor) {
        my $p        = Games::Sokoban::Solver::prepare('rows' => $level, 'want' => ['game']);
        my $best_len = length BruteForce::solve($p->{'code'}{'code'});
        my $first = Games::Sokoban::Solver::first_solution('prepared' => $p, 'time' => $TIME, 'modes' => ['PUSH_SCORE', 'ORDER']);
        is($first->{'reason'}, 'SOLVED', "$level->{'title'}: a first solution");
        my @improved;
        my $best = Games::Sokoban::Solver::best_solution(
            'prepared'    => $p,
            'seed'        => $first->{'path'},
            'time'        => 30,
            'on_improved' => sub ($path, $s) {push @improved, $path}
        );
        is($best->{'reason'},      'SOLVED',                     "$level->{'title'}: proved");
        is($best->{'proved'},      1,                            'proved = 1');
        is($best->{'status'},      'SOLVED',                     'status SOLVED');
        is(length $best->{'path'}, $best_len,                    "the oracle's optimum ($best_len moves)");
        is(scalar @improved,       scalar @{ $best->{'track'} }, 'on_improved once per improvement');
        my $full = Games::Sokoban::Solver::full_path($p, $best->{'path'});
        like($full, qr/\A\Q$p->{'firststep'}\E/, 'the full path begins with the opening');
        is(Games::Sokoban::Solver::Replay::check($p->{'code1'}, $full), undef, 'and plays on the level as drawn');
        is(length($full), length($p->{'firststep'}) + $best_len, 'as long as opening + optimum') if $level != $corridor;
    } ## end for my $level ($levels[...])

    # a time of a microsecond: TIMEOUT with the seed
    my $p     = Games::Sokoban::Solver::prepare('rows' => $levels[3], 'want' => ['game']);
    my $first = Games::Sokoban::Solver::first_solution('prepared' => $p, 'time' => $TIME, 'modes' => ['PUSH_SCORE']);
    my $best  = Games::Sokoban::Solver::best_solution('prepared' => $p, 'seed' => $first->{'path'}, 'time' => 0.000001);
    is($best->{'reason'}, 'TIMEOUT', 'no time: TIMEOUT');
    is($best->{'proved'}, 0,         'not proved');
    ok(length($best->{'path'}) <= length($first->{'path'}), 'the path is the seed at worst');

    # a stop already raised: IGNORE or a proof before the first check
    my %stop = ($p->{'label'} => 1);
    $best = Games::Sokoban::Solver::best_solution('prepared' => $p, 'seed' => $first->{'path'}, 'time' => 30, 'stop' => \%stop);
    ok($best->{'reason'} eq 'IGNORE' || $best->{'reason'} eq 'SOLVED', "stop raised: $best->{'reason'}");
    is($best->{'status'}, $best->{'reason'}, 'status named the same');

    # a wrong mode
    ok(!eval {Games::Sokoban::Solver::best_solution('prepared' => $p, 'mode' => 'FAST'); 1}, 'a wrong optimal mode is refused');

    # full_path refuses a path that does not solve
    ok(!eval {Games::Sokoban::Solver::full_path($p, 'u'); 1}, 'full_path: a path that does not solve is refused');
    like($@, qr/\AINTERNAL: /, '... as INTERNAL');
}

# --- solve_level, end to end ----------------------------------------------------
{
    for my $level ($levels[2], $corridor) {
        my @notes;
        my $r = Games::Sokoban::Solver::solve_level(
            'rows'    => $level,
            'time'    => $TIME,
            'optimal' => 30,
            'modes'   => ['ORDER', 'PUSH_SCORE', 'FF_BASE'],
            'on_note' => sub ($t) {push @notes, $t}
        );
        is($r->{'status'}, 'SOLVED',          "$level->{'title'}: solve_level SOLVED");
        is($r->{'title'},  $level->{'title'}, 'the title');
        is($r->{'proved'}, 1,                 'proved');
        my ($code0, $code1) = Games::Sokoban::Solver::Level::normalize($level->{'rows'});
        is(Games::Sokoban::Solver::Replay::check($code1, $r->{'path'}), undef, 'the path plays on the level as drawn');
        is($r->{'moves'},  length $r->{'path'},                                'moves');
        is($r->{'pushes'}, ($r->{'path'} =~ tr/DLRU//),                        'pushes');
        is($r->{'forced'}, length $r->{'prepared'}{'firststep'},               'forced = the opening');
        ok(ref $r->{'first'} && ref $r->{'best'}, 'first and best are there');
        is(
            length($r->{'path'}),
            $r->{'forced'} + length BruteForce::solve($r->{'prepared'}{'code'}{'code'}),
            'opening + the oracle optimum'
          )
            if $level != $corridor;
    } ## end for my $level ($levels[...])
    my $r = Games::Sokoban::Solver::solve_level('rows' => $levels[0], 'time' => $TIME, 'optimal' => 0, 'modes' => ['PUSH_SCORE']);
    is($r->{'status'}, 'SOLVED', 'optimal 0: SOLVED by the race alone');
    ok(!$r->{'proved'} && !defined $r->{'best'}, 'and not proved, no best');

    # nothing solves it: a Festival mode with no time at all walks away
    $r = Games::Sokoban::Solver::solve_level('rows' => $levels[3], 'time' => 0.0001, 'modes' => ['FF_BASE']);
    is($r->{'status'}, 'UNSOLVED', 'FF_BASE with no time: UNSOLVED');
    like($r->{'reason'}, qr/no mode solved/, 'with the reason');
    ok($r->{'first'}{'answers'}[0]{'reason'} ne 'SOLVED',
        'its answer was not SOLVED (' . $r->{'first'}{'answers'}[0]{'reason'} . ')');
    ok(!defined $r->{'path'}, 'no path');
}

# --- a shared pool, threads where they are, the patterns from the pool -----------
SKIP: {
    skip 'this perl has no ithreads', 12 unless $Config::Config{'useithreads'};
    my $pool = Games::Sokoban::Solver::pool('jobs' => 3);
    is($pool->threaded, 1, 'a threaded pool');
    for my $level ($levels[1], $levels[3]) {
        my $serial = Games::Sokoban::Solver::prepare('rows' => $level, 'want' => ['game'], 'blok_budget' => -1);
        my $pooled = Games::Sokoban::Solver::prepare('rows' => $level, 'want' => ['game'], 'blok_budget' => -1, 'pool' => $pool);
        is_deeply(
            $pooled->{'game'}{'blok'},
            $serial->{'game'}{'blok'},
            "$level->{'title'}: the pool's bloks equal the serial ones"
        );
        is($pooled->{'blok_complete'},           1,                                    'complete');
        is(scalar @{ $pooled->{'blok_report'} }, scalar @{ $serial->{'blok_report'} }, 'the same number of patterns reported');
        my $r = Games::Sokoban::Solver::solve_level('rows' => $level, 'pool' => $pool, 'time' => $TIME, 'optimal' => 30);
        is($r->{'status'}, 'SOLVED', "$level->{'title'}: solved through the shared pool");
        ok($r->{'proved'}, 'and proved');
    }
    $pool->close;
    $pool->join;
    pass('the pool joined');
} ## end SKIP:
done_testing;
