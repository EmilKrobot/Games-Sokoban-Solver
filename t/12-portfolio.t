# The policy of the race: 27 names exactly once, the race order a permutation
# of them, the engines' own lists agree, kinds and caps, the blob each engine
# takes, the routing by name (and to the BerkeleyDB twin under $BERK), the
# control word reaching Festival, and consistent() able to fail.
use v5.42;
use Test::More;
use Games::Sokoban::Solver::Portfolio ();
my $P    = 'Games::Sokoban::Solver::Portfolio';
my @all  = Games::Sokoban::Solver::Portfolio::all_modes();
my @race = Games::Sokoban::Solver::Portfolio::race_order();
is(scalar @all,  27, '27 modes in all');
is(scalar @race, 27, '27 in the race order');
my %seen;
++$seen{$_} for @all;
is(scalar(grep {$seen{$_} != 1} keys %seen), 0, 'every mode once in all_modes');
is_deeply([sort @race], [sort @all], 'race_order is a permutation of all_modes');
is($race[0],  'ORDER',    'ORDER goes first');
is($race[-1], 'CONVEYOR', 'CONVEYOR goes last');
is_deeply(
    [Games::Sokoban::Solver::Portfolio::firstbet_modes()],
    [qw(FEATURE PUSH_ASSIGN BACKWARD ORDER MOVE_SUM PUSH_SCORE ROUTE MOVE_SCORE FLOW CONVEYOR)],
    'Firstbet: ten, in order'
);
is_deeply([Games::Sokoban::Solver::Portfolio::firstback_modes()], ['FIRSTBACK'], 'FirstBack: one');
is_deeply(
    [Games::Sokoban::Solver::Portfolio::festival_modes()],
    [Games::Sokoban::Solver::Festival::modes()],
    'Festival: the engine\'s own'
);
is_deeply([Games::Sokoban::Solver::Portfolio::fest_modes()], [Games::Sokoban::Solver::Fest::modes()], 'Fest: the engine\'s own');
is(scalar(grep {/\AFF_/} @all), 8, 'eight FF_*');
is(scalar(grep {/\AE_/} @all),  8, 'eight E_*');
is_deeply([Games::Sokoban::Solver::Portfolio::solver_modes()], [qw(DIAL ASTAR FIFO)], 'the optimal regimes');
is(Games::Sokoban::Solver::Portfolio::own_limit('ORDER'),                           30,        'ORDER has 30 s of its own');
is(Games::Sokoban::Solver::Portfolio::own_limit('FF_HF'),                           undef,     'FF_HF has none');
is(Games::Sokoban::Solver::Portfolio::kind_of('BACKWARD'),                          'pull',    'BACKWARD is a pull search');
is(Games::Sokoban::Solver::Portfolio::kind_of('FIRSTBACK'),                         'pull',    'FIRSTBACK too');
is(Games::Sokoban::Solver::Portfolio::kind_of('FEATURE'),                           'forward', 'FEATURE forward');
is(Games::Sokoban::Solver::Portfolio::kind_of('ORDER'),                             'light',   'ORDER light');
is(Games::Sokoban::Solver::Portfolio::kind_of('FF_BASE'),                           'light',   'Festival light');
is(Games::Sokoban::Solver::Portfolio::kind_of('E_BASE'),                            'light',   'Fest light');
is(scalar(grep {Games::Sokoban::Solver::Portfolio::kind_of($_) eq 'forward'} @all), 7,         'seven forward modes');
is_deeply({ Games::Sokoban::Solver::Portfolio::default_caps() }, { 'pull' => 1, 'forward' => 3 }, 'the default caps');

for my $m (@all) {
    my $pkg = Games::Sokoban::Solver::Portfolio::engine_for($m);
    my $expect =
          $m =~ /\AFF_/     ? 'Games::Sokoban::Solver::Festival'
        : $m =~ /\AE_/      ? 'Games::Sokoban::Solver::Fest'
        : $m eq 'FIRSTBACK' ? 'Games::Sokoban::Solver::FirstBack'
        :                     'Games::Sokoban::Solver::Firstbet';
    is($pkg, $expect, "$m routes to $expect") or last;
    ok($pkg->can('solve'), "$pkg has solve")  or last;
    is(
        Games::Sokoban::Solver::Portfolio::blob_for($m),
        $m =~ /\AFF_/ ? 'fest' : $m =~ /\AE_/ ? 'analysis' : 'game',
        "$m takes the right blob"
      )
        or last;
} ## end for my $m (@all)
is_deeply([Games::Sokoban::Solver::Portfolio::consistent()], [], 'consistent: no problem');

# $BERK routes Firstbet's modes to the twin -- a stand-in package here
{

    package Games::Sokoban::Solver::Firstbet::Berk {our @Got; sub solve {push @Got, [@_]; return ('SOLVED', 'uU', 0.1, 3)}}
    local $Games::Sokoban::Solver::Portfolio::BERK = 1;
    is(
        Games::Sokoban::Solver::Portfolio::engine_for('FEATURE'),
        'Games::Sokoban::Solver::Firstbet::Berk',
        '$BERK: Firstbet modes go to the twin'
      );
    is(Games::Sokoban::Solver::Portfolio::engine_for('FF_HF'), 'Games::Sokoban::Solver::Festival', '$BERK: Festival untouched');
    is(
        Games::Sokoban::Solver::Portfolio::engine_for('FIRSTBACK'),
        'Games::Sokoban::Solver::FirstBack',
        '$BERK: FirstBack untouched'
      );
    my @r = Games::Sokoban::Solver::Portfolio::solve(5, 'blob', 7, 'PUSH_SCORE');
    is_deeply(\@r,                                             ['SOLVED', 'uU', 0.1, 3],          'solve() through the twin');
    is_deeply($Games::Sokoban::Solver::Firstbet::Berk::Got[0], [5, 'blob',      7, 'PUSH_SCORE'], 'the four arguments as given');
}

# the race signal and the control word reach the engine the mode belongs to
{
    no warnings 'redefine', 'once';
    my $flag = { 5 => 1 };
    local $Games::Sokoban::Solver::Portfolio::RACE_FLAG    = $flag;
    local $Games::Sokoban::Solver::Portfolio::RACE_GID     = 5;
    local $Games::Sokoban::Solver::Portfolio::CTL          = { 'blok_replaces' => 0, 'blok' => 0 };
    local $Games::Sokoban::Solver::Festival::BLOK_REPLACES = 1;
    local $Games::Sokoban::Solver::Fest::BLOK              = 1;
    local *Games::Sokoban::Solver::Festival::solve         = sub (@a) {
        $Games::Sokoban::Solver::Festival::LastFail = 'Perimeter not reached';
        return ('FAILED', '', 0.5, 9);
    };
    local *Games::Sokoban::Solver::Fest::solve = sub (@a) {return ('TIMEOUT', '', 1, 2)};
    my @r = Games::Sokoban::Solver::Portfolio::solve(5, 'fest blob', 3, 'FF_REV');
    is($r[0],                                            'FAILED',                'Festival answered');
    is($Games::Sokoban::Solver::Portfolio::LastFail,     'Perimeter not reached', '$LastFail carried up');
    is($Games::Sokoban::Solver::Festival::RACE_FLAG,     $flag,                   'race flag copied down to Festival');
    is($Games::Sokoban::Solver::Festival::RACE_GID,      5,                       'race gid too');
    is($Games::Sokoban::Solver::Festival::BLOK_REPLACES, 0, 'blok_replaces of the task written into Festival');
    is($Games::Sokoban::Solver::Fest::BLOK,              1, 'Fest untouched by a Festival call');
    Games::Sokoban::Solver::Portfolio::solve(5, 'analysis blob', 3, 'E_REV');
    is($Games::Sokoban::Solver::Fest::BLOK,      0,     'blok of the task written into Fest');
    is($Games::Sokoban::Solver::Fest::RACE_FLAG, $flag, 'race flag copied down to Fest');
    eval {Games::Sokoban::Solver::Portfolio::solve(5, 'blob', 3)};
    like($@, qr/needs a mode/, 'no mode: refused');
}

# consistent() can fail: a mode taken out of the engines' view
{
    no warnings 'redefine', 'once';
    local *Games::Sokoban::Solver::Fest::modes = sub {return qw(E_BASE E_REV)};
    my @p = Games::Sokoban::Solver::Portfolio::consistent();
    ok(scalar @p >= 6, 'consistent() names the modes missing from an engine') or diag(join "\n", @p);
    like(join("\n", @p), qr/E_HF is in no engine's list but in the race order/, 'and says which');
}
done_testing;
