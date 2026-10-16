# The settings: the defaults and their kinds, the parser (comments, spaces, a
# ';' inside a value, a BOM, a section heading, an empty file, a wrong line, an
# unknown key), save -> load unchanged, the three layers of resolve, refusals
# of nonsense, and ask() over a prepared input (Enter = the offer, a wrong
# answer asked again).
use v5.42;
use Test::More;
use File::Temp ();
use Games::Sokoban::Solver::Config ();

my $C = 'Games::Sokoban::Solver::Config';
my $tmp = File::Temp->newdir;
my $dir = "$tmp";
$dir =~ tr{\\}{/};

# defaults
my %d = Games::Sokoban::Solver::Config::defaults();
my @names = Games::Sokoban::Solver::Config::names();
is(scalar @names, 15, 'fifteen settings');
is_deeply([sort keys %d], [sort @names], 'defaults has every name and no other');
is_deeply([Games::Sokoban::Solver::Config::check(\%d)], [], 'the defaults pass check()');
ok($d{'jobs'} >= 1 && $d{'jobs'} <= 8, 'jobs between 1 and 8');
is($d{'time'}, 60, 'time 60');
is($d{'optimal_mode'}, 'DIAL', 'DIAL by default');
is($d{'blok_budget'}, 30, 'blok_budget 30 (the calibration)');
like($d{'berkeley'}, qr/\A[01]\z/, 'berkeley 0 or 1');
is($d{'berkeley'}, (eval { require BerkeleyDB; 1 } ? 1 : 0), 'berkeley 1 exactly when the module loads');
like(Games::Sokoban::Solver::Config::describe('time'), qr/seconds/, 'describe() says what a key means');
eval { Games::Sokoban::Solver::Config::describe('nosuch') };
like($@, qr/no setting/, 'describe of an unknown key refused');

# dir, path
{
    local $ENV{'SOKO_SOLVER_HOME'} = 'C:\\somewhere\\cfg';
    is(Games::Sokoban::Solver::Config::dir(), 'C:/somewhere/cfg', 'SOKO_SOLVER_HOME wins, slashes forward');
    is(Games::Sokoban::Solver::Config::path(), 'C:/somewhere/cfg/soko-solver.ini', 'path under it');
    my %dd = Games::Sokoban::Solver::Config::defaults();
    is($dd{'berkeley_root'}, 'C:/somewhere/cfg/berkeley', 'berkeley_root under the config dir');
}
{
    local $ENV{'SOKO_SOLVER_HOME'};
    delete $ENV{'SOKO_SOLVER_HOME'};
    like(Games::Sokoban::Solver::Config::path(), qr{/soko-solver/soko-solver\.ini\z}, 'the default place ends in soko-solver/soko-solver.ini');
}

# the parser
sub write_file ($name, $text) {
    open(my $fh, '>:raw', "$dir/$name") or die $!;
    print {$fh} $text;
    close $fh;
    return "$dir/$name";
}

my $f = write_file('a.ini', "\xEF\xBB\xBF; a comment\r\n# another\r\n\r\n[section]\r\n  time =  90  \r\njobs=2\r\nberkeley_root = \"D:/x y ; z\"\r\nformat = json ; not a comment here\r\n");
my %got = Games::Sokoban::Solver::Config::load($f);
is_deeply(\%got, { 'time' => '90', 'jobs' => '2', 'berkeley_root' => 'D:/x y ; z', 'format' => 'json ; not a comment here' },
    'BOM, CRLF, comments, a section heading, spaces, quotes and a ; inside a value');
$f = write_file('empty.ini', '');
is_deeply({ Games::Sokoban::Solver::Config::load($f) }, {}, 'an empty file sets nothing');
$f = write_file('bad.ini', "time = 5\nthis is no setting\n");
eval { Games::Sokoban::Solver::Config::load($f) };
like($@, qr/line 2: not a 'key = value' line/, 'a line that is no setting is refused with its number');
$f = write_file('unknown.ini', "speed = 5\n");
eval { Games::Sokoban::Solver::Config::load($f) };
like($@, qr/no setting 'speed'/, 'an unknown key is refused');
eval { Games::Sokoban::Solver::Config::load("$dir/none.ini") };
like($@, qr/cannot read/, 'a missing file is an error');

# save -> load unchanged, the directory made
{
    my %cfg = %d;
    $cfg{'time'}          = 120;
    $cfg{'berkeley_root'} = 'D:/stores ; here';
    $cfg{'format'}        = 'report';
    my $file = "$dir/sub/dir/soko-solver.ini";
    Games::Sokoban::Solver::Config::save($file, \%cfg);
    ok(-f $file, 'save makes the directory and the file');
    my %back = Games::Sokoban::Solver::Config::load($file);
    is_deeply(\%back, { map { $_ => "$cfg{$_}" } keys %cfg }, 'load gives back exactly what was saved');
    open(my $fh, '<', $file) or die $!;
    my $text = do { local $/; <$fh> };
    close $fh;
    like($text, qr/^; seconds for one mode of the race/m, 'every key has its meaning in a comment');
    like($text, qr/^; default: 60\n^time = 120$/m, 'and its default beside the value');
    my %wrong = (%d, 'jobs' => 0);
    eval { Games::Sokoban::Solver::Config::save("$dir/wrong.ini", \%wrong) };
    like($@, qr/refusing to write.*jobs = '0'/, 'save refuses a wrong value');
    ok(!-e "$dir/wrong.ini", 'and writes nothing');
}

# check: the refusals of nonsense
{
    my @cases = (
        [{ 'jobs' => 0 },                 qr/jobs = '0' is not a whole number of at least 1/],
        [{ 'jobs' => '2.5' },             qr/jobs = '2\.5'/],
        [{ 'berkeley_cache' => 8 },       qr/berkeley_cache = '8' is not a pool in GB between 0\.001 and 3/],
        [{ 'time' => 0 },                 qr/time = '0' is not a number of seconds above 0/],
        [{ 'optimal' => -1 },             qr/optimal = '-1'/],
        [{ 'blok_budget' => -2 },         qr/blok_budget = '-2'/],
        [{ 'optimal_mode' => 'BEST' },    qr/optimal_mode = 'BEST' is not DIAL, ASTAR or FIFO/],
        [{ 'format' => 'xml' },           qr/format = 'xml'/],
        [{ 'berkeley' => 2 },             qr/berkeley = '2' is not 0 or 1/],
        [{ 'maxgb' => 'lots' },           qr/maxgb = 'lots'/],
        [{ 'berkeley_root' => '' },       qr/berkeley_root = '' is not a directory/],
        [{ 'nosuch' => 1 },               qr/unknown setting 'nosuch'/],
    );
    for my $c (@cases) {
        my %cfg = (%d, %{ $c->[0] });
        my @p = Games::Sokoban::Solver::Config::check(\%cfg);
        like(join('; ', @p), $c->[1], 'check refuses ' . join(' ', %{ $c->[0] }));
    }
    my %cfg = %d;
    delete $cfg{'time'};
    like(join('; ', Games::Sokoban::Solver::Config::check(\%cfg)), qr/time is not set/, 'a missing key is said');
    %cfg = (%d, 'blok_budget' => -1, 'optimal' => 0, 'maxgb' => 0, 'berkeley_cache' => 3);
    is_deeply([Games::Sokoban::Solver::Config::check(\%cfg)], [], 'blok_budget -1, optimal 0, cache 3 are allowed');
}

# resolve: defaults < ini < command line
{
    my $file = write_file('r.ini', "time = 200\njobs = 3\nformat = sok\n");
    my %cfg = Games::Sokoban::Solver::Config::resolve({ 'jobs' => 5, 'optimal' => undef }, 'ini' => $file);
    is($cfg{'time'},    200,   'ini over the default');
    is($cfg{'jobs'},    5,     'command line over the ini');
    is($cfg{'format'},  'sok', 'ini value kept where the command line says nothing');
    is($cfg{'optimal'}, 60,    'an undefined command-line value means not given');
    %cfg = Games::Sokoban::Solver::Config::resolve({}, 'ini' => $file, 'no_ini' => 1);
    is($cfg{'time'}, 60, 'no_ini: the file is not read');
    %cfg = Games::Sokoban::Solver::Config::resolve({ 'time' => 7 }, 'ini' => "$dir/none.ini");
    is($cfg{'time'}, 7, 'a missing ini is simply left out');
    eval { Games::Sokoban::Solver::Config::resolve({ 'jobs' => 0 }, 'ini' => $file) };
    like($@, qr/jobs = '0'/, 'a wrong command-line value dies naming it');
    eval { Games::Sokoban::Solver::Config::resolve({ 'speed' => 1 }, 'no_ini' => 1) };
    like($@, qr/no setting 'speed'/, 'an unknown command-line key dies');
    my $bad = write_file('rb.ini', "berkeley_cache = 9\n");
    eval { Games::Sokoban::Solver::Config::resolve({}, 'ini' => $bad) };
    like($@, qr/berkeley_cache = '9'/, 'a wrong ini value dies naming it');
}

# ask: Enter takes the offer, a wrong answer is asked again, the store
# questions follow berkeley = 1 and not berkeley = 0
sub ask_with ($answers, %start) {
    my %cfg = (%d, %start);
    open(my $in,  '<', \$answers) or die $!;
    my $shown = '';
    open(my $out, '>', \$shown) or die $!;
    Games::Sokoban::Solver::Config::ask(\%cfg, $in, $out);
    close $out;
    return (\%cfg, $shown);
}
{
    my ($cfg, $shown) = ask_with("\n\n\n\n0\n");
    is($cfg->{'jobs'}, $d{'jobs'}, 'ask: Enter keeps jobs');
    is($cfg->{'time'}, 60, 'ask: Enter keeps time');
    is($cfg->{'berkeley'}, 0, 'ask: berkeley answered 0');
    is($cfg->{'berkeley_root'}, $d{'berkeley_root'}, 'ask: the store questions were not asked after 0');
    like($shown, qr/How many threads/, 'the first question shown');
    unlike($shown, qr/Where should the stores live/, 'the store question not shown');
    ok(!$cfg->{'maxgb'} || $cfg->{'maxgb'} > 0, 'maxgb kept or offered');

    SKIP: {
        skip 'BerkeleyDB not installed: the store questions are never asked', 5 unless eval { require BerkeleyDB; 1 };
        ($cfg, $shown) = ask_with("abc\n4\n\n\n\n1\nD:/stores\n9\n2\n300\n");
        is($cfg->{'jobs'}, 4, 'ask: a wrong answer (abc) is asked again, then 4 taken');
        like($shown, qr/'abc' is not a whole number/, 'and the wrong answer is said');
        is($cfg->{'berkeley_root'}, 'D:/stores', 'ask: the root taken');
        is($cfg->{'berkeley_cache'}, 2, 'ask: cache 9 refused, 2 taken');
        is($cfg->{'berkeley_from'}, 300, 'ask: from taken');
    }
}

done_testing;
