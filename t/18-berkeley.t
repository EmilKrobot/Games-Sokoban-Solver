# The BerkeleyDB branch: the seam's two store families in a scratch root, the
# lock against a second process, what a close keeps and what it deletes, and
# the two twins on the micro levels -- Firstbet::Berk against Firstbet,
# Optimal::Berk against the brute-force oracle, warm after a TIMEOUT.
# Skipped where the BerkeleyDB module is not installed: the branch is optional.
use v5.42;
no warnings 'once';    # the twins' package variables are set once each

# A twin is held to its baseline position for position, and the search breaks
# its ties by hash order: without a fixed hash seed two correct copies differ
# run to run. perl reads the seed at start-up, so this test runs itself again
# with it set when it was started without.
BEGIN {
    unless (($ENV{'PERL_HASH_SEED'} // '') eq '0' and ($ENV{'PERL_PERTURB_KEYS'} // '') eq '0') {
        local $ENV{'PERL_HASH_SEED'}    = '0';
        local $ENV{'PERL_PERTURB_KEYS'} = '0';
        my $rc = system($^X, (map { "-I$_" } grep { !ref } @INC), $0, @ARGV);
        exit($rc == -1 ? 1 : $rc >> 8);
    }
}
use Test::More;
use File::Temp ();
use lib 't/lib';
use BruteForce ();
use Games::Sokoban::Solver::Level   ();
use Games::Sokoban::Solver::Code    ();
use Games::Sokoban::Solver::Parser  ();
use Games::Sokoban::Solver::Replay  ();
use Games::Sokoban::Solver::Path    ();
use Games::Sokoban::Solver::Firstbet ();

plan skip_all => 'the BerkeleyDB module is not installed: the branch is optional' unless eval { require BerkeleyDB; 1 };
require Games::Sokoban::Solver::Berkeley;
require Games::Sokoban::Solver::Firstbet::Berk;
require Games::Sokoban::Solver::Optimal::Berk;

my $B = 'Games::Sokoban::Solver::Berkeley';

# ---- the root --------------------------------------------------------------------
{
    local $Games::Sokoban::Solver::Berkeley::ROOT = undef;
    local $ENV{'SOKOBAN_BERK_ROOT'};
    delete $ENV{'SOKOBAN_BERK_ROOT'};
    ok(!eval { Games::Sokoban::Solver::Berkeley::berk_root(); 1 }, 'no root set: refused');
    like($@, qr/no root directory/, '... saying so');
}
my $root = File::Temp::tempdir('soko-solver-XXXXXX', 'TMPDIR' => 1, 'CLEANUP' => 1);
$Games::Sokoban::Solver::Berkeley::ROOT = $root;
(my $slash = $root) =~ tr{\\}{/};
is(Games::Sokoban::Solver::Berkeley::berk_root(), $slash, 'the root as set, with forward slashes');

# ---- the fb_* family -------------------------------------------------------------------
{
    Games::Sokoban::Solver::Berkeley::fb_init(7, 16 * 1024 * 1024, 'TEST');
    ok(-d "$slash/Firstbet/G7_TEST", 'fb_init made the level directory, tagged by mode');
    ok(-f "$slash/Firstbet/G7_TEST/lock", 'and took its lock file');
    my ($p, $q, $r) = ('aaaa', 'bbbb', 'cccc');
    is(Games::Sokoban::Solver::Berkeley::fb_isbad($p), 0, 'a position not marked bad');
    Games::Sokoban::Solver::Berkeley::fb_setbad($p);
    is(Games::Sokoban::Solver::Berkeley::fb_isbad($p), 1, '... is bad once marked');
    is(Games::Sokoban::Solver::Berkeley::fb_tahy_get($p), undef, 'no move list yet');
    Games::Sokoban::Solver::Berkeley::fb_tahy_set($p, [$q, $r]);
    is_deeply(Games::Sokoban::Solver::Berkeley::fb_tahy_get($p), [$q, $r], 'the move list comes back as it went');
    Games::Sokoban::Solver::Berkeley::fb_tahy_del($p);
    is(Games::Sokoban::Solver::Berkeley::fb_tahy_get($p), undef, '... and is gone when deleted');
    Games::Sokoban::Solver::Berkeley::fb_pos_set($q, $p);
    is(Games::Sokoban::Solver::Berkeley::fb_pos_present($q), 1, 'a position seen');
    is(Games::Sokoban::Solver::Berkeley::fb_pos_parent($q), $p, '... with its parent');
    is(Games::Sokoban::Solver::Berkeley::fb_pos_count(), 1, '... counted');
    Games::Sokoban::Solver::Berkeley::fb_pos_del($q);
    is(Games::Sokoban::Solver::Berkeley::fb_pos_present($q), 0, '... forgotten when deleted');

    # a second process on the same directory is refused
    my $out = `"$^X" -Ilib -MGames::Sokoban::Solver::Berkeley -e "\$Games::Sokoban::Solver::Berkeley::ROOT = shift; eval { Games::Sokoban::Solver::Berkeley::fb_init(7, 16777216, 'TEST'); 1 } or print \$@" "$slash" 2>&1`;
    like($out, qr/open in another process/, 'a second process on the same directory is refused');

    Games::Sokoban::Solver::Berkeley::fb_close();
    ok(-f "$slash/Firstbet/G7_TEST/bad.brk" && -f "$slash/Firstbet/G7_TEST/tahy.brk", 'the close keeps the deadlock and move caches');
    Games::Sokoban::Solver::Berkeley::fb_sweep([7]);
    ok(!-f "$slash/Firstbet/G7_TEST/pozice.brk", 'a sweep of a kept level removes its scratch');
    ok(-f "$slash/Firstbet/G7_TEST/bad.brk", '... and keeps the caches');
    Games::Sokoban::Solver::Berkeley::fb_sweep([7], [7]);
    ok(!-d "$slash/Firstbet/G7_TEST", 'a sweep of a solved level removes its directory');
}

# ---- the g_* family ----------------------------------------------------------------------
{
    ok(!eval { Games::Sokoban::Solver::Berkeley::g_init(9, 4 * 1024 ** 3, 1); 1 }, 'a pool over 3 GB is refused');
    like($@, qr/at most 3 GB/, '... with the reason');
    Games::Sokoban::Solver::Berkeley::g_init(9, 16 * 1024 * 1024, 1);
    ok(-d "$slash/Optimal/G9", 'g_init made the level directory');
    Games::Sokoban::Solver::Berkeley::g_setbad('xx');
    is(Games::Sokoban::Solver::Berkeley::g_isbad('xx'), 1, 'bad set and read');
    Games::Sokoban::Solver::Berkeley::g_tahy_set('xx', ['yy', 3, 'zz', 5]);
    is_deeply(Games::Sokoban::Solver::Berkeley::g_tahy_get('xx'), ['yy', 3, 'zz', 5], 'a move list with its steps');
    Games::Sokoban::Solver::Berkeley::g_pos_set('yy', 'xx', 12);
    is(Games::Sokoban::Solver::Berkeley::g_pos_getsol('yy'), 12, 'a position with its cost');
    is(Games::Sokoban::Solver::Berkeley::g_pos_getparent('yy'), 'xx', '... and its parent');
    Games::Sokoban::Solver::Berkeley::g_bq_add('cc', 30);
    Games::Sokoban::Solver::Berkeley::g_bq_add('aa', 10);
    Games::Sokoban::Solver::Berkeley::g_bq_add('bb', 10);
    is_deeply([Games::Sokoban::Solver::Berkeley::g_bq_pop()], [10, 'aa'], 'the queue pops the cheapest, first in first out');
    is_deeply([Games::Sokoban::Solver::Berkeley::g_bq_pop()], [10, 'bb'], '... then the next of that cost');
    is(Games::Sokoban::Solver::Berkeley::g_bq_trim(20), 1, 'the trim removes what costs 20 or more');
    is_deeply([Games::Sokoban::Solver::Berkeley::g_bq_pop()], [], '... and the queue is empty');
    Games::Sokoban::Solver::Berkeley::g_exp_set('yy');
    is(Games::Sokoban::Solver::Berkeley::g_exp_has('yy'), 1, 'expanded set');
    Games::Sokoban::Solver::Berkeley::g_exp_del('yy');
    is(Games::Sokoban::Solver::Berkeley::g_exp_has('yy'), 0, '... and cleared');
    ok(!eval { Games::Sokoban::Solver::Berkeley::g_init(10, 16 * 1024 * 1024, 1); 1 }, 'a second level before the close is refused');
    Games::Sokoban::Solver::Berkeley::g_close(0);
    ok(-f "$slash/Optimal/G9/bad.brk" && -f "$slash/Optimal/G9/tahy.brk", 'a close without solving keeps the caches');
    ok(!-f "$slash/Optimal/G9/pozice.brk" && !-f "$slash/Optimal/G9/bucket.brk" && !-f "$slash/Optimal/G9/expanded.brk",
        '... and deletes the run state');
    Games::Sokoban::Solver::Berkeley::g_init(9, 16 * 1024 * 1024, 1);
    is(Games::Sokoban::Solver::Berkeley::g_isbad('xx'), 1, 'the deadlock cache survived the close');
    Games::Sokoban::Solver::Berkeley::g_close(1);
    ok(!-d "$slash/Optimal/G9", 'a close after a solve removes the directory');
}

# ---- the twins on the micro levels ------------------------------------------------------
my $room = <<'XSB';
########
#  .   #
# $$$ .#
#  .  @#
########
XSB
my ($level) = Games::Sokoban::Solver::Level::read($room);
my ($code0, $code1) = Games::Sokoban::Solver::Level::normalize($level->{'rows'});
my %code = Games::Sokoban::Solver::Code::prepare($code1);
my %game = Games::Sokoban::Solver::Parser::parse(\%code);
my $blob = Games::Sokoban::Solver::Parser::blob(\%game);

for my $pkg ('Games::Sokoban::Solver::Firstbet', 'Games::Sokoban::Solver::Firstbet::Berk', 'Games::Sokoban::Solver::Optimal::Berk') {
    no strict 'refs';
    ${"${pkg}::QUIET"} = 2;
}
$Games::Sokoban::Solver::Firstbet::Berk::CACHE          = 16 * 1024 * 1024;
$Games::Sokoban::Solver::Firstbet::Berk::STORE_PER_MODE = 1;
$Games::Sokoban::Solver::Optimal::Berk::CACHE           = 16 * 1024 * 1024;

for my $mode ('PUSH_SCORE', 'BACKWARD', 'FEATURE') {
    my ($ar, $ap, undef, $an) = Games::Sokoban::Solver::Firstbet::solve(11, $blob, 20, $mode);
    my ($br, $bp, undef, $bn) = Games::Sokoban::Solver::Firstbet::Berk::solve(11, $blob, 20, $mode);
    is($br, 'SOLVED', "Firstbet::Berk $mode: solved");
    is($bp, $ap, "Firstbet::Berk $mode: the same path as Firstbet");
    is($bn, $an, "Firstbet::Berk $mode: the same number of positions");
    is(Games::Sokoban::Solver::Replay::check($code{'code'}, $bp), undef, "Firstbet::Berk $mode: the path plays");
}
ok(-d "$slash/Firstbet/G11_PUSH_SCORE", 'the forward stores of the solved level stay until the sweep');
Games::Sokoban::Solver::Berkeley::fb_sweep([11], [11]);
ok(!-d "$slash/Firstbet/G11_PUSH_SCORE" && !-d "$slash/Firstbet/G11b", 'the sweep removed them, the pull scratch too');

{
    my $best = BruteForce::solve($code{'code'});
    $Games::Sokoban::Solver::Optimal::Berk::LIMIT = 30;
    for my $mode ('DIAL', 'ASTAR', 'FIFO') {
        $Games::Sokoban::Solver::Optimal::Berk::MODE = $mode;
        my ($reason, $path) = Games::Sokoban::Solver::Optimal::Berk::solve(12, $blob, undef);
        is($reason, 'SOLVED', "Optimal::Berk $mode: proved");
        is(length $path, length $best, "Optimal::Berk $mode: the optimum of the oracle");
        is(Games::Sokoban::Solver::Replay::check($code{'code'}, $path), undef, "Optimal::Berk $mode: the path plays");
        is($Games::Sokoban::Solver::Optimal::Berk::LastStatus, 'SOLVED', "Optimal::Berk $mode: the stop is named");
        ok(!-d "$slash/Optimal/G12", "Optimal::Berk $mode: a proof removes the level's directory");
    }

    # a limit of nothing: TIMEOUT, the caches kept, and the next run warm
    $Games::Sokoban::Solver::Optimal::Berk::MODE  = 'DIAL';
    $Games::Sokoban::Solver::Optimal::Berk::LIMIT = 0.000001;
    my $seed = BruteForce::longer($code{'code'}, $best, length($best) + 12) // $best;
    my ($reason, $path) = Games::Sokoban::Solver::Optimal::Berk::solve(12, $blob, $seed);
    is($reason, 'TIMEOUT', 'a limit of a microsecond: TIMEOUT');
    is($Games::Sokoban::Solver::Optimal::Berk::LastStatus, 'TIMEOUT', '... named');
    ok(-f "$slash/Optimal/G12/bad.brk" && -f "$slash/Optimal/G12/tahy.brk", 'the caches stay in the directory');
    ok(!-f "$slash/Optimal/G12/pozice.brk", 'the run state does not');
    $Games::Sokoban::Solver::Optimal::Berk::LIMIT = 30;
    my @calls;
    $Games::Sokoban::Solver::Optimal::Berk::ON_IMPROVED = sub ($p, $cas) { push @calls, $p };
    ($reason, $path) = Games::Sokoban::Solver::Optimal::Berk::solve(12, $blob, $seed);
    $Games::Sokoban::Solver::Optimal::Berk::ON_IMPROVED = undef;
    is($reason, 'SOLVED', 'the warm run proves');
    is(length $path, length $best, '... the optimum');
    is(scalar @calls, scalar @Games::Sokoban::Solver::Optimal::Berk::Track, 'ON_IMPROVED once per entry of @Track');
    ok(!-d "$slash/Optimal/G12", 'and the directory is gone');
}

done_testing;
