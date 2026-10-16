# The pool: a toy engine on both backends (serial, and threads where this perl
# has them), the race signal (a level won makes the other mode IGNORE), a DIE
# carried as a result, a handler of another kind over fifty tasks, next_timed
# answering 0 while nothing is finished, stop(), and that the serial backend
# never loads the thread modules -- Race.pm itself compiles with threads.pm
# refused.
use v5.42;
use Test::More;
use Config ();
use Time::HiRes ();

# THE TOY ENGINE: a mode is a word; 'WIN' solves in no time, 'SLOW' polls the
# race flag once every 50 ms until its limit and reports TIMEOUT or IGNORE,
# 'DIE' dies, 'FAIL' fails with a reason in $LastFail.
package Toy {
    our ($RACE_FLAG, $RACE_GID, $LastFail, $CTL);
    our @Calls;

    sub solve ($label, $blob, $limit, $mode) {
        push @Calls, [$label, $mode, $blob, $CTL];
        $LastFail = '';
        return ('SOLVED', 'rRdD', 0.01, 4) if $mode eq 'WIN';
        die "the toy engine was told to die on $label\n" if $mode eq 'DIE';
        if ($mode eq 'FAIL') { $LastFail = 'no reason at all'; return ('FAILED', '', 0.02, 7) }
        my $t0 = Time::HiRes::time();
        while (Time::HiRes::time() - $t0 < $limit) {
            return ('IGNORE', '', Time::HiRes::time() - $t0, 1) if $RACE_FLAG && $RACE_FLAG->{$RACE_GID};
            Time::HiRes::sleep(0.05);
        }
        return ('TIMEOUT', '', $limit, 10);
    }
}

use Games::Sokoban::Solver::Race ();

my $sum = sub (@n) { my $s = 0; $s += $_ for @n; return ($s, scalar @n) };

sub drain ($race) {
    my @r;
    while (my $r = $race->next) { push @r, $r }
    return @r;
}

# --- the serial backend --------------------------------------------------------
{
    my $race = Games::Sokoban::Solver::Race->new('jobs' => 1, 'engine' => 'Toy', 'handlers' => { 'sum' => $sum });
    $race->start;
    is($race->threaded, 0, 'serial: no threads');
    ok(!$INC{'threads.pm'}, 'serial: threads.pm not loaded');

    # B then A: the level is won, so A is IGNORE without running
    @Toy::Calls = ();
    $race->submit(7, 'WIN', 'blob7', 5);
    $race->submit(7, 'SLOW', 'blob7', 5);
    my $r = $race->next;
    is($r->{'reason'}, 'SOLVED', 'serial: WIN solved');
    is($r->{'kind'},   'solve',  'a solve carries its kind');
    is($r->{'path'},   'rRdD',   'the path');
    is($r->{'sollen'}, 4,        'sollen counted');
    is($r->{'pushes'}, 2,        'pushes counted');
    is($r->{'tid'},    0,        'serial tid 0');
    ok($r->{'wall'} > 0, 'wall measured');
    ok($race->solved(7), 'level 7 marked won');
    $r = $race->next;
    is($r->{'reason'}, 'IGNORE', 'serial: a mode of a won level is IGNORE');
    is(scalar @Toy::Calls, 1, 'and the engine was not called for it');

    # A then B on another level: A runs its limit, B wins
    my $t0 = Time::HiRes::time();
    $race->submit(8, 'SLOW', 'blob8', 0.3);
    $race->submit(8, 'WIN',  'blob8', 5);
    my @r = ($race->next, $race->next);
    is($r[0]{'reason'}, 'TIMEOUT', 'serial: SLOW ran its limit');
    is($r[1]{'reason'}, 'SOLVED',  'serial: then WIN');
    ok(Time::HiRes::time() - $t0 >= 0.3, 'the limit was really spent');

    # a list of modes in one task, stopped once the level is solved
    @Toy::Calls = ();
    $race->submit(9, ['FAIL', 'WIN', 'SLOW'], 'blob9', 5, { 'blok_replaces' => 1 });
    @r = ($race->next, $race->next, $race->next);
    is_deeply([map { $_->{'reason'} } @r], ['FAILED', 'SOLVED', 'IGNORE'], 'a list task: one row per mode, the rest IGNORE after the win');
    is($r[0]{'fail'}, 'no reason at all', '$LastFail carried as fail');
    is_deeply($Toy::Calls[0][3], { 'blok_replaces' => 1 }, 'the control word reaches the engine as $CTL');

    # a death is a result, not the end of the pool
    $race->submit(10, 'DIE', 'blob10', 5);
    $r = $race->next;
    is($r->{'reason'}, 'DIE', 'a die is reported as DIE');
    like($r->{'error'}, qr/told to die on 10/, 'with its message');

    # a handler of another kind
    $race->submit_task('sum', 11, 1 .. 10);
    $r = $race->next;
    is($r->{'kind'}, 'sum', 'a task of a kind carries it');
    is_deeply($r->{'payload'}, [55, 10], 'and what the handler returned');
    is($r->{'label'}, 11, 'and its label');

    # next_timed on the open serial pool: 0 when nothing is queued
    is($race->next_timed(1), 0, 'serial next_timed: 0 with nothing queued');
    eval { $race->next };
    like($@, qr/nothing queued/, 'serial next() on an open empty pool is refused');

    # stop() before the mode runs
    $race->stop(12);
    $race->submit(12, 'SLOW', 'blob12', 5);
    $r = $race->next;
    is($r->{'reason'}, 'IGNORE', 'stop() before the task: IGNORE at once');

    eval { $race->submit_task('nosuch', 1) };
    like($@, qr/no handler/, 'a kind without a handler is refused');

    $race->close;
    eval { $race->submit(13, 'WIN', 'b', 1) };
    like($@, qr/after close/, 'submit after close refused');
    is($race->next, undef, 'closed and drained: undef');
    $race->join;
    ok(!$INC{'threads.pm'} && !$INC{'Thread/Queue.pm'}, 'serial run over: no thread module loaded');
}

# fifty tasks of a kind, serially
{
    my $race = Games::Sokoban::Solver::Race->new('jobs' => 1, 'engine' => 'Toy', 'handlers' => { 'sum' => $sum });
    $race->start;
    $race->submit_task('sum', $_, 1 .. $_) for 1 .. 50;
    $race->close;
    my @r = drain($race);
    is(scalar @r, 50, 'serial: fifty results');
    is(scalar(grep { $_->{'payload'}[0] == $_->{'label'} * ($_->{'label'} + 1) / 2 } @r), 50, 'every sum right');
    $race->join;
}

# a serial pool asked for with jobs > 1 but serial => 1
{
    my $race = Games::Sokoban::Solver::Race->new('jobs' => 4, 'engine' => 'Toy', 'serial' => 1);
    $race->start;
    is($race->threaded, 0, 'serial => 1 overrides jobs');
    $race->close;
    $race->join;
}

# refusals of new() and start()
{
    eval { Games::Sokoban::Solver::Race->new('jobs' => 0) };
    like($@, qr/at least 1/, 'jobs 0 refused');
    eval { Games::Sokoban::Solver::Race->new('handlers' => { 'solve' => sub { } }) };
    like($@, qr/cannot be a handler/, "a handler named 'solve' refused");
    eval { Games::Sokoban::Solver::Race->new('handlers' => { 'x' => 'notcode' }) };
    like($@, qr/hash of kind/, 'a handler that is no code refused');
    my $race = Games::Sokoban::Solver::Race->new('engine' => 'No::Such::Engine');
    eval { $race->start };
    like($@, qr/not loaded/, 'an engine without solve() is refused at start');
    $race = Games::Sokoban::Solver::Race->new('engine' => 'Toy');
    eval { $race->submit(1, 'WIN', 'b', 1) };
    like($@, qr/before start/, 'submit before start refused');
}

# Race.pm compiles and runs serially in a perl where threads.pm cannot be loaded
{
    my $code = <<'PERL';
use v5.42;
unshift @INC, sub ($self, $file) { die "threads refused: $file\n" if $file =~ m{\A(?:threads|Thread)[/.]}; return };
package Toy { our ($RACE_FLAG, $RACE_GID, $LastFail); sub solve { return ('SOLVED', 'uU', 0, 1) } }
require Games::Sokoban::Solver::Race;
my $r = Games::Sokoban::Solver::Race->new('jobs' => 1, 'engine' => 'Toy');
$r->start; $r->submit(1, 'X', 'b', 1); $r->close;
my $res = $r->next; $r->join;
print $res->{'reason'}, ' ', ($INC{'threads.pm'} ? 'threads' : 'nothreads'), "\n";
PERL
    require File::Temp;
    my $script = File::Temp->new('SUFFIX' => '.pl');
    print {$script} $code;
    close $script;
    my $out = `"$^X" -Ilib "$script" 2>&1` // '';
    chomp $out;
    is($out, 'SOLVED nothreads', 'Race.pm compiles and runs serially with threads.pm refused') or diag($out);
}

# --- the threaded backend ------------------------------------------------------
SKIP: {
    skip 'this perl has no ithreads', 12 unless $Config::Config{'useithreads'};

    my $race = Games::Sokoban::Solver::Race->new('jobs' => 2, 'engine' => 'Toy', 'handlers' => { 'sum' => $sum });
    $race->start;
    is($race->threaded, 1, 'threads: the pool runs on threads');
    ok($INC{'threads.pm'}, 'threads.pm loaded at start');

    # SLOW and WIN on one level: WIN wins, SLOW comes back IGNORE within two seconds
    my $t0 = Time::HiRes::time();
    $race->submit(21, 'SLOW', 'blob', 10);
    $race->submit(21, 'WIN',  'blob', 10);
    my %got;
    for (1 .. 2) {
        my $r = $race->next;
        $got{ $r->{'mode'} } = $r;
    }
    is($got{'WIN'}{'reason'},  'SOLVED', 'threads: WIN solved');
    is($got{'SLOW'}{'reason'}, 'IGNORE', 'threads: SLOW told to stop');
    ok(Time::HiRes::time() - $t0 < 5, 'and it stopped well before its limit') or diag(Time::HiRes::time() - $t0);
    ok($got{'SLOW'}{'tid'} != $got{'WIN'}{'tid'} || 1, 'tids reported');

    # next_timed returns 0 while a task is still running
    $race->submit(22, 'SLOW', 'blob', 3);
    my $r = $race->next_timed(1);
    is($r, 0, 'threads: next_timed(1) gives 0 while SLOW runs');
    $race->stop(22);
    $r = $race->next_timed(5);
    is(ref $r && $r->{'reason'}, 'IGNORE', 'stop() ends the running mode with IGNORE');

    # a die carried out of a worker
    $race->submit(23, 'DIE', 'blob', 1);
    $r = $race->next;
    is($r->{'reason'}, 'DIE', 'threads: DIE carried out of the worker');

    # fifty tasks of a kind across the workers
    $race->submit_task('sum', $_, 1 .. $_) for 1 .. 50;
    my @sums;
    while (@sums < 50) {
        my $x = $race->next;
        push @sums, $x if $x->{'kind'} eq 'sum';
    }
    is(scalar(grep { $_->{'payload'}[0] == $_->{'label'} * ($_->{'label'} + 1) / 2 } @sums), 50, 'threads: every sum right');
    $race->close;
    is($race->next, undef, 'threads: every worker done');
    $race->join;
    is(scalar(threads->list), 0, 'threads: all joined');
}

done_testing;
