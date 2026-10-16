package Games::Sokoban::Solver::Race;

# THE POOL OF WORKERS a racing caller needs, once, instead of in every caller.
#
# WHAT A RACE IS HERE. Several modes are set on the SAME level at the same time
# and the first one to solve it wins; the others are told to stop rather than
# run their budget out on a level that is already done. That "tell the others"
# is the only thing the workers must share, and it is one hash.
#
# WHAT THIS MODULE IS NOT. It knows nothing about levels, modes, engines or
# budgets. It hands work to workers and hands results back. Which modes, in
# what order, and what to do with a result, stays with the caller -- that is
# policy, and policy is what makes one caller different from another.
#
# TWO BACKENDS BEHIND ONE INTERFACE. With jobs > 1 on a perl built with
# ithreads the workers are threads, loaded at start() and not before: nothing in
# this file says `use threads`, so a perl without them compiles it, and a
# program that asks for one job never pays for the thread modules. With jobs = 1
# (or on a perl without ithreads, or when the caller says serial) the SAME
# submit / next / join calls run every task in this interpreter, one at a time,
# in the order submitted -- exactly as the worker closure would, so there is
# one tested way of running a task and the serial one is the deterministic one
# the gates use.
#
# TASKS HAVE A KIND. An ordinary task is a solve: the engine named at
# construction is called as solve($label, $blob, $limit, $mode) in Firstbet's
# shape. A task of another kind goes to the handler registered for it at
# construction (handlers => {blok => \&Finder::blok_task}) and its result is
# whatever the handler returned; that is how the patterns of a level are dealt
# out to the same pool that will race its modes (two pools in one process
# deadlock, since join waits on every thread there is).
#
# WHY THE ENGINE AND THE HANDLERS MUST BE LOADED BEFORE start(). Perl's threads
# clone the whole interpreter at the moment they are created; a module required
# afterwards exists only in the main thread, and the workers would die on a call
# into it. start() checks the engine for that reason. (The Sokoban project's
# Race also refused an open database connection for the same reason -- here
# there is none to refuse.)
#
# Lineage: Games::Sokoban::Race 0.03 of the Sokoban project.
use v5.42;
use warnings FATAL => 'uninitialized';
no warnings 'once';
use Carp        ();
use Config      ();
use Time::HiRes ();    # next_timed: a wait that came back early has to be made up
our $VERSION = '0.01';

=head1 NAME

Games::Sokoban::Solver::Race - run several solver modes at one level and keep the winner

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Portfolio ();     # the engine face, BEFORE start()
    use Games::Sokoban::Solver::Race;

    my $race = Games::Sokoban::Solver::Race->new(
        'jobs'     => 4,
        'engine'   => 'Games::Sokoban::Solver::Portfolio',
        'handlers' => { 'blok' => \&Games::Sokoban::Solver::Finder::blok_task },
    );
    $race->start;                                  # the workers, threads or none

    $race->submit($label, $mode, $blob, $limit, \%ctl);
    $race->submit_task('blok', $label, $pattern, $kmax, 1, '', $deadline);
    ...
    $race->close;                                  # no more work is coming
    while (my $r = $race->next) {
        if ($r->{'kind'} ne 'solve') { ...$r->{'payload'}... ; next }
        next if $r->{'error'};
        ...
    }
    $race->join;

=head1 DESCRIPTION

A pool of workers for a race: several modes are set on the same level at the
same time, the first to solve it wins and the others are told to stop. The
pool knows nothing about levels, modes or engines; it hands tasks to workers
and results back, and the one thing the workers share is the race signal.

Two backends stand behind one interface. With more than one job on a perl
with ithreads the workers are threads, loaded at C<start> and not before, so
a perl without them compiles this module and a program that asks for one job
never pays for the thread modules. Otherwise the same C<submit>, C<next> and
C<join> run every task in this interpreter, one at a time, in the order
submitted -- through the very code the worker runs, so the two backends cannot
differ. A task is a solve by the engine named at construction, or a task of
another kind given to the handler registered for it (the distribution deals a
level's deadlock patterns out this way, to the pool that will race its modes:
two pools in one process deadlock).

=head1 THE RACE SIGNAL

One shared hash, label to true. A worker that solves a level sets it; the
workers still running that same level notice at their next checkpoint and stop
with the reason C<IGNORE>, which is not a result and should be dropped. The
engine reads it through its own C<$RACE_FLAG> and C<$RACE_GID>, which this
module sets inside each worker (and before each task in the serial backend);
the engine is named at construction, so a caller can race any package that has
Firstbet's C<solve>.

=cut

# new(jobs => N, engine => PACKAGE, winner => 1, handlers => {kind => CODE}, serial => 0)
sub new ($class, %arg) {
    my $self = {
        'jobs'   => $arg{'jobs'}   // 1,
        'engine' => $arg{'engine'} // 'Games::Sokoban::Solver::Portfolio',

        # winner => 0 turns the race off: no mode is told to stop when another
        # solves the level, so every submitted (level, mode) really runs. That
        # is a MATRIX, not a race -- slower by definition, and the only way to
        # learn which modes can solve a level rather than which got there first.
        'winner'   => $arg{'winner'}   // 1,
        'handlers' => $arg{'handlers'} // {},
        'serial'   => $arg{'serial'}   // 0,
        'threads'  => 0,       # 1 once start() has made threads
        'queue'    => [],      # the serial backend's tasks
        'in'       => undef,
        'out'      => undef,
        'live'     => 0,       # workers still running (threads) or 1 while the serial pool is open
        'closed'   => 0,
        'solved'   => undef,
    };
    Carp::croak('Race: jobs must be at least 1') if $self->{'jobs'} < 1;
    Carp::croak('Race: handlers must be a hash of kind => code')
        if ref $self->{'handlers'} ne 'HASH'
        or grep {ref $_ ne 'CODE'} values %{ $self->{'handlers'} };
    Carp::croak("Race: 'solve' is the kind of an ordinary task and cannot be a handler") if $self->{'handlers'}{'solve'};
    return bless $self, $class;
} ## end sub new

=head2 start

    $race->start;

Make the workers: threads when C<jobs> is above one, this perl has ithreads
and the caller did not ask for C<serial>; otherwise the serial backend, which
runs every task in this interpreter when a result is asked for. Dies if the
engine is not loaded (the workers get only what is loaded now).

=cut

sub start ($self) {
    Carp::croak('Race: already started') if $self->{'live'};
    my $engine = $self->{'engine'};
    Carp::croak("Race: engine $engine is not loaded, or has no solve() -- "
            . 'load it BEFORE start(), the workers only get what is loaded now')
        unless $engine->can('solve');
    my $threaded = $self->{'jobs'} > 1 && !$self->{'serial'} && $Config::Config{'useithreads'};
    unless ($threaded) {
        my %solved;
        $self->{'solved'} = \%solved;
        $self->{'live'}   = 1;
        $self->{'jobs'}   = 1;          # whatever was asked: one task at a time is what runs
        return $self;
    }

    # THE ORDER OF LOADING MATTERS: threads::shared loaded before threads makes
    # share() a silent no-op, and the race signal would then be a private hash
    # in every worker -- every mode running its budget out on a solved level.
    Carp::croak('Race: threads::shared or Thread::Queue was loaded before threads -- '
            . 'in that order share() does nothing and the race signal is lost')
        if (($INC{'threads/shared.pm'} or $INC{'Thread/Queue.pm'}) and !$INC{'threads.pm'});
    require threads;
    require threads::shared;
    require Thread::Queue;
    my %solved;
    threads::shared::share(\%solved);
    $self->{'solved'}  = \%solved;
    $self->{'in'}      = Thread::Queue->new;
    $self->{'out'}     = Thread::Queue->new;
    $self->{'threads'} = 1;
    my ($in, $out) = @{$self}{ 'in', 'out' };
    my $winner   = $self->{'winner'};
    my $handlers = $self->{'handlers'};
    my $worker   = sub {
        no strict 'refs';
        ${"${engine}::RACE_FLAG"} = \%solved;
        my $tid = threads->tid;
        while (defined(my $task = $in->dequeue)) {
            $out->enqueue($_) for _run($engine, $handlers, $winner, \%solved, $tid, $task);
        }
        $out->enqueue(['DONE']);
    };
    threads->create($worker) for 1 .. $self->{'jobs'};

    # A worker that was never made posts no DONE, and next() would then wait for
    # it for ever after the last result.
    my $made = threads->list;
    Carp::croak("Race: only $made of $self->{'jobs'} worker threads could be created")
        if $made < $self->{'jobs'};
    $self->{'live'} = $self->{'jobs'};
    return $self;
} ## end sub start

# ONE TASK, RUN: the worker's body, and the serial backend's -- the same code,
# so the two backends cannot differ. Returns the raw result rows (a list task
# gives one per mode).
sub _run ($engine, $handlers, $winner, $solved, $tid, $task) {
    my ($kind, $label, @rest) = @$task;
    if ($kind ne 'solve') {
        my $started = Time::HiRes::time();
        my @r       = eval {$handlers->{$kind}->(@rest)};
        my $wall    = Time::HiRes::time() - $started;
        return (['TASK', $kind, $label, ($@ ? "$@" : q{}), $wall, $started, $tid, [@r]]);
    }
    my ($mode, $blob, $lim, $ctl) = @rest;
    my @rows;
    no strict 'refs';

    # A task carries EITHER one mode or a list of them. The list is one level's
    # modes run inside ONE worker, in the given order, for an engine that keeps
    # something per level and can only reuse it if the same interpreter sees the
    # modes in sequence. Each attempt still reports its own row.
    for my $m (ref $mode eq 'ARRAY' ? @$mode : $mode) {

        # free skip: another mode won this level before this one started
        if ($winner && $solved->{$label}) {
            push @rows, [$label, $m, 'IGNORE', q{}, 0, '0.000000', q{}, q{}, 0, Time::HiRes::time(), $tid];
            next;
        }
        ${"${engine}::RACE_GID"} = $label;
        ${"${engine}::CTL"}      = $ctl;     # what the caller tells the engine about THIS task (see Portfolio)

        # THE WORKER'S OWN CLOCK around the call. The engines do not time the
        # same thing -- Firstbet and FirstBack start their clock after the level
        # is loaded, Festival before, Fest between the two, none counts its
        # teardown -- so `cas` cannot compare them. This does: one clock, the
        # whole call, every engine.
        my ($reason, $path, $cas, $nseen);
        my $started = Time::HiRes::time();
        my $ok      = eval {
            ($reason, $path, $cas, $nseen) = &{"${engine}::solve"}($label, $blob, $lim, $m);
            1;
        };
        my $wall = Time::HiRes::time() - $started;
        $wall = 0.000001 if $wall < 0.000001;    # a clock corrected by the system can run backwards for a tick

        # a die in one level must not take the worker down with it: it is
        # reported like any other outcome and the pool carries on
        unless ($ok) {
            push @rows, [$label, $m, 'DIE', q{}, 0, '0.000000', "$@", q{}, $wall, $started, $tid];
            next;
        }
        $path = q{} unless defined $path;
        if ($reason eq 'SOLVED' && length $path) {
            $solved->{$label} = 1 if $winner;    # tell the losers of THIS level to stop -- unless this is a matrix
        }
        else {$path = q{}}

        # Why the engine stopped, when it cares to say ($LastFail: Festival and
        # Fest keep one, the other two do not).
        push @rows,
            [
                $label, $m, $reason, $path,
                $nseen // 0,
                sprintf('%.6f', $cas // 0),
                q{},   ${"${engine}::LastFail"} // q{},
                $wall, $started, $tid
            ];
    } ## end for my $m (ref $mode eq...)
    return @rows;
} ## end sub _run

=head2 submit

    $race->submit($label, $mode, $blob, $limit, \%ctl);

Hand one level's solve to the pool. C<$label> is the integer the engine is
told the level by (and the key of the race signal), C<$mode> one mode name or
an ARRAY reference of them (run inside ONE worker, in order, stopping once the
level is solved), C<$blob> what the engine takes for that mode, C<$limit> its
seconds, C<\%ctl> optional: a hash the engine face finds in its C<$CTL> for
this task alone (Portfolio reads C<blok_replaces> from it).

=cut

sub submit ($self, $label, $mode, $blob, $limit, $ctl = undef) {
    $self->_enqueue(['solve', $label, $mode, $blob, $limit, $ctl]);
    return;
}

=head2 submit_task

    $race->submit_task($kind, $label, @payload);

Hand the pool a task of another kind: the handler registered for C<$kind> at
construction is called with C<@payload> and its return values come back in the
result's C<payload>. Everything travels as plain data (the threads share
nothing), so the payload and the result must be scalars and references to
plain structures.

=cut

sub submit_task ($self, $kind, $label, @payload) {
    Carp::croak("Race: no handler for tasks of kind '$kind'") unless $self->{'handlers'}{$kind};
    $self->_enqueue([$kind, $label, @payload]);
    return;
}

sub _enqueue ($self, $task) {
    Carp::croak('Race: submit() before start()') unless $self->{'live'};
    Carp::croak('Race: submit() after close()') if $self->{'closed'};
    if   ($self->{'threads'}) {$self->{'in'}->enqueue($task)}
    else                      {push @{ $self->{'queue'} }, $task}
    return;
}

=head2 close

    $race->close;

Say that no more work is coming. Each worker finishes what it has and ends.
Results already in flight still arrive through C<next>.

=cut

sub close ($self) {
    return if $self->{'closed'};
    $self->{'in'}->enqueue(undef) for ($self->{'threads'} ? 1 .. $self->{'jobs'} : ());
    $self->{'closed'} = 1;
    return;
}

=head2 next

    while (my $r = $race->next) { ... }

The next result, as a hash reference, or undef once every worker has ended
(in the serial backend: once the pool is closed and the queue is empty).

A solve's result:

    kind label mode reason path sollen pushes nseen cas fail wall started tid

C<kind> is C<solve>. C<cas> is the time the ENGINE reports, and the engines do
not time the same thing. C<wall> is this module's own measurement of the whole
call, in seconds, C<started> the moment it began (epoch, fractional) and C<tid>
the worker thread that ran it (0 in the serial backend). C<reason> is whatever
the engine returned, plus two of this module's own: C<IGNORE> for a level
another mode had already won, and C<DIE> for a solve that threw -- its message
is in C<error>. C<fail> is the engine's own account of why it stopped
(C<$LastFail>), or the empty string.

A task's result has C<kind> (the handler's), C<label>, C<payload> (an ARRAY
reference of what the handler returned), C<wall>, C<started>, C<tid>, and
C<error> when the handler died.

=cut

sub _result ($r) {
    if ($r->[0] eq 'TASK') {
        my (undef, $kind, $label, $err, $wall, $started, $tid, $payload) = @$r;
        return {
            'kind'    => $kind,
            'label'   => $label,
            'payload' => $payload,
            'wall'    => $wall,
            'started' => $started,
            'tid'     => $tid,
            (length $err ? ('error' => $err) : ()),
        };
    }
    my ($label, $mode, $reason, $path, $nseen, $cas, $err, $fail, $wall, $started, $tid) = @$r;
    return {
        'kind'    => 'solve',
        'label'   => $label,
        'mode'    => $mode,
        'reason'  => $reason,
        'path'    => $path,
        'sollen'  => length $path,
        'pushes'  => ($path =~ tr/DLRU//),
        'nseen'   => $nseen,
        'cas'     => $cas,
        'fail'    => $fail,
        'wall'    => $wall,
        'started' => $started,
        'tid'     => $tid,
        (length $err ? ('error' => $err) : ()),
    };
} ## end sub _result

# The serial backend: the next queued task run here and now, its rows kept for
# the calls that follow (a list task gives several).
sub _serial_next ($self) {
    $self->{'pending'} //= [];
    unless (@{ $self->{'pending'} }) {
        my $task = shift @{ $self->{'queue'} };
        unless ($task) {
            return undef if $self->{'closed'};
            return 0;    # nothing queued and the pool is open: the caller may submit more
        }
        no strict 'refs';
        my $engine = $self->{'engine'};
        ${"${engine}::RACE_FLAG"} = $self->{'solved'};
        push @{ $self->{'pending'} }, _run($engine, $self->{'handlers'}, $self->{'winner'}, $self->{'solved'}, 0, $task);
    }
    return _result(shift @{ $self->{'pending'} });
} ## end sub _serial_next

sub next ($self) {
    return undef unless $self->{'live'};
    unless ($self->{'threads'}) {
        my $r = $self->_serial_next;
        Carp::croak('Race: next() on an open serial pool with nothing queued -- submit or close first') if defined $r and !ref $r;
        return $r;
    }
    while (1) {
        my $r = $self->{'out'}->dequeue;
        if ($r->[0] eq 'DONE') {
            return undef unless --$self->{'live'};
            next;
        }
        return _result($r);
    }
} ## end sub next

=head2 next_timed

    while (defined(my $r = $race->next_timed(60))) {
        unless (ref $r) { ...say what is going on...; next }
        ...
    }

The same as C<next>, except that it gives up waiting after C<$secs> and returns
B<0> instead of a result. Three outcomes, and the caller has to tell them apart:
a hash reference is a result, C<0> means nothing has finished yet and the pool
is still alive, and C<undef> means every worker has ended.

In the serial backend there is nothing to wait for: a queued task is run now
(for as long as it takes -- its own limit, not C<$secs>) and its result
returned, C<0> comes back when nothing is queued and the pool is still open,
C<undef> once it is closed and drained.

B<A wait shorter than a second is raised to one>, and that is not tidiness.
C<Thread::Queue::dequeue_timed> turns the wait into an absolute deadline against
a whole-second clock, so a fractional timeout can be in the past before it is
waited on -- a caller passing half a second would get a busy loop, not a slow
poll (measured in the Sokoban project: 232 098 turns in three seconds).

=cut

sub next_timed ($self, $secs) {
    return undef               unless $self->{'live'};
    return $self->_serial_next unless $self->{'threads'};
    $secs = 1 if $secs < 1;    # see the POD: a fractional wait is no wait at all
    while (1) {
        my $t0 = Time::HiRes::time();
        my $r  = $self->{'out'}->dequeue_timed($secs);
        unless (defined $r) {

            # AND THE REST OF THE WAIT IS MADE UP -- LISTENING. The whole-second
            # clock bites at a whole-second timeout too, now and then: the wait
            # can come back at once. The queue is asked every fiftieth of a
            # second until the time is really up, so a result is still seen at
            # once and a poll loop is still a poll loop.
            my $until = $t0 + $secs;
            while (Time::HiRes::time() < $until) {
                $r = $self->{'out'}->dequeue_nb;
                last if defined $r;
                Time::HiRes::sleep(0.02);
            }
            return 0 unless defined $r;
        } ## end unless (defined $r)
        if ($r->[0] eq 'DONE') {
            return undef unless --$self->{'live'};
            next;
        }
        return _result($r);
    } ## end while (1)
} ## end sub next_timed

=head2 join

    $race->join;

Wait for the workers and clean up. Call it from the main thread and only after
C<next> has run dry: a file a worker opened stays locked by the operating system
until its thread is gone, so anything that has to be deleted -- a BerkeleyDB
environment, for one -- can only be deleted after this. Nothing to do in the
serial backend.

=cut

sub join ($self) {
    if ($self->{'threads'}) {$_->join for threads->list}
    $self->{'live'} = 0;
    return;
}

=head2 solved

    my $won = $race->solved($label);

Whether some mode has already won that level.

=cut

sub solved ($self, $label) {
    return $self->{'solved'} && $self->{'solved'}{$label} ? 1 : 0;
}

=head2 stop

    $race->stop($label);

Tell every worker still on that level to give up. It raises the same shared
flag a win raises, so nothing new has to be watched for: the engines test it
at their own checkpoint -- once a second in the Firstbet family -- and come
back with C<IGNORE>. It exists for the interrupt: a caller that raises this on
Ctrl+C gets its results back within about a second and can tidy up.

=cut

sub stop ($self, $label) {
    $self->{'solved'}{$label} = 1 if $self->{'solved'};
    return;
}

=head2 threaded, jobs

    my $on = $race->threaded;
    my $n  = $race->jobs;

Whether the started pool runs on threads (1) or in this interpreter (0), and
how many tasks it runs at once (1 in the serial backend).

=cut

sub threaded ($self) {return $self->{'threads'} ? 1 : 0}
sub jobs     ($self) {return $self->{'jobs'}}
1;
__END__

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
