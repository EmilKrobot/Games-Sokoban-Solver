package Games::Sokoban::Solver;

# THE FACADE: one level from its text to its solution, the way the program
# bin/soko-solver.pl does it and the way a program of your own can.
#
# The chain, in the order it runs:
#   Level      the text of a level -> digits (code0 as drawn, code1 reduced to
#              what the player can reach), with every refusal of a level that
#              is none
#   Code       the reduction: outer walls, unreachable floor, dead-end corridors
#              -- and the FORCED OPENING those corridors give (firststep), the
#              letters every solution of the reduced level must be preceded by
#              to play on the level as drawn
#   Parser     the analysis the first-solution engines Firstbet and FirstBack
#              take; its deadlock patterns (bloks) are computed here, under a
#              budget, by the Finder -- serially, or by the pool that will race
#              the modes (one pool: two in one process deadlock)
#   Festival::Analysis, Fest::Analysis   what the other two engines take
#   Race + Portfolio   the race of up to 27 modes of four engines, the first to
#              solve the level winning, the others told to stop
#   Optimal    the search for the shortest solution, seeded by the winner,
#              and where it can, its proof
#   Path, Replay   the finished path written again from its pushes with the
#              opening in front, and replayed on the level as drawn by a second
#              reading that shares no code with the first
#
# Nothing here prints: every function returns data, and what a caller wants to
# hear about as it happens comes through callbacks (on_note, on_answer,
# on_improved). Every refusal is a death with one sentence beginning REFUSED:;
# an inner fault (a path that will not replay) one beginning INTERNAL:.
#
# The engines are told the level by an integer label: the first 48 bits of the
# MD5 of code1 -- stable over runs and files, so the BerkeleyDB twins find the
# stores a TIMEOUT left for the same level, and a number, because every engine
# prints it with %d.
#
# Lineage: the Sokoban project's drivers app/first/wave_batch.pl (the feeding
# of the pool by kind, one level in hand), app/base/add_game.pl (the chain of
# one level) and app/best/solve_one.pl (the call of the proof).

use v5.42;
use warnings FATAL => 'uninitialized';
no warnings 'once';
use Carp ();
use Digest::MD5 ();
use Scalar::Util ();
use Time::HiRes ();
use Games::Sokoban::Solver::Level     ();
use Games::Sokoban::Solver::Code      ();
use Games::Sokoban::Solver::Finder    ();
use Games::Sokoban::Solver::Parser    ();
use Games::Sokoban::Solver::Festival::Analysis ();
use Games::Sokoban::Solver::Fest::Analysis     ();
use Games::Sokoban::Solver::Portfolio ();
use Games::Sokoban::Solver::Race      ();
use Games::Sokoban::Solver::Optimal   ();
use Games::Sokoban::Solver::Path      ();
use Games::Sokoban::Solver::Replay    ();
use Games::Sokoban::Solver::Memory    ();

our $VERSION = '0.01';

# The four engines and the optimal solver, by the names the run control is set
# on; the twins join the list when a pool is made with BerkeleyDB.
my @ENGINES = map { "Games::Sokoban::Solver::$_" } 'Firstbet', 'FirstBack', 'Festival', 'Fest';

# Results of a pool that arrived while somebody was waiting for others (the
# blok source collecting its tasks while a race's late answers come in, or the
# other way round), kept for the one who wants them. Keyed by the pool.
my %Aside;

=head1 NAME

Games::Sokoban::Solver - solve Sokoban levels: a first solution by a race of search modes, then the shortest one

=head1 SYNOPSIS

    use Games::Sokoban::Solver ();

    my @levels = Games::Sokoban::Solver::read_levels($text_of_a_file);
    my $r = Games::Sokoban::Solver::solve_level('rows' => $levels[0]{'rows'}, 'time' => 60, 'optimal' => 60);
    say $r->{'status'};    # SOLVED, UNSOLVED or REFUSED
    say $r->{'path'};      # the solution in uUrRlLdD letters, for the level as drawn

    # the same, piece by piece, with a pool of workers shared over many levels
    my $pool = Games::Sokoban::Solver::pool('jobs' => 4);
    for my $level (@levels) {
        my $p     = Games::Sokoban::Solver::prepare('rows' => $level->{'rows'}, 'pool' => $pool, 'lazy' => 1);
        my $first = Games::Sokoban::Solver::first_solution('prepared' => $p, 'pool' => $pool, 'time' => 60);
        next unless $first->{'reason'} eq 'SOLVED';
        my $best  = Games::Sokoban::Solver::best_solution('prepared' => $p, 'seed' => $first->{'path'}, 'time' => 60);
        say Games::Sokoban::Solver::full_path($p, $best->{'path'});
    }
    $pool->close;
    $pool->join;

From the command line:

    soko-solver.pl levels.xsb

=head1 DESCRIPTION

This distribution is the solver pipeline of the Sokoban project of Jiri Broz,
packaged for use outside that project. A level in the standard text format is
read, reduced to what matters for the search, analysed, and then solved
twice: first by a race of up to twenty-seven search modes of four engines
(Firstbet, FirstBack, Festival, Fest), the first to find a solution winning,
then by an optimal solver that looks for the shortest solution and, where it
can, proves it.

The functions below are the facade: they return data and print nothing; a
caller that wants to follow the work gives callbacks. L</solve_level> runs the
whole chain on one level; the others are its pieces, for a caller that shares
one pool of workers over many levels, as the program does.

=head2 Two things to know before reading solutions

B<The forced opening.> A dead-end corridor with one entrance has exactly one
way to play; the reduction walls it off and keeps the letters that empty it as
the C<firststep>. Every solution of the reduced level must be preceded by
those letters to play on the level as drawn, and L</full_path> does exactly
that. The engines' own paths (in C<first> and C<best>) are for the reduced
level.

B<The deadlock patterns are computed under a budget.> The Sokoban project
spent a year of processor time on its table of patterns; here the patterns of a
level are found when the level is solved, within C<blok_budget> seconds (30 by
default, calibrated: it recovers 57-99 % of the table depending on the size of
the level), and a search with fewer patterns may take another way or fail where
the project's campaign succeeded. The report in C<blok_report> says how many
patterns were done; a cut table is never wrong, only smaller.

=head1 FUNCTIONS

=head2 read_levels

    my @levels = read_levels($text);

The levels of a text (a whole file), each a hash with C<index> (from 1),
C<title> and C<rows>. See L<Games::Sokoban::Solver::Level/read>.

=cut

sub read_levels ($text) { return Games::Sokoban::Solver::Level::read($text) }

=head2 pool

    my $pool = pool('jobs' => 4, 'serial' => 0, 'max_gb' => 0, 'quiet' => 2, 'berkeley' => undef);

A started L<Games::Sokoban::Solver::Race> pool with the Portfolio as its
engine and the Finder's C<blok_task> as the handler of tasks of kind C<blok>,
so that the same pool deals out a level's patterns and races its modes (two
pools in one process deadlock). C<jobs> 1, or C<serial>, runs everything in
this interpreter without threads. Every engine is set quiet (C<quiet>: the
engines' C<$QUIET>, 2 = nothing, 0 = their own progress lines) and given the
memory ceiling C<max_gb> (GB of the whole machine in use, 0 = none) before the
workers are made -- they are clones of that moment, so set nothing on an
engine afterwards.

C<berkeley>, a hash C<{root => DIR, cache_gb => F}>, loads the BerkeleyDB
branch (the module must be installed) and sends Firstbet's modes to its twin
on disk, each mode with a store of its own; L</best_solution> then runs the
optimal twin when told so. Dies when the module is missing.

Close and join the pool when the work is done (C<< $pool->close; $pool->join >>).

=cut

sub pool (%opt) {
    my $jobs = $opt{'jobs'} // 1;
    for my $pkg (@ENGINES) {
        no strict 'refs';
        ${"${pkg}::QUIET"}  = $opt{'quiet'} // 2;    # Fest has none and prints nothing; the variable does no harm there
        ${"${pkg}::MAX_GB"} = $opt{'max_gb'} // 0;
    }
    $Games::Sokoban::Solver::Festival::BLOK_REPLACES //= 0;
    $Games::Sokoban::Solver::Fest::BLOK = 1;
    $Games::Sokoban::Solver::Portfolio::BERK = 0;
    if (my $berk = $opt{'berkeley'}) {
        _load_berkeley($berk);
        $Games::Sokoban::Solver::Firstbet::Berk::QUIET          = 2;
        $Games::Sokoban::Solver::Firstbet::Berk::MAX_GB         = $opt{'max_gb'} // 0;
        $Games::Sokoban::Solver::Firstbet::Berk::STORE_PER_MODE = 1;    # the modes of one level run at once
        $Games::Sokoban::Solver::Firstbet::Berk::CACHE          = _cache_bytes($berk->{'cache_gb'});
        $Games::Sokoban::Solver::Portfolio::BERK                = 1;
    }
    my $race = Games::Sokoban::Solver::Race->new(
        'jobs'     => $jobs,
        'serial'   => $opt{'serial'} // 0,
        'engine'   => 'Games::Sokoban::Solver::Portfolio',
        'handlers' => { 'blok' => \&Games::Sokoban::Solver::Finder::blok_task },
    );
    $race->start;
    return $race;
}

sub _load_berkeley ($berk) {
    Carp::croak('REFUSED: the BerkeleyDB branch needs a root directory for the stores') unless length($berk->{'root'} // '');
    eval { require BerkeleyDB; 1 } or Carp::croak('REFUSED: the BerkeleyDB module is not installed, so the search cannot go to disk');
    require Games::Sokoban::Solver::Berkeley;
    require Games::Sokoban::Solver::Firstbet::Berk;
    require Games::Sokoban::Solver::Optimal::Berk;
    $Games::Sokoban::Solver::Berkeley::ROOT = $berk->{'root'};
    return;
}

sub _cache_bytes ($gb) {
    $gb //= 0.5;
    Carp::croak("REFUSED: a BerkeleyDB pool of $gb GB: the module keeps the size in 32 bits, 3 GB is the most") if $gb > 3;
    return int($gb * 1073741824);
}

=head2 prepare

    my $p = prepare(
        'rows'        => \@rows,          # the lines of one level
        'blok_budget' => 30,              # seconds for the deadlock patterns; 0 = none, -1 = the complete table
        'fest_budget' => 120,             # seconds for the Festival analysis
        'want'        => ['game', 'fest', 'analysis'],   # which analyses to build
        'lazy'        => 0,               # 1 = fest and analysis built on demand by first_solution
        'pool'        => $pool,           # the patterns dealt out to the pool; serial without it
        'on_note'     => sub ($text) {},  # what a caller should know, as it is found out
    );

Everything a level needs before a search, in one hash:

    title index                the level's (as given in rows => $level, or '')
    code0 code1                the digits, as drawn and reduced (Level)
    w h nbox ncell             of code1
    code                       the record of the Code stage (the reduced board is code->{code})
    firststep                  the forced opening, letters ('' when none)
    solved_by_opening          1 when the opening alone solves the level: nothing to search
    label                      the integer the engines are told the level by
    game                       the Parser's analysis (a hash), game_blob what Firstbet and FirstBack take
    fest_blob analysis_blob    what Festival and Fest take (undef when not built)
    build                      the builders of the two, when lazy (first_solution calls them)
    failed                     {fest => why, analysis => why} where an analysis died
    blok_report                [[pattern, kmax, k_done, candidates, seconds], ...]
    blok_complete              1 when every pattern was done to its largest size
    fest_incomplete            [] or the fuses that fired: 'hotspots', 'envelopes'
    cost                       seconds: level code parser blok fest analysis
    notes                      every sentence on_note was given

Dies with C<REFUSED: ...> when the rows are no level, when the reduction cannot
read them, or when a goal can never receive a box. The value of C<rows> may
also be a hash as L</read_levels> returns them.

=cut

sub prepare (%opt) {
    my $level = $opt{'rows'} // Carp::croak('prepare: rows are needed');
    my ($rows, $title, $index) = ref $level eq 'HASH' ? ($level->{'rows'}, $level->{'title'} // '', $level->{'index'} // 0) : ($level, '', 0);
    my @notes;
    my $note = sub ($text) { push @notes, $text; $opt{'on_note'}->($text) if $opt{'on_note'}; return };
    my %cost;
    my $t0 = Time::HiRes::time();

    my ($code0, $code1, $info) = Games::Sokoban::Solver::Level::normalize($rows);
    $note->($_) for @{ $info->{'notes'} };
    $cost{'level'} = Time::HiRes::time() - $t0;

    $t0 = Time::HiRes::time();
    my %code = Games::Sokoban::Solver::Code::prepare($code1);
    $cost{'code'} = Time::HiRes::time() - $t0;
    my %p = (
        'title'             => $title,
        'index'             => $index,
        'code0'             => $code0,
        'code1'             => $code1,
        'w'                 => $info->{'w'},
        'h'                 => $info->{'h'},
        'nbox'              => $info->{'nbox'},
        'ncell'             => $info->{'ncell'},
        'code'              => \%code,
        'firststep'         => $code{'firststep'},
        'solved_by_opening' => (@{ $code{'baggage'} } ? 0 : 1),
        'label'             => label($code1),
        'fest_blob'         => undef,
        'analysis_blob'     => undef,
        'build'             => {},
        'failed'            => {},
        'blok_report'       => [],
        'blok_complete'     => 0,
        'fest_incomplete'   => [],
        'cost'              => \%cost,
        'notes'             => \@notes,
    );
    if ($p{'solved_by_opening'}) {
        $note->('the forced opening alone solves the level: nothing to search');
        return \%p;
    }
    $note->(sprintf 'the forced opening has %d letters', length $code{'firststep'}) if length $code{'firststep'};

    # The Parser, its patterns from the pool or serially under the budget.
    my $budget = $opt{'blok_budget'} // 30;
    $budget = undef if $budget < 0;    # -1: the complete table
    my %report;
    my %parse = ('blok_budget' => $budget, 'report' => \%report);
    $parse{'blok_source'} = _pool_blok_source($opt{'pool'}, $p{'label'}) if $opt{'pool'} and (!defined $budget or $budget > 0);
    $t0 = Time::HiRes::time();
    my %game = Games::Sokoban::Solver::Parser::parse(\%code, %parse);
    $p{'game'}          = \%game;
    $p{'game_blob'}     = Games::Sokoban::Solver::Parser::blob(\%game);
    $p{'blok_report'}   = $report{'blok'} // [];
    $p{'blok_complete'} = $report{'blok_complete'} // 0;
    $cost{'blok'}       = $report{'seconds'}{'blok'} // 0;
    $cost{'parser'}     = Time::HiRes::time() - $t0 - $cost{'blok'};
    {
        my $rows = $p{'blok_report'};
        my $cut  = grep { $_->[2] < $_->[1] } @$rows;
        $note->(sprintf '%d patterns, %d complete, %d cut by the budget of %s s', scalar @$rows, @$rows - $cut, $cut, $budget // 'no') if @$rows;
    }

    # The two other analyses: now, or as builders for first_solution.
    my %want = map { $_ => 1 } @{ $opt{'want'} // ['game', 'fest', 'analysis'] };
    my $fest_budget = $opt{'fest_budget'} // 120;
    $p{'build'}{'fest'} = sub {
        my $fest = Games::Sokoban::Solver::Festival::Analysis::parse($code{'code'}, $fest_budget);
        Games::Sokoban::Solver::Festival::Analysis::with_blok($fest, $game{'blok'});
        $p{'fest_incomplete'} = [grep { $fest->{"${_}_incomplete"} } 'hotspots', 'envelopes'];
        return Games::Sokoban::Solver::Festival::Analysis::freeze($fest);
    } if $want{'fest'};
    $p{'build'}{'analysis'} = sub {
        return Games::Sokoban::Solver::Fest::Analysis::analysis_record(Games::Sokoban::Solver::Fest::Analysis::prepare(\%game));
    } if $want{'analysis'};
    unless ($opt{'lazy'}) {
        build(\%p, $_, $note) for grep { $p{'build'}{$_} } 'fest', 'analysis';
    }
    return \%p;
}

=head2 build

    my $blob = build($p, 'fest');       # or 'analysis'

Build one of the two deferred analyses of a prepared level (C<lazy>): the blob
goes into C<fest_blob> / C<analysis_blob>, its seconds into C<cost>, and an
analysis that dies is noted in C<failed> and returns undef -- the level is not
lost, only that engine's modes. Nothing to do when it is built or failed
already.

=cut

sub build ($p, $what, $note = undef) {
    my $builder = delete $p->{'build'}{$what};
    return $p->{"${what}_blob"} unless $builder;
    my $t0   = Time::HiRes::time();
    my $blob = eval { $builder->() };
    $p->{'cost'}{$what} = Time::HiRes::time() - $t0;
    unless (defined $blob) {
        my $why = (split /\n/, "$@")[0] // 'died without a word';
        $p->{'failed'}{$what} = $why;
        my $text = ($what eq 'fest' ? 'the Festival analysis' : 'the Fest analysis') . " failed, its modes are left out: $why";
        push @{ $p->{'notes'} }, $text;
        $note->($text) if $note;
        return undef;
    }
    $p->{"${what}_blob"} = $blob;
    if ($what eq 'fest' and @{ $p->{'fest_incomplete'} }) {
        my $text = 'the Festival analysis ran out of budget: ' . join(' and ', @{ $p->{'fest_incomplete'} }) . ' incomplete';
        push @{ $p->{'notes'} }, $text;
        $note->($text) if $note;
    }
    return $blob;
}

=head2 label

    my $n = label($code1);

The integer the engines are told a level by: the first 48 bits of the MD5 of
its reduced digits.

=cut

sub label ($code1) { return unpack('Q>', "\0\0" . substr(Digest::MD5::md5($code1), 0, 6)) }

# THE BLOK SOURCE OF A POOL: the Parser's patterns dealt out as tasks of kind
# blok, in the two passes Finder::blok_table makes serially -- every pattern to
# size 3 first (cheap everywhere, the small sets prune the most), then the rest
# -- under one absolute deadline. A task cut by the deadline returns what it
# has; after the deadline no second pass is started. Results of other kinds that
# arrive meanwhile are put aside for first_solution.
sub _pool_blok_source ($race, $label) {
    return sub ($patlist, %opt) {
        my $nbox     = $opt{'nbox'};
        my $deadline = $opt{'deadline'};
        my %kmax     = map {
            my $free = tr/03//;
            $_ => ($nbox - 1 < $free ? $nbox - 1 : $free)
        } keys %$patlist;
        my @order = sort { $kmax{$a} <=> $kmax{$b} or $a cmp $b } keys %$patlist;
        my (%bloks, %row);
        $row{$_} = [$_, $kmax{$_}, 0, 0, 0] for @order;

        for my $pass ([1, 3], [4, undef]) {
            my ($from, $to) = @$pass;
            last if defined $deadline and Time::HiRes::time() > $deadline;
            my (%waiting, %target);
            for my $p (@order) {
                my $kmax = $to // $kmax{$p};
                $kmax = $kmax{$p} if $kmax > $kmax{$p};
                next if $kmax < $from;
                $race->submit_task('blok', $label, $p, $kmax, $from, $bloks{$p} // '', $deadline);
                $waiting{$p} = 1;
                $target{$p}  = $kmax;
            }
            while (%waiting) {
                my $r = _take($race, 1, 'blok');
                Carp::confess('the pool ended while patterns were in flight') unless defined $r;
                next unless ref $r;
                Carp::croak("INTERNAL: a blok task died: $r->{'error'}") if $r->{'error'};
                my ($pattern, $k_done, $string, $candidates, $seconds) = @{ $r->{'payload'}[0] };
                delete $waiting{$pattern};
                $bloks{$pattern} = $string;
                $row{$pattern}[2] = $k_done;
                $row{$pattern}[3] += $candidates;
                $row{$pattern}[4] += $seconds;
            }
            last if grep { $row{$_}[2] < $target{$_} } keys %target;    # something was cut: the deadline is past
        }
        $bloks{$_} //= '' for @order;
        return (\%bloks, [map { $row{$_} } @order]);
    };
}

# The next result of the pool for the one asking: the ones put aside for it
# first, then the pool's own, those of another kind (or another level, when
# $label is given) put aside. Returns a hash, 0 (nothing yet) or undef (the
# pool has ended), as next_timed does.
sub _take ($race, $secs, $kind, $label = undef) {
    my $aside = $Aside{ Scalar::Util::refaddr($race) } //= [];
    for my $i (0 .. $#$aside) {
        next unless $aside->[$i]{'kind'} eq $kind and (!defined $label or $aside->[$i]{'label'} == $label);
        return splice @$aside, $i, 1;
    }
    while (1) {
        my $r = $race->next_timed($secs);
        return $r unless ref $r;
        return $r if $r->{'kind'} eq $kind and (!defined $label or $r->{'label'} == $label);
        push @$aside, $r;
    }
}

=head2 first_solution

    my $first = first_solution(
        'prepared'  => $p,
        'pool'      => $pool,            # or jobs => N for a pool of this call's own
        'time'      => 60,               # seconds for one mode (ORDER has its own 30)
        'modes'     => [Games::Sokoban::Solver::Portfolio::race_order()],
        'caps'      => { 'pull' => 1, 'forward' => 3 },   # modes of a kind in flight at once
        'hold_gb'   => 0,                # no counted mode starts while the machine holds more (0 = off)
        'blok'      => undef,            # Festival with the blok table standing in for its battery: undef = when complete
        'on_answer' => sub ($r) {},      # every answer of the pool as it comes (IGNORE included)
        'on_note'   => sub ($text) {},
    );

The race: the modes in the given order, each with C<time> seconds (or its
own limit), as many at once as the pool has workers and the caps allow, the
first SOLVED stopping the rest. An analysis still to build (C<lazy>) is built
when the first mode that needs it comes up. Returns

    reason    SOLVED, or UNSOLVED when no mode solved the level
    path mode seconds pushes sollen    of the winner (the path is for the reduced level)
    answers   every answer that said something (not IGNORE), in order of arrival
    died      the modes whose engine died, with the message

=cut

sub first_solution (%opt) {
    my $p    = $opt{'prepared'} // Carp::croak('first_solution: a prepared level is needed');
    my $note = sub ($text) { push @{ $p->{'notes'} }, $text; $opt{'on_note'}->($text) if $opt{'on_note'}; return };
    my %r    = ('reason' => 'UNSOLVED', 'answers' => [], 'died' => []);
    return \%r if $p->{'solved_by_opening'};

    my $own  = !$opt{'pool'};
    my $race = $opt{'pool'} // pool('jobs' => $opt{'jobs'} // 1, 'max_gb' => $opt{'max_gb'});
    my $jobs = $race->threaded ? $race->jobs : 1;
    my $time = $opt{'time'} // 60;
    my %cap  = %{ $opt{'caps'} // { Games::Sokoban::Solver::Portfolio::default_caps() } };
    my $hold = $opt{'hold_gb'} // 0;
    my $label = $p->{'label'};
    my @pending = @{ $opt{'modes'} // [Games::Sokoban::Solver::Portfolio::race_order()] };
    my %kind    = map { $_ => Games::Sokoban::Solver::Portfolio::kind_of($_) } @pending;
    my %blob_of = ('game' => 'game_blob', 'fest' => 'fest_blob', 'analysis' => 'analysis_blob');
    my (%flying, $inflight, $won, $waited);
    $inflight = 0;

    while (1) {

        # The level was stopped from outside (Race::stop, the program's Ctrl+C):
        # what has not started does not start.
        @pending = () if @pending and $race->solved($label);

        # Feed: the first waiting mode whose kind has room and whose blob exists
        # or can be built now.
        my $light_only = ($hold > 0 and Games::Sokoban::Solver::Memory::used_gb() > $hold) ? 1 : 0;
        FEED: while ($inflight < $jobs and @pending) {
            my $ix;
            for my $i (0 .. $#pending) {
                my $k = $kind{ $pending[$i] };
                next if $k ne 'light' and ($light_only or ($flying{$k} // 0) >= ($cap{$k} // 1e9));
                $ix = $i;
                last;
            }
            last FEED unless defined $ix;
            my ($mode) = splice @pending, $ix, 1;
            my $what = Games::Sokoban::Solver::Portfolio::blob_for($mode);
            my $blob = $p->{ $blob_of{$what} } // build($p, $what eq 'game' ? 'game' : $what, $note);
            unless (defined $blob) {
                my @left = grep { Games::Sokoban::Solver::Portfolio::blob_for($_) ne $what } @pending;
                my $more = @pending - @left;
                $note->(sprintf '%s left out: no %s analysis%s', $mode . ($more ? " and $more more modes" : ''), $what,
                    ($p->{'failed'}{$what} ? " (it failed: $p->{'failed'}{$what})" : ''));
                @pending = @left;
                next FEED;
            }
            my $limit = Games::Sokoban::Solver::Portfolio::own_limit($mode) // $time;
            my %ctl   = ('blok_replaces' => ($opt{'blok'} // ($p->{'blok_complete'} ? 1 : 0)), 'blok' => 1);
            $race->submit($label, $mode, $blob, $limit, \%ctl);
            ++$inflight;
            ++$flying{ $kind{$mode} };
        }
        last unless $inflight or @pending;

        # Nothing in flight and modes waiting: only the memory hold can do that.
        unless ($inflight) {
            $note->(sprintf 'nothing may start: the machine holds %.1f GB, over the hold of %g', Games::Sokoban::Solver::Memory::used_gb(), $hold)
                unless $waited++;
            Time::HiRes::sleep(1);
            next;
        }

        my $a = _take($race, 1, 'solve', $label);
        Carp::confess('the pool ended with modes in flight') unless defined $a;
        next unless ref $a;
        --$inflight;
        --$flying{ $kind{ $a->{'mode'} } } if $kind{ $a->{'mode'} };
        $opt{'on_answer'}->($a) if $opt{'on_answer'};
        my $reason = $a->{'reason'};
        if ($reason eq 'DIE') {
            push @{ $r{'died'} }, { 'mode' => $a->{'mode'}, 'error' => $a->{'error'} };
            $note->("the engine of $a->{'mode'} died: " . (split /\n/, $a->{'error'})[0]);
            next;
        }
        next if $reason eq 'IGNORE';
        push @{ $r{'answers'} }, $a;
        if ($reason eq 'SOLVED' and !$won) {
            $won = $a;
            @pending = ();    # what has not started does not start; the running are told by the signal
        }
    }

    if ($won) {
        @r{ 'reason', 'path', 'mode', 'seconds', 'sollen', 'pushes' } = ('SOLVED', @{$won}{ 'path', 'mode', 'wall', 'sollen', 'pushes' });
    }
    if ($own) { $race->close; $race->join; delete $Aside{ Scalar::Util::refaddr($race) } }
    return \%r;
}

=head2 best_solution

    my $best = best_solution(
        'prepared'    => $p,
        'seed'        => $first->{'path'},   # the solution to better; undef = none
        'time'        => 60,                 # seconds; DIAL and ASTAR may run to twice that when the proof is near
        'mode'        => 'DIAL',             # DIAL, ASTAR or FIFO
        'band'        => 2,                  # FIFO's band, 0 = none
        'max_gb'      => 0,
        'stop'        => \%flag,             # a hash: set $flag{$p->{'label'}} = 1 to interrupt
        'on_improved' => sub ($path, $seconds) {},
        'berkeley'    => undef,              # {cache_gb => F}: the optimal twin on disk (pool() loaded the branch)
    );

The optimal solver on the reduced level, seeded by C<seed>. Returns

    reason      SOLVED (the path is proved shortest), TIMEOUT (not proved; the path is the best found,
                the seed at worst), UNSOLVABLE, IGNORE (interrupted through stop)
    status      the stop by name: SOLVED, TIMEOUT, MEMCAP, IGNORE
    path proved seconds candidates pops
    track       the improvements, as the solver recorded them

=cut

sub best_solution (%opt) {
    my $p = $opt{'prepared'} // Carp::croak('best_solution: a prepared level is needed');
    return { 'reason' => 'SOLVED', 'status' => 'SOLVED', 'path' => '', 'proved' => 1, 'seconds' => 0, 'candidates' => 0, 'pops' => 0, 'track' => [] }
        if $p->{'solved_by_opening'};
    my $mode = $opt{'mode'} // 'DIAL';
    Carp::croak("best_solution: the mode is DIAL, ASTAR or FIFO, not '$mode'") unless grep { $_ eq $mode } Games::Sokoban::Solver::Portfolio::solver_modes();
    my $pkg = 'Games::Sokoban::Solver::Optimal';
    if ($opt{'berkeley'}) {
        _load_berkeley({ 'root' => $Games::Sokoban::Solver::Berkeley::ROOT // $opt{'berkeley'}{'root'} }) unless defined &Games::Sokoban::Solver::Optimal::Berk::solve;
        $pkg = 'Games::Sokoban::Solver::Optimal::Berk';
        $Games::Sokoban::Solver::Optimal::Berk::CACHE = _cache_bytes($opt{'berkeley'}{'cache_gb'});
    }
    no strict 'refs';
    ${"${pkg}::QUIET"}       = 2;
    ${"${pkg}::LIMIT"}       = $opt{'time'} // 60;
    ${"${pkg}::MODE"}        = $mode;
    ${"${pkg}::BAND"}        = $opt{'band'} // 2;
    ${"${pkg}::MAX_GB"}      = $opt{'max_gb'} // 0;
    ${"${pkg}::RACE_FLAG"}   = $opt{'stop'};
    ${"${pkg}::RACE_GID"}    = $p->{'label'};
    ${"${pkg}::ON_IMPROVED"} = $opt{'on_improved'};
    my $seed = $opt{'seed'};
    $seed = undef if defined $seed and !length $seed;
    my ($reason, $path, $seconds, $candidates, $pops) = &{"${pkg}::solve"}($p->{'label'}, $p->{'game_blob'}, $seed);
    my $status = ${"${pkg}::LastStatus"};
    ${"${pkg}::ON_IMPROVED"} = undef;
    ${"${pkg}::RACE_FLAG"}   = undef;
    return {
        'reason'     => $reason,
        'status'     => $status,
        'path'       => $path // $seed // '',
        'proved'     => ($reason eq 'SOLVED' ? 1 : 0),
        'seconds'    => $seconds,
        'candidates' => $candidates,
        'pops'       => $pops,
        'track'      => [@{"${pkg}::Track"}],
    };
}

=head2 full_path

    my $path = full_path($p, $engine_path);

The solution for the level as drawn: the forced opening in front of the
engine's path, written again from its pushes (a shortest walk to each, the
seam between the two included) and replayed on C<code1> by a second reading
that shares no code with the first. Dies with C<INTERNAL: ...> when the path
does not play -- which no caller should ever see.

=cut

sub full_path ($p, $path) {
    my $full = eval { Games::Sokoban::Solver::Path::rebuilt(Games::Sokoban::Solver::Path::level($p->{'code1'}), 'path' => $p->{'firststep'} . ($path // '')) };
    Carp::croak('INTERNAL: the solution does not play on the level: ' . ((split /\n/, "$@")[0] // '')) unless defined $full;
    my $why = Games::Sokoban::Solver::Replay::check($p->{'code1'}, $full);
    Carp::croak("INTERNAL: the second reading refuses the solution: $why") if defined $why;
    return $full;
}

=head2 refusal

    my $sentence = refusal($@);

The one sentence of a C<REFUSED:> death: the first line, without the place in
the code that C<croak> appends (the Code stage draws the board after its
sentence; that goes too).

=cut

sub refusal ($why) {
    $why =~ s/\n.*//s;
    $why =~ s/ at \S+ line \d+\.?\s*\z//;
    return $why;
}

=head2 solve_level

    my $r = solve_level(
        'rows'    => \@rows,       # or a level hash of read_levels
        'time'    => 60,           # the race
        'optimal' => 60,           # the proof; 0 = none
        'optimal_mode' => 'DIAL', 'band' => 2,
        'blok_budget' => 30, 'fest_budget' => 120,
        'modes' => [...], 'pool' => $pool, 'jobs' => 1, 'caps' => {...}, 'hold_gb' => 0, 'max_gb' => 0, 'blok' => undef,
        'stop' => \%flag, 'berkeley' => undef,
        'on_note' => sub {}, 'on_answer' => sub {}, 'on_improved' => sub {},
    );

The whole chain on one level. Returns

    status      SOLVED, UNSOLVED or REFUSED
    reason      for REFUSED, the sentence; for UNSOLVED, what the race said
    title index
    path        the solution for the level as drawn (SOLVED only)
    moves pushes forced       of that path; forced = the letters of the opening
    proved      1 when the shortest solution was proved
    prepared first best       the three results above (first and best undef where they did not run)

=cut

sub solve_level (%opt) {
    my $level = $opt{'rows'};
    my %r = ('title' => (ref $level eq 'HASH' ? $level->{'title'} // '' : ''), 'index' => (ref $level eq 'HASH' ? $level->{'index'} // 0 : 0));
    my %pass = map { ($_, $opt{$_}) } grep { exists $opt{$_} } 'rows', 'blok_budget', 'fest_budget', 'want', 'pool', 'on_note';
    my $p = eval { prepare(%pass) };
    unless ($p) {
        my $why = "$@";
        die $why unless $why =~ /\AREFUSED:/;
        return { %r, 'status' => 'REFUSED', 'reason' => refusal($why) };
    }
    $r{'prepared'} = $p;
    %pass = map { ($_, $opt{$_}) } grep { exists $opt{$_} } 'time', 'modes', 'pool', 'jobs', 'caps', 'hold_gb', 'max_gb', 'blok', 'on_answer', 'on_note';
    my $first = first_solution(%pass, 'prepared' => $p);
    $r{'first'} = $first;
    my $path;
    if ($p->{'solved_by_opening'}) { $path = ''; $r{'proved'} = 1 }
    elsif ($first->{'reason'} ne 'SOLVED') {
        return { %r, 'status' => 'UNSOLVED', 'reason' => (@{ $first->{'died'} } ? 'an engine died: ' . $first->{'died'}[0]{'error'} : 'no mode solved the level'), 'proved' => 0 };
    }
    else {
        $path = $first->{'path'};
        $r{'proved'} = 0;
        if (($opt{'optimal'} // 60) > 0) {
            %pass = map { ($_, $opt{$_}) } grep { exists $opt{$_} } 'band', 'max_gb', 'stop', 'on_improved', 'berkeley';
            my $best = best_solution(%pass, 'prepared' => $p, 'seed' => $path, 'time' => $opt{'optimal'} // 60, 'mode' => $opt{'optimal_mode'} // 'DIAL');
            $r{'best'} = $best;
            $path = $best->{'path'} if length $best->{'path'} and length $best->{'path'} <= length $path;
            $r{'proved'} = $best->{'proved'};
        }
    }
    my $full = full_path($p, $path);
    return {
        %r,
        'status' => 'SOLVED',
        'path'   => $full,
        'moves'  => length $full,
        'pushes' => ($full =~ tr/DLRU//),
        'forced' => length $p->{'firststep'},
    };
}

1;

__END__

=head1 EXIT OF A WORKER, AND WHAT A RESULT MEANS

An engine that dies inside the pool is reported, not fatal: C<first_solution>
lists it in C<died> and goes on with the other modes; C<solve_level> says
UNSOLVED with the message when nothing else solved the level. An engine that
answers UNSOLVABLE on a level the Parser accepted is an answer like any other
here (the program is not a campaign's tripwire); it is in C<answers>.

=head1 CAVEATS

The Firstbet mode BACKWARD, and the FirstBack engine, keep state between the
levels one worker runs, so the path they return for a level may differ from
the one they return for the same level alone. Every path returned is a
solution all the same.

The engines were measured on levels of up to 400 reachable cells and 30
boxes; L</prepare> notes a level outside that range and solves it anyway.

The analysis of a level for the Festival engine has a budget that fuses two
of its parts (the hotspot table at a quarter of it, the envelopes at half) and
no limit on the rest; a very large level can take minutes there. The Fest
analysis has no budget (about five seconds on a large level).

=head1 SEE ALSO

L<Games::Sokoban::Solver::Level>, L<Games::Sokoban::Solver::Code>,
L<Games::Sokoban::Solver::Parser>, L<Games::Sokoban::Solver::Finder>,
L<Games::Sokoban::Solver::Portfolio>, L<Games::Sokoban::Solver::Race>,
L<Games::Sokoban::Solver::Optimal>, L<Games::Sokoban::Solver::Path>,
L<Games::Sokoban::Solver::Replay>, L<Games::Sokoban::Solver::Config>,
L<soko-solver.pl>.

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
