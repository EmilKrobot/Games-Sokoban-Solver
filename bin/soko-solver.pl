#!/usr/bin/env perl
# soko-solver.pl -- solve the levels of a file: a first solution by a race of
# search modes, then the shortest one. The whole program is the facade
# Games::Sokoban::Solver driven from the command line; what it adds is the
# settings (the ini file and its questions), the pool made once for the run,
# the formats of the output, the lines on STDERR, Ctrl+C and the exit status.
# Everything below __END__ is its documentation (--help prints it).
use v5.42;
use warnings FATAL => 'uninitialized';
no warnings 'once';
use Getopt::Long                      ();
use Pod::Usage                        ();
use POSIX                             ();
use Time::HiRes                       ();
use Games::Sokoban::Solver            ();
use Games::Sokoban::Solver::Config    ();
use Games::Sokoban::Solver::Portfolio ();
use Games::Sokoban::Solver::Level     ();
use Games::Sokoban::Solver::Memory    ();
our $VERSION = $Games::Sokoban::Solver::VERSION;

# --- the options -----------------------------------------------------------------
my %o = ('blok' => undef, 'band' => 2, 'format' => undef, 'out' => undef, 'level' => undef, 'modes' => undef, 'engines' => undef);
Getopt::Long::Configure('bundling', 'no_ignore_case');
Getopt::Long::GetOptions(
    \%o,                'time|limit=f',    'jobs=i',         'no-threads', 'modes=s',       'engines=s',
    'pull=i',           'forward=i',       'hold=f',         'maxgb=f',    'blok-budget=f', 'fest-budget=f',
    'blok=i',           'optimal=f',       'optimal-mode=s', 'band=i',     'berkeley=i',    'berkeley-root=s',
    'berkeley-cache=f', 'berkeley-from=f', 'ini=s',          'init',       'no-ini',        'level=s',
    'format=s',         'out=s',           'show',           'quiet|q',    'verbose|v',     'version|V',
    'help|h|?',
    )
    or Pod::Usage::pod2usage('-exitval' => 2, '-verbose' => 0);
Pod::Usage::pod2usage('-exitval' => 0, '-verbose' => 2, '-noperldoc' => 1) if $o{'help'};
if ($o{'version'}) {say "soko-solver.pl $VERSION (Games::Sokoban::Solver)"; exit 0}
Pod::Usage::pod2usage(
    '-exitval' => 2,
    '-verbose' => 0,
    '-message' => 'soko-solver.pl: no level file given (use - for standard input)'
    )
    unless @ARGV;

# --- the settings: defaults < ini < command line -----------------------------------
my %cli = (
    'jobs'           => $o{'jobs'},
    'time'           => $o{'time'},
    'optimal'        => $o{'optimal'},
    'optimal_mode'   => $o{'optimal-mode'},
    'fest_budget'    => $o{'fest-budget'},
    'blok_budget'    => $o{'blok-budget'},
    'maxgb'          => $o{'maxgb'},
    'berkeley'       => $o{'berkeley'},
    'berkeley_root'  => $o{'berkeley-root'},
    'berkeley_cache' => $o{'berkeley-cache'},
    'berkeley_from'  => $o{'berkeley-from'},
    'pull'           => $o{'pull'},
    'forward'        => $o{'forward'},
    'hold'           => $o{'hold'},
    'format'         => $o{'format'},
);
my $ini = $o{'ini'} // Games::Sokoban::Solver::Config::path();
my %cfg = eval {
    if (!$o{'no-ini'} and ($o{'init'} or (!-f $ini and -t STDIN))) {
        my %ask = Games::Sokoban::Solver::Config::defaults();
        if (-f $ini) {
            my %was = Games::Sokoban::Solver::Config::load($ini);
            $ask{$_} = $was{$_} for keys %was;
        }
        Games::Sokoban::Solver::Config::ask(\%ask, \*STDIN, \*STDERR);
        Games::Sokoban::Solver::Config::save($ini, \%ask);
        say {*STDERR} "settings written to $ini (edit it, or run with --init to be asked again)";
    }
    Games::Sokoban::Solver::Config::resolve(\%cli, 'ini' => $ini, 'no_ini' => $o{'no-ini'} // 0);
};
unless (%cfg) {print {*STDERR} "soko-solver.pl: $@"; exit 2}
my $serial  = ($o{'no-threads'} or $cfg{'jobs'} <= 1 or $o{'verbose'}) ? 1 : 0;
my $jobs    = $serial                                                  ? 1 : $cfg{'jobs'};
my $quiet   = $o{'quiet'}                                              ? 1 : 0;
my $verbose = $o{'verbose'}                                            ? 1 : 0;
my %caps    = ('pull' => $cfg{'pull'}, 'forward' => $cfg{'forward'});

# The memory probe says once on STDERR when this machine has none (the memory
# net is then off). --quiet leaves errors alone on STDERR, and that is a notice:
# the first probe is made here with the warning swallowed, and it is never said again.
if ($quiet) {
    local $SIG{'__WARN__'} = sub { };
    Games::Sokoban::Solver::Memory::scope();
}
for my $mode ($cfg{'optimal_mode'}) {
    die "soko-solver.pl: --optimal-mode must be DIAL, ASTAR or FIFO\n"
        unless grep {$_ eq $mode} Games::Sokoban::Solver::Portfolio::solver_modes();
}

# The modes of the race: the order of the Portfolio, cut down by --modes and
# --engines; the analyses built are those the modes left need.
my %engine_of = ('firstbet' => 'Firstbet', 'firstback' => 'FirstBack', 'festival' => 'Festival', 'fest' => 'Fest');
my @modes     = Games::Sokoban::Solver::Portfolio::race_order();
if (defined $o{'engines'}) {
    my %on;
    for my $e (split /,/, lc $o{'engines'}) {
        die "soko-solver.pl: --engines: '$e' is none of " . join(', ', sort keys %engine_of) . "\n" unless $engine_of{$e};
        $on{"Games::Sokoban::Solver::$engine_of{$e}"} = 1;
    }
    @modes = grep {$on{ Games::Sokoban::Solver::Portfolio::engine_for($_) }} @modes;
}
if (defined $o{'modes'}) {
    my %known = map {$_ => 1} Games::Sokoban::Solver::Portfolio::all_modes();
    my @asked = split /,/, uc $o{'modes'};
    for (@asked) {die "soko-solver.pl: --modes: '$_' is no mode (see --help)\n" unless $known{$_}}
    my %asked = map {$_ => 1} @asked;
    @modes = grep {$asked{$_}} @modes;
}
die "soko-solver.pl: no mode is left to run\n" unless @modes;
my %want = ('game' => 1, map {Games::Sokoban::Solver::Portfolio::blob_for($_) => 1} @modes);

# --- the levels ------------------------------------------------------------------
my @work;    # [file, level]
for my $file (@ARGV) {
    my $text;
    if ($file eq '-') {$text = do {local $/; <STDIN>} // ''}
    else {
        open(my $fh, '<', $file) or do {print {*STDERR} "soko-solver.pl: cannot read $file: $!\n"; exit 2};
        $text = do {local $/; <$fh>};
        close $fh;
    }
    my @levels = Games::Sokoban::Solver::read_levels($text);
    unless (@levels) {print {*STDERR} "soko-solver.pl: no level in $file\n"; exit 2}
    if     (defined $o{'level'}) {
        my %pick;
        for my $part (split /,/, $o{'level'}) {
            if    ($part =~ /\A(\d+)-(\d+)\z/) {$pick{$_} = 1 for $1 .. $2}
            elsif ($part =~ /\A(\d+)\z/)       {$pick{$1} = 1}
            else {print {*STDERR} "soko-solver.pl: --level takes numbers and ranges, not '$part'\n"; exit 2}
        }
        @levels = grep {$pick{ $_->{'index'} }} @levels;
    }
    push @work, map {[$file, $_]} @levels;
} ## end for my $file (@ARGV)
unless (@work) {print {*STDERR} "soko-solver.pl: --level picked no level\n"; exit 2}
my $out;
if (defined $o{'out'}) {
    open($out, '>', $o{'out'}) or do {print {*STDERR} "soko-solver.pl: cannot write $o{'out'}: $!\n"; exit 2};
}
my $format = $cfg{'format'};
my $json;
if ($format eq 'json') {require JSON::PP; $json = JSON::PP->new->canonical->ascii}

sub emit ($line) {
    print {*STDOUT} $line, "\n";
    print {$out} $line,    "\n" if $out;
    return;
}
sub info (@text) {print {*STDERR} @text, "\n" unless $quiet; return}

# --- the pool, once for the run ----------------------------------------------------
STDOUT->autoflush(1);
STDERR->autoflush(1);    # a thread's clone of STDERR is buffered and would cut lines in half
my $berk_race = ($cfg{'berkeley'} and $cfg{'time'} >= $cfg{'berkeley_from'}) ? 1 : 0;
my $berk_best = ($cfg{'berkeley'} and $cfg{'optimal'} > 0 and $cfg{'optimal'} >= $cfg{'berkeley_from'}) ? 1 : 0;
my %berk      = ('root' => $cfg{'berkeley_root'}, 'cache_gb' => $cfg{'berkeley_cache'});
my $pool      = eval {
    Games::Sokoban::Solver::pool(
        'jobs'   => $jobs,
        'serial' => $serial,
        'max_gb' => $cfg{'maxgb'},
        'quiet'  => ($verbose ? 0 : 2),
        ($berk_race ? ('berkeley' => \%berk) : ()),
    );
};
unless ($pool) {(my $why = "$@") =~ s/\n.*//s; print {*STDERR} "soko-solver.pl: $why\n"; exit 2}
emit('# ' . join("\t", qw(level title status moves pushes forced proved first_mode first_s optimal_mode optimal_s path)))
    if $format eq 'report';
info(
    sprintf 'soko-solver.pl %s: %d level%s, %d mode%s, %s s a mode, %s s the proof (%s), %s, memory probe %s%s%s',
    $VERSION,
    scalar @work,
    (@work == 1 ? '' : 's'),
    scalar @modes,
    (@modes == 1 ? '' : 's'),
    $cfg{'time'},
    ($cfg{'optimal'} > 0 ? $cfg{'optimal'} : 'no'),
    $cfg{'optimal_mode'},
    ($pool->threaded ? "$jobs threads" : 'one task at a time, no threads'),
    Games::Sokoban::Solver::Memory::scope(),
    ($cfg{'maxgb'}            ? ", ceiling $cfg{'maxgb'} GB"                      : ''),
    ($berk_race || $berk_best ? ", BerkeleyDB stores under $cfg{'berkeley_root'}" : '')
);
info(
    sprintf '  a level takes up to about %d s: %d modes x %s s / %d + the analyses + up to 2 x %s s for the proof',
    (@modes * $cfg{'time'} / $jobs + 2 * $cfg{'optimal'}),
    scalar @modes,
    $cfg{'time'}, $jobs, $cfg{'optimal'}
    )
    unless $quiet;

# --- Ctrl+C: the first stops the level in hand and skips the rest, the second ends at once
my ($Stop, $Label) = (0, undef);
my %stop_flag;
$SIG{'INT'} = sub {
    if ($Stop++) {print {*STDERR} "\nsoko-solver.pl: stopped\n"; POSIX::_exit(130)}
    print {*STDERR}
        "\nsoko-solver.pl: interrupted -- the level in hand is being stopped, the rest skipped (Ctrl+C again ends at once)\n";
    if (defined $Label) {$pool->stop($Label); $stop_flag{$Label} = 1}
};

# --- the levels, one after another -------------------------------------------------
my %tally = ('SOLVED' => 0, 'UNSOLVED' => 0, 'REFUSED' => 0, 'proved' => 0);
my $exit  = 0;
my $n     = 0;
my $t_run = Time::HiRes::time();
for my $w (@work) {
    my ($file, $level) = @$w;
    ++$n;
    if ($Stop) {
        say_level_result($level, { 'status' => 'UNSOLVED', 'reason' => 'skipped after the interrupt' });
        ++$tally{'UNSOLVED'};
        $exit ||= 1;
        next;
    }
    my $tag = sprintf '[%d/%d] "%s"', $n, scalar @work, $level->{'title'};
    my $t0  = Time::HiRes::time();

    # prepare
    my $p = eval {
        Games::Sokoban::Solver::prepare(
            'rows'        => $level,
            'blok_budget' => $cfg{'blok_budget'},
            'fest_budget' => $cfg{'fest_budget'},
            'want'        => [keys %want],
            'lazy'        => 1,
            'pool'        => $pool,
            'on_note'     => sub ($t) {info("  note: $t") if $verbose}
        );
    };
    unless ($p) {
        my $why = "$@";
        if ($why =~ /\AREFUSED:/) {
            $why = Games::Sokoban::Solver::refusal($why);
            info("$tag  REFUSED: " . ($why =~ s/\AREFUSED:\s*//r));
            say_level_result($level, { 'status' => 'REFUSED', 'reason' => $why });
            ++$tally{'REFUSED'};
            $exit ||= 1;
            next;
        }
        print {*STDERR} "soko-solver.pl: $tag: $why";
        exit 3;
    }
    $Label = $p->{'label'};
    info(
        sprintf '%s  %dx%d  %d box%s  %d cells%s',
        $tag, $p->{'w'}, $p->{'h'}, $p->{'nbox'}, ($p->{'nbox'} == 1 ? '' : 'es'),
        $p->{'ncell'}, (length $p->{'firststep'} ? sprintf(', a forced opening of %d letters', length $p->{'firststep'}) : '')
    );
    if ($o{'show'}) {print {*STDERR} Games::Sokoban::Solver::Level::as_text($p->{'code1'})}
    my %r = ('status' => 'SOLVED', 'prepared' => $p);
    if ($p->{'solved_by_opening'}) {
        info('  the forced opening alone solves the level');
        $r{'proved'}      = 1;
        $r{'engine_path'} = '';
    }
    else {
        # the race
        my $first = Games::Sokoban::Solver::first_solution(
            'prepared'  => $p,
            'pool'      => $pool,
            'time'      => $cfg{'time'},
            'modes'     => \@modes,
            'caps'      => \%caps,
            'hold_gb'   => $cfg{'hold'},
            'blok'      => $o{'blok'},
            'on_note'   => sub ($t) {info("  note: $t")},
            'on_answer' => sub ($a) {
                return unless $verbose;
                info(
                    sprintf '    %-12s %-10s %7.1f s  %10d positions%s%s',
                    @{$a}{ 'mode', 'reason', 'wall', 'nseen' },
                    ($a->{'reason'} eq 'SOLVED' ? sprintf('  %d moves / %d pushes', @{$a}{ 'sollen', 'pushes' }) : ''),
                    (length($a->{'fail'} // '') ? "  ($a->{'fail'})"                                             : '')
                );
            },
        );
        $r{'first'} = $first;
        my $cost = $p->{'cost'};
        info(
            sprintf '  prepare: level %.2f s, code %.2f s, parser %.1f s, blok %.1f s (%d patterns%s)%s%s',
            @{$cost}{ 'level', 'code', 'parser', 'blok' },
            scalar @{ $p->{'blok_report'} },
            ($p->{'blok_complete'} ? ', complete' : ', cut by the budget'),
            (
                defined $cost->{'fest'}
                ? sprintf(', fest %.1f s%s',
                    $cost->{'fest'},
                    (@{ $p->{'fest_incomplete'} } ? ' (' . join(' and ', @{ $p->{'fest_incomplete'} }) . ' incomplete)' : ''))
                : ''
            ),
            (defined $cost->{'analysis'} ? sprintf(', analysis %.1f s', $cost->{'analysis'}) : '')
        );
        if (@{ $first->{'died'} }) {
            for my $d (@{ $first->{'died'} }) {
                print {*STDERR} "soko-solver.pl: $tag: the engine of $d->{'mode'} died: " . (split /\n/, $d->{'error'})[0] . "\n";
            }
            $exit = 3;
        }
        if ($first->{'reason'} ne 'SOLVED') {
            my %why;
            ++$why{ $_->{'reason'} } for @{ $first->{'answers'} };
            info(
                sprintf '  UNSOLVED  %s  %.1f s',
                join(', ', map {"$_ $why{$_}"} sort keys %why) || 'no mode ran',
                Time::HiRes::time() - $t0
            );
            say_level_result($level, { %r, 'status' => 'UNSOLVED', 'reason' => 'no mode solved the level' });
            ++$tally{'UNSOLVED'};
            $exit ||= 1;
            next;
        }
        info(sprintf '  first:    %-12s %d moves / %d pushes  %.1f s', @{$first}{ 'mode', 'sollen', 'pushes', 'seconds' });
        $r{'engine_path'} = $first->{'path'};
        $r{'proved'}      = 0;

        # the proof
        if ($cfg{'optimal'} > 0 and !$Stop) {
            my $best = Games::Sokoban::Solver::best_solution(
                'prepared' => $p,
                'seed'     => $first->{'path'},
                'time'     => $cfg{'optimal'},
                'mode'     => $cfg{'optimal_mode'},
                'band'     => $o{'band'},
                'max_gb'   => $cfg{'maxgb'},
                'stop'     => \%stop_flag,
                ($berk_best ? ('berkeley' => \%berk) : ()),
                'on_improved' =>
                    sub ($path, $s) {info(sprintf '    improved: %d moves  %.1f s', length $path, $s) if $verbose},
            );
            $r{'best'}        = $best;
            $r{'engine_path'} = $best->{'path'} if length $best->{'path'} and length $best->{'path'} <= length $first->{'path'};
            $r{'proved'}      = $best->{'proved'};
            my $said =
                $best->{'reason'} eq 'SOLVED' ? sprintf('%d moves PROVED shortest for the reduced level', length $best->{'path'})
                : $best->{'status'} eq 'IGNORE' ? sprintf('%d moves, not proved (interrupted)',        length $r{'engine_path'})
                : $best->{'status'} eq 'MEMCAP' ? sprintf('%d moves, not proved (the memory ceiling)', length $r{'engine_path'})
                : $best->{'reason'} eq 'UNSOLVABLE' ? 'UNSOLVABLE -- the first solution stands'
                :   sprintf('%d moves, not proved (%s)', length $r{'engine_path'}, $best->{'status'});
            info(sprintf '  optimal:  %s  %s %.1f s%s',
                $said, $cfg{'optimal_mode'}, $best->{'seconds'},
                (length $p->{'firststep'} ? sprintf(' (%d forced opening moves prepended)', length $p->{'firststep'}) : ''));
        } ## end if ($cfg{'optimal'} > ...)
    } ## end else [ if ($p->{'solved_by_opening'...})]

    # the whole path, checked
    my $full = eval {Games::Sokoban::Solver::full_path($p, $r{'engine_path'})};
    unless (defined $full) {
        print {*STDERR} "soko-solver.pl: $tag: " . ("$@" =~ s/\n.*//sr) . " -- the solution is NOT printed\n";
        say_level_result($level, { %r, 'status' => 'UNSOLVED', 'reason' => 'internal: the solution did not replay' });
        ++$tally{'UNSOLVED'};
        $exit = 3;
        next;
    }
    $r{'path'}   = $full;
    $r{'moves'}  = length $full;
    $r{'pushes'} = ($full =~ tr/DLRU//);
    $r{'forced'} = length $p->{'firststep'};
    info(
        sprintf '  SOLVED    %d moves / %d pushes%s  %.1f s',
        $r{'moves'}, $r{'pushes'},
        ($r{'proved'} ? ', proved' : ''),
        Time::HiRes::time() - $t0
    );
    if ($o{'show'}) {print {*STDERR} "$full\n"}
    say_level_result($level, \%r);
    ++$tally{'SOLVED'};
    ++$tally{'proved'} if $r{'proved'};
} ## end for my $w (@work)
continue {$Label = undef}
$pool->close;
$pool->join;
close $out if $out;
info(
    sprintf 'done: %d solved (%d proved), %d unsolved, %d refused, %.0f s',
    @tally{ 'SOLVED', 'proved', 'UNSOLVED', 'REFUSED' },
    Time::HiRes::time() - $t_run
);
exit $exit;

# One level's line(s) on STDOUT, in the format asked for.
sub say_level_result ($level, $r) {
    my $status = $r->{'status'};
    if    ($format eq 'path') {emit($status eq 'SOLVED' ? $r->{'path'} : $status)}
    elsif ($format eq 'sok') {
        emit($level->{'title'});
        emit($_) for @{ $level->{'rows'} };
        emit('Solution: ' . ($status eq 'SOLVED' ? $r->{'path'} : 'none' . ($status eq 'REFUSED' ? " ($r->{'reason'})" : '')));
        emit('');
    }
    elsif ($format eq 'report') {
        my $first = $r->{'first'};
        my $best  = $r->{'best'};
        emit(
            join "\t",
            $level->{'index'},
            $level->{'title'},
            $status,
            $r->{'moves'}  // '',
            $r->{'pushes'} // '',
            $r->{'forced'} // '',
            $r->{'proved'} // 0,
            $first ? ($first->{'mode'} // '', defined $first->{'seconds'} ? sprintf('%.1f', $first->{'seconds'}) : '') : ('', ''),
            $best ? ($cfg{'optimal_mode'}, sprintf('%.1f', $best->{'seconds'})) : ('', ''),
            $r->{'path'} // ''
        );
    } ## end elsif ($format eq 'report')
    else {
        my %j = (
            'level'   => $level->{'index'},
            'title'   => $level->{'title'},
            'status'  => $status,
            'threads' => ($pool->threaded ? 'on' : 'off'),
            ($status eq 'REFUSED'  ? ('reason' => $r->{'reason'}) : ()),
            ($status eq 'UNSOLVED' ? ('reason' => $r->{'reason'}) : ()),
            (
                $status eq 'SOLVED'
                ? (
                    'path'   => $r->{'path'},
                    'moves'  => $r->{'moves'},
                    'pushes' => $r->{'pushes'},
                    'forced' => $r->{'forced'},
                    'proved' => $r->{'proved'}
                  )
                : ()
            ),
        );
        if (my $p = $r->{'prepared'}) {
            $j{'boxes'}         = $p->{'nbox'};
            $j{'cells'}         = $p->{'ncell'};
            $j{'blok_complete'} = $p->{'blok_complete'};
            $j{'cost'}          = { map {$_ => 0 + sprintf('%.3f', $p->{'cost'}{$_})} keys %{ $p->{'cost'} } };
        }
        if (my $f = $r->{'first'}) {
            $j{'first'} = {
                'reason' => $f->{'reason'},
                (
                    $f->{'reason'} eq 'SOLVED'
                    ? (
                        'mode'    => $f->{'mode'},
                        'moves'   => $f->{'sollen'},
                        'pushes'  => $f->{'pushes'},
                        'seconds' => 0 + sprintf('%.3f', $f->{'seconds'})
                      )
                    : ()
                ),
                'answers' => [
                    map {
                        {
                            'mode'      => $_->{'mode'},
                            'reason'    => $_->{'reason'},
                            'seconds'   => 0 + sprintf('%.3f', $_->{'wall'}),
                            'positions' => 0 + $_->{'nseen'}
                        }
                    } @{ $f->{'answers'} }
                ]
            };
        } ## end if (my $f = $r->{'first'...})
        if (my $b = $r->{'best'}) {
            $j{'best'} = {
                'reason'  => $b->{'reason'},
                'status'  => $b->{'status'},
                'mode'    => $cfg{'optimal_mode'},
                'moves'   => length $b->{'path'},
                'proved'  => $b->{'proved'},
                'seconds' => 0 + sprintf('%.3f', $b->{'seconds'})
            };
        }
        emit($json->encode(\%j));
    } ## end else [ if ($format eq 'path')]
    return;
} ## end sub say_level_result
__END__

=head1 NAME

soko-solver.pl - solve Sokoban levels: a first solution by a race of search modes, then the shortest one

=head1 SYNOPSIS

    soko-solver.pl [options] FILE [FILE ...]        (FILE - reads standard input)

    soko-solver.pl levels.xsb
    soko-solver.pl --time 120 --optimal 300 --jobs 8 --format report levels.xsb
    soko-solver.pl --level 3,7-9 --show levels.xsb
    soko-solver.pl --init                             (ask the settings again)

=head1 DESCRIPTION

Every level of the files given is read, reduced to what the search needs,
analysed, and solved twice: first by a race of up to 27 search modes of four
engines, the first to find a solution winning, then by an optimal solver that
looks for the shortest solution and, where it can, proves it. One line per
level goes to standard output: the solution as letters (C<u r d l> a step,
C<U R D L> a push) for the level as drawn, or the word C<UNSOLVED> or
C<REFUSED>. Everything else goes to standard error.

The first run asks a few questions and writes the answers to a settings file
(see L</CONFIGURATION>); every setting is also an option here, and an option
wins over the file.

=head1 OPTIONS

=over 4

=item B<--time> S, B<--limit> S

Seconds for one mode of the race on a level (default 60). The mode ORDER
always has 30 of its own.

=item B<--jobs> N

Worker threads of the race (default: the processors less one, 1 to 8). With 1
nothing is threaded: every task runs in turn in this process.

=item B<--no-threads>

The same as C<--jobs 1>: no threads even on a perl that has them.

=item B<--modes> M,M,...

Only these modes, in the order of the race (default: all 27 --
see L<Games::Sokoban::Solver::Portfolio>).

=item B<--engines> L

Only these engines, a comma-separated list of C<firstbet>, C<firstback>,
C<festival>, C<fest> (default all). An engine left out is not analysed for
either.

=item B<--pull> N, B<--forward> N

How many pull searches (BACKWARD, FIRSTBACK) and forward modes of Firstbet may
run at once (defaults 1 and 3): the memory of a large level is in those.

=item B<--hold> GB

No counted mode starts while the whole machine uses more than this many GB
(default 0 = off).

=item B<--maxgb> F

Every engine stops when the whole machine uses more than this many GB
(default 0 = off); the level is then reported by the modes that finished.

=item B<--blok-budget> S

Seconds for the deadlock patterns of a level (default 30; 0 = none, -1 = the
complete table, which can take hours on a large level). The patterns are
dealt out to the worker threads, so more threads finish more of them.

=item B<--fest-budget> S

Seconds for the Festival analysis of a level (default 120). Two parts of it
stop when it is spent; the rest has no limit.

=item B<--blok> 0|1

Whether the Festival engine lets the pattern table stand in for its own
deadlock battery. Default: 1 when the table came out complete, 0 when the
budget cut it.

=item B<--optimal> S

Seconds for the proof of the shortest solution (default 60; 0 = skip it).
DIAL and ASTAR may run on to twice that when the search predicts the proof
fits; FIFO ends when its wave is done.

=item B<--optimal-mode> M

The regime of the proof: DIAL (default), ASTAR or FIFO.

=item B<--band> K

FIFO's band in boxes (default 2; 0 = none).

=item B<--berkeley> 0|1, B<--berkeley-root> DIR, B<--berkeley-cache> GB, B<--berkeley-from> S

The search of long runs on disk through BerkeleyDB (the module must be
installed): Firstbet's modes and the proof run in their twins when their limit
is at least C<--berkeley-from> seconds (default 600; 0 = always), with their
stores under C<--berkeley-root> and a memory pool of C<--berkeley-cache> GB a
store (default 0.5, at most 3). A level that was not solved leaves its stores
for the next attempt.

=item B<--ini> FILE, B<--init>, B<--no-ini>

The settings file to use; ask the questions again and rewrite it; use neither
(the defaults and the options alone -- what the tests do).

=item B<--level> N[,N|N-M]

Only these levels of each file, counted from 1.

=item B<--format> F

C<path> (default): one line per level. C<sok>: the level's text, then
C<Solution: ...>. C<report>: tab-separated columns (a header line first).
C<json>: one JSON object per level per line.

=item B<--out> FILE

The same output into FILE as well.

=item B<--show>

Draw the reduced level and the solution on standard error.

=item B<--quiet>, B<--verbose>

Only errors on standard error; or every answer of every mode, the engines'
own progress lines included (which makes the run single-threaded).

=item B<--version>, B<--help>

=back

=head1 INPUT

Level files in the standard text format (XSB, .sok): C<#> a wall, C<$> a
box, C<.> a goal, C<@> the player, C<*> a box on a goal, C<+> the player on a
goal, a space (or C<-> or C<_>) for floor. A level is a run of such lines;
the nearest non-blank line before it (or a C<Title:> line) is its title. A
level whose floor touches the edge of its rectangle gets a ring of walls.

A level that is none -- a character that is no part of a level, more than one
player, boxes and goals of different numbers, no box off a goal, a goal no
box can ever be pushed onto -- is REFUSED with its reason, and the run goes on
with the next level.

=head1 OUTPUT

Standard output holds nothing but the results, so it can be piped on. Every
solution printed has been replayed on the level as drawn by a second program
that shares no code with the solver; a solution that would not replay is an
internal error and is never printed.

Standard error: a banner with the settings of the run and the time a level
can take at most; for every level its size, what the preparation cost, the
mode that found the first solution and how long it took, the verdict of the
proof, and the whole; at the end the tally.

=head1 EXIT STATUS

0 when every level was solved; 1 when at least one was UNSOLVED or REFUSED
(the run goes on to the end); 2 for a mistake in the options, the settings or
a file; 3 for an internal fault (an engine died, a solution did not replay).

=head1 INTERRUPT

Ctrl+C once: the level in hand is stopped (the modes still running come back
within about a second, the proof at its next checkpoint) and its best known
solution is printed as not proved; the levels after it are reported UNSOLVED
without being tried. Ctrl+C twice: the program ends at once with status 130.

=head1 CONFIGURATION

The settings live in C<soko-solver.ini> -- under C<%APPDATA%\soko-solver> on
Windows, under C<$XDG_CONFIG_HOME/soko-solver> or C<~/.config/soko-solver>
elsewhere (C<SOKO_SOLVER_HOME> overrides both). The first run with no file
and a terminal on standard input asks the questions (threads, seconds for the
race and the proof, a memory ceiling, BerkeleyDB) and writes the file with
every setting's meaning and default as a comment; C<--init> asks again,
C<--no-ini> uses neither. The file's keys are the long options with C<_> for
C<->. See L<Games::Sokoban::Solver::Config>.

=head1 WHAT TO EXPECT

The engines were measured on levels of up to 400 reachable cells and 30
boxes. The deadlock patterns are computed under a budget here (the Sokoban
project spent a year of processor time on its table), so a search may take
another way or fail where that project's campaign succeeded; the Festival
analysis has a budget of its own. A level the race does not solve in the
given time is UNSOLVED, not unsolvable.

=head1 SEE ALSO

L<Games::Sokoban::Solver>, L<Games::Sokoban::Solver::Portfolio>,
L<Games::Sokoban::Solver::Config>.

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This program is free software; you can redistribute it and/or modify it under
the same terms as Perl itself, either Perl version 5.42.2 or, at your option,
any later version of Perl 5 you may have available.

=cut
