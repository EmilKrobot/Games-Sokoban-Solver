# The program: one line per level that plays on the level as drawn, exit 0;
# --level; the four formats; a refused level (REFUSED, exit 1, the run goes
# on); standard input; --quiet leaves STDERR empty and no run says "isn't
# numeric"; the settings file written by --init and read by the next run;
# threads where this perl has them.
use v5.42;
use Test::More;
use Config ();
use File::Temp ();
use IPC::Open3 ();
use Symbol ();
use JSON::PP ();
use Games::Sokoban::Solver::Level  ();
use Games::Sokoban::Solver::Replay ();

my $PROG = 'bin/soko-solver.pl';
my $tmp  = File::Temp->newdir;
my $dir  = "$tmp";

# run the program: (stdout, stderr, exit status). A trailing scalar reference
# is the text for its standard input. STDERR goes into a file, not a pipe: two
# pipes read one after the other deadlock once the second fills up.
my $runs = 0;
sub run_raw (@args) {
    my $stdin = ref $args[-1] ? ${ pop @args } : undef;
    my $o     = Symbol::gensym();
    ++$runs;
    open(my $ef, '+>', "$dir/err.$runs") or die $!;

    # standard input from a file too: a pipe's write end is inherited by the
    # child on Windows, which then never sees the end of its input
    open(my $if, '+>', "$dir/in.$runs") or die $!;
    print {$if} $stdin if defined $stdin;
    $if->flush;
    seek $if, 0, 0;
    my $pid = IPC::Open3::open3('<&' . fileno($if), $o, '>&' . fileno($ef), $^X, '-Ilib', $PROG, @args);
    local $/;
    my $out = <$o> // '';
    waitpid($pid, 0);
    my $exit = $? >> 8;
    seek $ef, 0, 0;
    my $err = <$ef> // '';
    close $ef;
    s/\r\n/\n/g for $out, $err;    # a pipe on Windows carries CRLF
    return ($out, $err, $exit);
}
sub run (@args) { return run_raw('--no-ini', @args) }

open my $fh, '<', 't/data/micro.xsb' or die $!;
my $text = do { local $/; <$fh> };
close $fh;
my @levels = Games::Sokoban::Solver::Level::read($text);
my @code1  = map { (Games::Sokoban::Solver::Level::normalize($_->{'rows'}))[1] } @levels;

# --- the plain run ----------------------------------------------------------------
{
    my ($out, $err, $exit) = run('--jobs', 1, '--time', 10, '--optimal', 5, 't/data/micro.xsb');
    is($exit, 0, 'exit 0: every level solved') or diag($err);
    my @lines = split /\n/, $out;
    is(scalar @lines, 4, 'one line per level');
    for my $i (0 .. 3) {
        like($lines[$i], qr/\A[udlrUDLR]+\z/, "line " . ($i + 1) . " is a path");
        is(Games::Sokoban::Solver::Replay::check($code1[$i], $lines[$i]), undef, "... and plays on '$levels[$i]{'title'}'");
    }
    like($err, qr/^soko-solver\.pl 0\.01: 4 levels, 27 modes/m, 'the banner');
    like($err, qr/no threads/, 'the banner says no threads');
    like($err, qr/^\[1\/4\] "One box, a corner to walk round"/m, 'a line per level on STDERR');
    like($err, qr/^done: 4 solved \(4 proved\)/m, 'the tally');
    unlike($err, qr/isn't numeric/, 'no "isn\'t numeric" anywhere');
}

# --- --level, --quiet, --show, --out ----------------------------------------------------
{
    my ($out, $err, $exit) = run('--jobs', 1, '--time', 10, '--optimal', 5, '--level', '2,4', '--quiet', '--out', "$dir/paths.txt", 't/data/micro.xsb');
    is($exit, 0, '--level 2,4: exit 0');
    my @lines = split /\n/, $out;
    is(scalar @lines, 2, 'two lines');
    is(Games::Sokoban::Solver::Replay::check($code1[1], $lines[0]), undef, 'the first is level 2');
    is(Games::Sokoban::Solver::Replay::check($code1[3], $lines[1]), undef, 'the second is level 4');
    is($err, '', '--quiet: STDERR empty');
    open my $fh, '<', "$dir/paths.txt" or die $!;
    my $copy = do { local $/; <$fh> };
    close $fh;
    is($copy, $out, '--out holds the same lines');

    ($out, $err, $exit) = run('--jobs', 1, '--time', 10, '--optimal', 0, '--level', 3, '--show', 't/data/micro.xsb');
    is($exit, 0, '--show: exit 0');
    like($err, qr/^#\@\$\.#$/m, 'the level is drawn on STDERR');
    like($err, qr/^R$/m, 'and the solution');
    like($err, qr/^done: 1 solved \(0 proved\)/m, '--optimal 0: not proved');
}

# --- the formats ---------------------------------------------------------------------
{
    my ($out, $err, $exit) = run('--jobs', 1, '--time', 10, '--optimal', 5, '--level', '1-2', '--format', 'sok', 't/data/micro.xsb');
    is($exit, 0, 'sok: exit 0');
    like($out, qr/\AOne box, a corner to walk round\n#######\n/, 'sok: the title and the level');
    my @sol = $out =~ /^Solution: (\S+)$/mg;
    is(scalar @sol, 2, 'sok: two solutions');
    is(Games::Sokoban::Solver::Replay::check($code1[1], $sol[1]), undef, 'sok: the second plays');

    ($out, $err, $exit) = run('--jobs', 1, '--time', 10, '--optimal', 5, '--level', 2, '--format', 'report', 't/data/micro.xsb');
    is($exit, 0, 'report: exit 0');
    my @lines = split /\n/, $out;
    like($lines[0], qr/\A# level\ttitle\tstatus\tmoves/, 'report: the header');
    my @col = split /\t/, $lines[1];
    is($col[0], 2, 'report: the level number');
    is($col[2], 'SOLVED', 'report: SOLVED');
    is($col[3], length $col[-1], 'report: moves = the length of the path');
    is($col[6], 1, 'report: proved');
    is($col[9], 'DIAL', 'report: the optimal mode');

    ($out, $err, $exit) = run('--jobs', 1, '--time', 10, '--optimal', 5, '--level', 4, '--format', 'json', 't/data/micro.xsb');
    is($exit, 0, 'json: exit 0');
    my $j = JSON::PP->new->decode($out);
    is($j->{'status'}, 'SOLVED', 'json: SOLVED');
    is($j->{'threads'}, 'off', 'json: threads off');
    is($j->{'moves'}, length $j->{'path'}, 'json: moves');
    is($j->{'boxes'}, 3, 'json: boxes');
    is($j->{'first'}{'reason'}, 'SOLVED', 'json: the first solution');
    is($j->{'best'}{'proved'}, 1, 'json: proved');
    ok(ref $j->{'first'}{'answers'} eq 'ARRAY' && @{ $j->{'first'}{'answers'} } >= 1, 'json: the answers');
}

# --- a refused level among good ones, standard input ------------------------------------
{
    my $file = <<'XSB';
Good
#####
#@$.#
#####

Two players
######
#@@$.#
######

Good again
######
#@ $.#
######
XSB
    my ($out, $err, $exit) = run('--jobs', 1, '--time', 10, '--optimal', 5, '-', \$file);
    is($exit, 1, 'a refused level: exit 1');
    my @lines = split /\n/, $out;
    is(scalar @lines, 3, 'three lines all the same');
    is($lines[1], 'REFUSED', 'the second is REFUSED');
    like($lines[0], qr/\A[udlrUDLR]+\z/, 'the first solved');
    like($lines[2], qr/\A[udlrUDLR]+\z/, 'the third solved: the run went on');
    like($err, qr/REFUSED: 2 players/, 'STDERR says why');
    like($err, qr/^done: 2 solved \(2 proved\), 0 unsolved, 1 refused/m, 'the tally counts it');
}

# --- an unsolved level: UNSOLVED in every format, never a path --------------------------
# (the round-trip gate once found status SOLVED on a level the race had not solved)
{
    my @args = ('--jobs', 1, '--time', 0.0001, '--optimal', 0, '--modes', 'FF_BASE', '--level', 4, 't/data/micro.xsb');
    my ($out, $err, $exit) = run(@args);
    is($exit, 1, 'unsolved: exit 1');
    is($out, "UNSOLVED\n", 'path format: the word UNSOLVED');
    like($err, qr/^  UNSOLVED /m, 'STDERR says UNSOLVED');
    ($out, $err, $exit) = run(@args, '--format', 'json');
    my $j = JSON::PP->new->decode($out);
    is($j->{'status'}, 'UNSOLVED', 'json: status UNSOLVED');
    ok(!exists $j->{'path'}, 'json: no path');
    like($j->{'reason'}, qr/no mode solved/, 'json: the reason');
    ($out, $err, $exit) = run(@args, '--format', 'report');
    like((split /\n/, $out)[1], qr/\A4\tThree boxes in a room\tUNSOLVED\t\t/, 'report: UNSOLVED with empty counts');
    ($out, $err, $exit) = run(@args, '--format', 'sok');
    like($out, qr/^Solution: none$/m, 'sok: Solution: none');
}

# --- usage errors ------------------------------------------------------------------------
{
    my ($out, $err, $exit) = run();
    is($exit, 2, 'no file: exit 2');
    ($out, $err, $exit) = run('--modes', 'NOSUCH', 't/data/micro.xsb');
    is($exit, 2, 'an unknown mode: exit 2');
    like($err, qr/NOSUCH/, '... named');
    ($out, $err, $exit) = run('--jobs', 0, 't/data/micro.xsb');
    is($exit, 2, 'jobs 0: exit 2');
    like($err, qr/jobs = '0'/, '... named by Config');
    ($out, $err, $exit) = run('--level', 9, 't/data/micro.xsb');
    is($exit, 2, 'a level the file has not: exit 2');
    ($out, $err, $exit) = run('t/data/no_such_file.xsb');
    is($exit, 2, 'a missing file: exit 2');
    ($out, $err, $exit) = run('--engines', 'festival', '--modes', 'ORDER', 't/data/micro.xsb');
    is($exit, 2, 'engines and modes that leave nothing: exit 2');
    ($out, $err, $exit) = run('--version');
    is($exit, 0, '--version: exit 0');
    like($out, qr/\Asoko-solver\.pl 0\.01/, '... and says it');
    ($out, $err, $exit) = run('--help');
    is($exit, 0, '--help: exit 0');
    like($out, qr/OPTIONS/, '... the POD');
}

# --- the settings file: --init with answers from a file, then read by the next run --------
{
    my $ini = "$dir/sub/soko-solver.ini";
    my $answers = "2\n7\n3\n0\n0\n";    # jobs, time, optimal, maxgb, berkeley
    my ($out, $err, $exit) = run_raw('--ini', $ini, '--init', '--level', 3, '--jobs', 1, 't/data/micro.xsb', \$answers);
    is($exit, 0, '--init: exit 0') or diag($err);
    ok(-f $ini, 'the ini was written');
    like($err, qr/How many threads/, 'the questions were asked');
    like($err, qr/settings written to/, 'and the file announced');
    like($err, qr/7 s a mode, 3 s the proof/, 'the run used the answers');
    like($out, qr/\AR\n\z/, 'and solved the level');

    # the next run reads the file; the command line still wins
    ($out, $err, $exit) = run_raw('--ini', $ini, '--level', 3, '--jobs', 1, '--optimal', 4, 't/data/micro.xsb');
    is($exit, 0, 'the next run: exit 0') or diag($err);
    like($err, qr/7 s a mode, 4 s the proof/, 'time from the file, optimal from the command line');
    unlike($err, qr/How many threads/, 'no questions this time');
}

# --- threads ------------------------------------------------------------------------------
SKIP: {
    skip 'this perl has no ithreads', 5 unless $Config::Config{'useithreads'};
    my ($out, $err, $exit) = run('--jobs', 3, '--time', 10, '--optimal', 5, '--format', 'json', 't/data/micro.xsb');
    is($exit, 0, 'threads: exit 0') or diag($err);
    my @j = map { JSON::PP->new->decode($_) } split /\n/, $out;
    is(scalar @j, 4, 'threads: four objects');
    is($j[0]{'threads'}, 'on', 'threads: on');
    is(scalar(grep { $_->{'status'} eq 'SOLVED' } @j), 4, 'threads: all solved');
    like($err, qr/3 threads/, 'the banner says 3 threads');
}

done_testing;
