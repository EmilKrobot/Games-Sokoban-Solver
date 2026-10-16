#!/usr/bin/env perl
# The program round trip: levels of the Sokoban project's collection written
# to ONE level file from their text (zdroj.orig_code), solved by
# bin/soko-solver.pl with threads and then without, and every line held to the
# project's database: exactly one object per level; every path plays on
# zdroj.code1 (the second reading); no path longer than the forced opening
# plus the first solution that seeded it; no PROVED length below the stored
# proved optimum plus the opening (a false proof); the forced opening the
# stored one; a level spoiled on purpose (two players) is REFUSED with its
# reason, the run goes on and ends with status 1; and the two runs solve the
# same levels (their paths may differ: a race is a race).
#
#   perl xt/cli_roundtrip.pl [--count N] [--limit S] [--optimal S] [--jobs N] [--gameids L]
#                            [--read FILE] [--nospoil] [--keep]
#
# Default: game 1, games 36610 8245 4596 (long forced openings), N random
# games per size tier (N = 5), one game with a hole and one with a corridor --
# about 25 levels -- at 30 s a mode and 30 s the proof, 4 threads. --read FILE
# checks a JSON output the program wrote earlier (the USER's long run) instead
# of running it; --nospoil leaves the spoiled level out; --keep leaves the
# level file and the outputs in data/ of the scratch directory named. Read-only
# on the database; PERL5LIB must be empty.
use v5.42;
no warnings 'once';
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long ();
use File::Temp   ();
use IPC::Open3   ();
use JSON::PP     ();
use Symbol       ();
use Time::HiRes  ();
use Games::Sokoban::Solver::Level  ();
use Games::Sokoban::Solver::Replay ();
STDOUT->autoflush(1);

my %opt = ('count' => 5, 'limit' => 30, 'optimal' => 30, 'jobs' => 4, 'gameids' => '', 'read' => '', 'nospoil' => 0, 'keep' => 0);
Getopt::Long::GetOptions(\%opt, 'count=i', 'limit=f', 'optimal=f', 'jobs=i', 'gameids=s', 'read=s', 'nospoil!', 'keep!')
    or die "usage: cli_roundtrip.pl [--count N] [--limit S] [--optimal S] [--jobs N] [--gameids L] [--read FILE] [--nospoil] [--keep]\n";

my $db  = Gate::db('Sokoban');
my $sql = <<'SQL';
    SELECT z.gameid, z.orig_code, z.code1, COALESCE(d.firststep, ''), d.size_tier, d.nbox,
           (SELECT sollen FROM bestbet b WHERE b.gameid = z.gameid AND b.status = 'SOLVED')
      FROM zdroj z JOIN game_blob g USING (gameid) JOIN game_data d USING (gameid)
     WHERE g.source = 'PARSER'
SQL
my @rows;
if (length $opt{'gameids'}) {
    my @ids = grep { /\A\d+\z/ } split /[,\s]+/, $opt{'gameids'};
    @rows = @{ $db->selectall_arrayref("$sql AND z.gameid IN (" . join(',', @ids) . ') ORDER BY z.gameid') };
}
else {
    @rows = @{ $db->selectall_arrayref("$sql AND z.gameid IN (1, 36610, 8245, 4596) ORDER BY z.gameid") };
    my %have = map { $_->[0] => 1 } @rows;
    for my $tier (1 .. 4) {
        push @rows, grep { !$have{ $_->[0] }++ } @{ $db->selectall_arrayref("$sql AND d.size_tier = ? ORDER BY random() LIMIT ?", undef, $tier, $opt{'count'}) };
    }
    push @rows, grep { !$have{ $_->[0] }++ } @{ $db->selectall_arrayref("$sql AND d.has_hole = 1 ORDER BY random() LIMIT 1") };
    push @rows, grep { !$have{ $_->[0] }++ } @{ $db->selectall_arrayref("$sql AND d.has_corridor = 1 ORDER BY random() LIMIT 1") };
}
my %by_index;    # level index in the file -> row
my $dir  = File::Temp::tempdir('cli_roundtrip-XXXXXX', 'TMPDIR' => 1, 'CLEANUP' => !$opt{'keep'});
my $file = "$dir/levels.xsb";
{
    open my $fh, '>', $file or die "$file: $!";
    my $i = 0;
    for my $row (@rows) {
        my ($gameid, $orig) = @$row;
        $by_index{ ++$i } = $row;
        print {$fh} "game $gameid\n$orig\n\n";
    }
    unless ($opt{'nospoil'}) {
        $by_index{ ++$i } = 'spoiled';
        print {$fh} "spoiled: two players\n######\n#@@\$.#\n######\n\n";
    }
    close $fh;
}
say "level file: $file (" . scalar(keys %by_index) . ' levels)';

my %n      = ('levels' => 0, 'solved' => 0, 'proved' => 0, 'unsolved' => 0, 'refused' => 0, 'bad_path' => 0, 'long_path' => 0, 'false_proof' => 0,
    'opening_differ' => 0, 'count_differ' => 0, 'spoil_missed' => 0, 'exit_wrong' => 0, 'runs_differ' => 0);
my $failed = 0;

# One run of the program: (the objects by level index, the exit status, seconds).
sub run_program ($jobs, $out_name) {
    my @cmd = ($^X, "-I$FindBin::Bin/../lib", "$FindBin::Bin/../bin/soko-solver.pl", '--no-ini', '--jobs', $jobs, '--time', $opt{'limit'},
        '--optimal', $opt{'optimal'}, '--format', 'json', '--out', "$dir/$out_name.json", $file);
    say "running: @cmd[3 .. $#cmd]";
    my $t0 = Time::HiRes::time();
    open(my $ef, '+>', "$dir/$out_name.err") or die $!;
    open(my $if, '<', $file) or die $!;    # anything closed would do; a pipe's write end is inherited on Windows
    my $o   = Symbol::gensym();
    my $pid = IPC::Open3::open3('<&' . fileno($if), $o, '>&' . fileno($ef), @cmd);
    local $/;
    my $out = <$o> // '';
    waitpid($pid, 0);
    my $exit = $? >> 8;
    seek $ef, 0, 0;
    my $err = <$ef> // '';
    print $err;
    $out =~ s/\r\n/\n/g;
    return (parse_output($out), $exit, Time::HiRes::time() - $t0);
}

sub parse_output ($text) {
    my %r;
    for my $line (grep { length } split /\n/, $text) {
        my $j = eval { JSON::PP->new->decode($line) };
        unless ($j) { say "a line that is no JSON: $line"; $failed = 1; next }
        $r{ $j->{'level'} } = $j;
    }
    return \%r;
}

# Every object against the database.
sub check ($r, $exit, $what) {
    my %status;
    if (scalar(keys %$r) != scalar(keys %by_index)) { say "$what: " . scalar(keys %$r) . ' objects for ' . scalar(keys %by_index) . ' levels'; ++$n{'count_differ'} }
    for my $i (sort { $a <=> $b } keys %by_index) {
        my $row = $by_index{$i};
        my $j   = $r->{$i};
        unless ($j) { say "$what: level $i has no object"; ++$n{'count_differ'}; next }
        ++$n{'levels'};
        if ($row eq 'spoiled') {
            if ($j->{'status'} eq 'REFUSED' and ($j->{'reason'} // '') =~ /2 players/) { ++$n{'refused'} }
            else { say "$what: the spoiled level was not REFUSED for its two players: $j->{'status'} " . ($j->{'reason'} // ''); ++$n{'spoil_missed'} }
            next;
        }
        my ($gameid, undef, $code1, $pre, $tier, $nbox, $proved_len) = @$row;
        $status{$gameid} = $j->{'status'};
        if ($j->{'status'} eq 'REFUSED') { say "$what: game $gameid REFUSED: $j->{'reason'}"; ++$n{'refused'}; ++$n{'bad_path'}; next }
        if ($j->{'status'} ne 'SOLVED') { ++$n{'unsolved'}; next }
        ++$n{'solved'};
        my $path = $j->{'path'};
        my $why  = Games::Sokoban::Solver::Replay::check($code1, $path);
        if (defined $why) { say "$what: game $gameid: the path does not play on code1: $why"; ++$n{'bad_path'} }
        if ($j->{'forced'} != length $pre) { say "$what: game $gameid: forced opening $j->{'forced'} letters, stored " . length($pre); ++$n{'opening_differ'} }
        if ($j->{'first'} and $j->{'first'}{'reason'} eq 'SOLVED' and length($path) > $j->{'forced'} + $j->{'first'}{'moves'}) {
            say "$what: game $gameid: the path (" . length($path) . ") is longer than opening + first solution ($j->{'forced'} + $j->{'first'}{'moves'})";
            ++$n{'long_path'};
        }
        if ($j->{'proved'}) {
            ++$n{'proved'};
            if (defined $proved_len and length($path) - $j->{'forced'} < $proved_len) {
                say "$what: game $gameid: PROVED " . (length($path) - $j->{'forced'}) . " moves, below the stored proof of $proved_len -- a false proof";
                ++$n{'false_proof'};
            }
        }
    }
    my $all_solved = !grep { $_ ne 'SOLVED' } values %status;
    my $want_exit  = ($opt{'nospoil'} and $all_solved) ? 0 : 1;
    if ($exit != $want_exit) { say "$what: exit status $exit, expected $want_exit"; ++$n{'exit_wrong'} }
    return \%status;
}

my ($status_a, $status_b);
if (length $opt{'read'}) {
    open my $fh, '<', $opt{'read'} or die "$opt{'read'}: $!";
    my $text = do { local $/; <$fh> };
    close $fh;
    $status_a = check(parse_output($text), 1, "read $opt{'read'}");
}
else {
    my ($r, $exit, $secs) = run_program($opt{'jobs'}, 'threads');
    say sprintf 'threads: %d objects, exit %d, %.0f s', scalar(keys %$r), $exit, $secs;
    $status_a = check($r, $exit, 'threads');
    ($r, $exit, $secs) = run_program(1, 'serial');
    say sprintf 'serial: %d objects, exit %d, %.0f s', scalar(keys %$r), $exit, $secs;
    $status_b = check($r, $exit, 'serial');
    for my $gameid (sort { $a <=> $b } keys %$status_a) {
        next if ($status_a->{$gameid} // '') eq ($status_b->{$gameid} // '');
        say "game $gameid: threads $status_a->{$gameid}, serial " . ($status_b->{$gameid} // 'missing');
        ++$n{'runs_differ'};
    }
}
$failed = 1 if grep { $n{$_} } qw(bad_path long_path false_proof opening_differ count_differ spoil_missed exit_wrong runs_differ);
say "the level file and the outputs are kept in $dir" if $opt{'keep'};
exit Gate::verdict($failed, %n);
