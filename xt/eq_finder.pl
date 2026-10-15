#!/usr/bin/env perl
# Finder against the Sokoban project's pattern database: for random patterns
# of Patterns.sqlite3 the blok string blok_task builds for the sizes 1..lim
# must equal the stored one byte for byte (the stored string is complete
# exactly to lim), and the same pattern under a short deadline must yield
# nothing but sets of the stored string (a cut leaves fewer bloks, never a
# wrong one).
#
#   perl xt/eq_finder.pl [--limit N] [--deadline S] [--spoil]
#
# --limit N: N patterns from each of three bands of lim (<= 5, 6..9, 10..14),
# default 100 (the whole run is some minutes; the 10..14 band carries the
# tail). --deadline S: the short deadline per pattern, default 0.1 s.
# --spoil: the first stored string is altered; the gate must report it.
#
# It also prints the time per pattern by lim, ours against the database's.
# Read-only; PERL5LIB must be empty.
use v5.42;
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long ();
use Time::HiRes  ();
use Games::Sokoban::Solver::Finder ();
STDOUT->autoflush(1);

my %opt = ('limit' => 100, 'deadline' => 0.1, 'spoil' => 0);
Getopt::Long::GetOptions(\%opt, 'limit=i', 'deadline=f', 'spoil!') or die "usage: eq_finder.pl [--limit N] [--deadline S] [--spoil]\n";

my $db = Gate::db('Patterns');
my @rows;
for my $band ([1, 5], [6, 9], [10, 14]) {
    push @rows, @{
        $db->selectall_arrayref(
            "SELECT pattern, lim, dat, blok, cas FROM patterns WHERE pass = 1 AND lim BETWEEN ? AND ? ORDER BY random() LIMIT ?",
            undef, @$band, $opt{'limit'})
    };
}

my %n = ('patterns' => 0, 'differ' => 0, 'not_subset' => 0, 'cut' => 0, 'insoluble' => 0);
my $failed = 0;

if ($opt{'spoil'}) {
    my ($pattern, $lim, undef, $blok) = @{ $rows[0] };
    my $spoiled = length $blok ? substr($blok, 1) : '0';    # one cell gone, or a set where none is
    my $r = Games::Sokoban::Solver::Finder::blok_task($pattern, $lim, 1, '');
    if ($r->[2] ne $spoiled) { say "spoil: an altered stored string for $pattern is reported -- the gate fires" }
    else                     { say 'spoil: NOT CAUGHT'; $failed = 1 }
}

my (%ours, %theirs, %count);
for my $row (@rows) {
    my ($pattern, $lim, $dat, $blok, $cas) = @$row;
    ++$n{'patterns'};
    unless (Games::Sokoban::Solver::Finder::pat_soluble($pattern)) {
        say "insoluble by itself (the database holds it as pass = 1): $pattern";
        ++$n{'insoluble'};
    }
    my $r = Games::Sokoban::Solver::Finder::blok_task($pattern, $lim, 1, '');
    $ours{$lim}   += $r->[4];
    $theirs{$lim} += $cas;
    ++$count{$lim};
    if ($r->[1] != $lim) { say "not finished without a deadline?! $pattern k_done $r->[1] of $lim"; ++$n{'differ'} }
    if ($r->[2] ne $blok) {
        say "differs: $pattern lim $lim\n  stored '$blok'\n  ours   '$r->[2]'";
        ++$n{'differ'};
    }
    my %full = map { $_ => 1 } split /;/, $blok;
    my $cut  = Games::Sokoban::Solver::Finder::blok_task($pattern, $lim, 1, '', Time::HiRes::time() + $opt{'deadline'});
    ++$n{'cut'} if $cut->[1] < $lim;
    my @extra = grep { !$full{$_} } split /;/, $cut->[2];
    if (@extra) { say "under the deadline a set not in the stored string: $pattern (@extra)"; ++$n{'not_subset'} }
    print {*STDERR} "\r$n{'patterns'}" if $n{'patterns'} % 10 == 0;
}
print {*STDERR} "\r";

say "time per pattern by lim (seconds): lim  n  ours  database";
for my $lim (sort { $a <=> $b } keys %count) {
    printf "  %2d %4d %8.3f %8.3f\n", $lim, $count{$lim}, $ours{$lim} / $count{$lim}, $theirs{$lim} / $count{$lim};
}
say "patterns cut by the $opt{'deadline'} s deadline: $n{'cut'} of $n{'patterns'}"
    . ($n{'cut'} ? '' : ' -- the subset check tested nothing; a longer band or a shorter deadline is needed');
$failed = 1 if $n{'differ'} or $n{'not_subset'} or $n{'insoluble'} or !$n{'cut'};
exit Gate::verdict($failed, %n);
