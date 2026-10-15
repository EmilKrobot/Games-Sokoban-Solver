#!/usr/bin/env perl
# Parser::parse against the Sokoban project's stored analyses: on games of its
# collection the hash parse() returns from the stored Code record
# (game_blob.code_blob) must equal the stored game_blob.game key for key --
# except blok, computed here by the Finder under a budget instead of looked up
# in Patterns.sqlite3, and except gate / has_gate / homes, which this Parser no
# longer writes. The bloks are held to the stored ones push by push: equal where
# the Finder finished the push's pattern (k_done == kmax), a subset where the
# budget cut it; a vector of ours the stored table does not have fails.
#
#   perl xt/eq_parser.pl [--limit N] [--budget S] [--complete] [--gameids L] [--spoil]
#   perl xt/eq_parser.pl --calibrate [--budgets 10,30,60,120] [--limit N] [--gameids L]
#
# --limit N: N random games from each size tier (default 50) plus game 1.
# --budget S: the blok budget for a game with more than 8 boxes (default 60);
# a game with up to 8 boxes gets the complete table (undef budget), as does
# every game under --complete (hours to days on the whole sample: the author's).
# --gameids L: these games only. --spoil: one edge of the first game's push
# graph is removed from our result; the gate must report that game.
#
# It also prints the Parser's time per tier, with and without the bloks.
#
# --calibrate (the author's, hours): no comparison but a measurement -- every
# game of the sample is parsed once per budget of --budgets, and the table says
# per tier and budget what share of the stored blok VECTORS the Finder found in
# that time, how many patterns it finished and how many games got the whole
# table; the figure the program's default --blok-budget is chosen by.
# Read-only; PERL5LIB must be empty.
use v5.42;
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long   ();
use Compress::Zlib ();
use Storable       ();
use Games::Sokoban::Solver::Parser ();
STDOUT->autoflush(1);

my %opt = ('limit' => 50, 'budget' => 60, 'complete' => 0, 'gameids' => '', 'spoil' => 0, 'calibrate' => 0, 'budgets' => '10,30,60,120');
Getopt::Long::GetOptions(\%opt, 'limit=i', 'budget=f', 'complete!', 'gameids=s', 'spoil!', 'calibrate!', 'budgets=s')
    or die "usage: eq_parser.pl [--limit N] [--budget S] [--complete] [--gameids L] [--spoil] | --calibrate [--budgets L]\n";

my $db  = Gate::db('Sokoban');
my $sql = <<'SQL';
    SELECT g.gameid, g.code_blob, g.game, d.size_tier, d.nbox
      FROM game_blob g JOIN game_data d USING (gameid)
     WHERE g.source = 'PARSER' AND g.code_blob IS NOT NULL AND g.game IS NOT NULL
SQL
my @rows;
if (length $opt{'gameids'}) {
    my @ids = grep { /\A\d+\z/ } split /[,\s]+/, $opt{'gameids'};
    @rows = @{ $db->selectall_arrayref("$sql AND g.gameid IN (" . join(',', @ids) . ') ORDER BY g.gameid') };
}
else {
    @rows = @{ $db->selectall_arrayref("$sql AND g.gameid = 1") };
    for my $tier (1 .. 4) {
        push @rows, @{ $db->selectall_arrayref("$sql AND d.size_tier = ? AND g.gameid <> 1 ORDER BY random() LIMIT ?", undef, $tier, $opt{'limit'}) };
    }
}

my %n = ('games' => 0, 'key_differ' => 0, 'blok_differ' => 0, 'blok_extra' => 0, 'blok_cut' => 0, 'complete' => 0, 'refused' => 0);
my $failed = 0;
my (%time_graph, %time_blok, %count);

sub thawed ($blob) { return Storable::thaw(Compress::Zlib::uncompress($blob)) }

# The bloks of one game, ours against the stored ones. Returns the counts of
# pushes that differ although complete, and of vectors the stored table lacks.
sub compare_bloks ($gameid, $got, $want, $report) {
    my %done = map { $_->[0] => ($_->[2] >= $_->[1] ? 1 : 0) } @{ $report->{'blok'} };
    my ($differ, $extra) = (0, 0);
    my %pushes;
    for my $h ($got->{'blok'}, $want->{'blok'}) {
        for my $bx (keys %$h) { $pushes{"$bx,$_"} = 1 for keys %{ $h->{$bx} } }
    }
    for my $key (sort keys %pushes) {
        my ($bx, $t) = split /,/, $key;
        my @ours   = sort @{ $got->{'blok'}{$bx}{$t}  // [] };
        my @theirs = sort @{ $want->{'blok'}{$bx}{$t} // [] };
        my %theirs = map { $_ => 1 } @theirs;
        my @more   = grep { !$theirs{$_} } @ours;
        if (@more) { say "game $gameid push $bx->$t: " . scalar(@more) . ' vector(s) the stored table does not have'; ++$extra }
        my $pattern  = $report->{'patpoz'}{$bx}{$t};
        my $complete = !defined $pattern || ($done{$pattern} // 0);    # no pattern = no bloks possible on either side
        next unless $complete;
        next if join("\0", @ours) eq join("\0", @theirs);
        say "game $gameid push $bx->$t (pattern " . ($pattern // '-') . ' complete): ours ' . scalar(@ours) . ' vectors, stored ' . scalar(@theirs);
        ++$differ;
    }
    return ($differ, $extra);
}

# The vectors of a blok table, counted.
sub vectors ($blok) {
    my $n = 0;
    for my $bx (keys %$blok) { $n += scalar @{ $blok->{$bx}{$_} } for keys %{ $blok->{$bx} } }
    return $n;
}

if ($opt{'calibrate'}) {
    my @budgets = grep { /\A\d+(?:\.\d+)?\z/ } split /,/, $opt{'budgets'};
    die "calibrate: --budgets needs numbers\n" unless @budgets;
    my %sum;    # tier -> budget -> [games, share of vectors summed, patterns, patterns complete, games complete]
    my $i = 0;
    for my $row (@rows) {
        my ($gameid, $code_blob, $game_blob, $tier, $nbox) = @$row;
        my $code   = thawed($code_blob);
        my $stored = vectors(thawed($game_blob)->{'blok'});
        for my $budget (@budgets) {
            my %report;
            my %got  = Games::Sokoban::Solver::Parser::parse($code, 'blok_budget' => $budget, 'report' => \%report);
            my $ours = vectors($got{'blok'});
            my $s    = $sum{$tier}{$budget} //= [0, 0, 0, 0, 0];
            $s->[0]++;
            $s->[1] += $stored ? $ours / $stored : 1;
            $s->[2] += $report{'patterns'};
            $s->[3] += grep { $_->[2] >= $_->[1] } @{ $report{'blok'} };
            $s->[4] += $report{'blok_complete'};
            printf {*STDERR} "\r%d  game %d tier %d nbox %d budget %s: %d of %d vectors, %s", ++$i, $gameid, $tier, $nbox, $budget, $ours, $stored,
                ($report{'blok_complete'} ? 'complete' : 'cut');
        }
    }
    print {*STDERR} "\n";
    say join("\t", 'tier', 'budget', 'games', 'vectors_share', 'patterns_complete_share', 'games_complete');
    for my $tier (sort keys %sum) {
        for my $budget (@budgets) {
            my $s = $sum{$tier}{$budget} or next;
            printf "%d\t%s\t%d\t%.3f\t%.3f\t%d\n", $tier, $budget, $s->[0], $s->[1] / $s->[0], $s->[3] / ($s->[2] || 1), $s->[4];
        }
    }
    exit 0;
}

if ($opt{'spoil'}) {
    my ($gameid, $code_blob, $game_blob) = @{ $rows[0] };
    my $code = thawed($code_blob);
    my %got  = Games::Sokoban::Solver::Parser::parse($code, 'blok_budget' => 0);
    my ($bx) = sort { $a <=> $b } keys %{ $got{'cm'} };
    my ($t)  = sort { $a <=> $b } keys %{ $got{'cm'}{$bx} };
    delete $got{'cm'}{$bx}{$t};
    my $want = thawed($game_blob);
    if (Gate::canon($got{'cm'}) ne Gate::canon($want->{'cm'})) { say "spoil: a removed push of game $gameid is reported -- the gate fires" }
    else                                                           { say 'spoil: NOT CAUGHT'; $failed = 1 }
}

for my $row (@rows) {
    my ($gameid, $code_blob, $game_blob, $tier, $nbox) = @$row;
    ++$n{'games'};
    my $code   = thawed($code_blob);
    my $want   = thawed($game_blob);
    my $budget = ($opt{'complete'} or $nbox <= 8) ? undef : $opt{'budget'};
    my %report;
    my %fresh = eval { Games::Sokoban::Solver::Parser::parse($code, 'blok_budget' => $budget, 'report' => \%report) };
    unless (%fresh) { say "REFUSED $gameid: " . (split /\n/, $@)[0]; ++$n{'refused'}; next }

    # Compared as the engines get it: through the blob and back, as the stored
    # one was. A number that is an integer from ** and a float from pow() are
    # the same value and come back from Storable in the same form.
    my %got = %{ thawed(Games::Sokoban::Solver::Parser::blob(\%fresh)) };
    $time_graph{$tier} += $report{'seconds'}{'graph'} + $report{'seconds'}{'rest'};
    $time_blok{$tier}  += $report{'seconds'}{'blok'};
    ++$count{$tier};

    my %skip = map { $_ => 1 } qw(blok gate has_gate homes);
    my @keys = grep { !$skip{$_} } sort keys %{ { %got, %$want } };
    my @bad  = grep { Gate::canon($got{$_}) ne Gate::canon($want->{$_}) } @keys;
    if (@bad) { say "game $gameid: keys differ (@bad)"; ++$n{'key_differ'} }
    my @left = grep { exists $got{$_} } qw(gate has_gate homes);
    if (@left) { say "game $gameid: still writes @left"; ++$n{'key_differ'} }

    my ($differ, $extra) = compare_bloks($gameid, \%got, $want, \%report);
    $n{'blok_differ'} += $differ;
    $n{'blok_extra'}  += $extra;
    if   ($report{'blok_complete'}) { ++$n{'complete'} }
    else                            { ++$n{'blok_cut'} }
    printf {*STDERR} "\r%d  game %d tier %d nbox %d: %d patterns, bloks %s in %.1f s", $n{'games'}, $gameid, $tier, $nbox,
        $report{'patterns'}, ($report{'blok_complete'} ? 'complete' : 'CUT'), $report{'seconds'}{'blok'};
}
print {*STDERR} "\n";

say 'Parser time per game by tier (seconds): tier  n  without bloks  bloks';
for my $tier (sort keys %count) {
    printf "  %d %4d %8.2f %8.2f\n", $tier, $count{$tier}, $time_graph{$tier} / $count{$tier}, $time_blok{$tier} / $count{$tier};
}
$failed = 1 if $n{'key_differ'} or $n{'blok_differ'} or $n{'blok_extra'} or $n{'refused'};
exit Gate::verdict($failed, %n);
