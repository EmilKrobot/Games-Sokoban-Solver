#!/usr/bin/env perl
# Fest::Analysis against the Sokoban project's stored Fest records: for games of
# its collection, analysis_record(prepare(thaw(game_blob.game))) unpacked must
# equal thaw(game_blob.analysis) key for key.
#
#   perl xt/eq_fest_analysis.pl [--limit N] [--gameids L] [--spoil]
#
# Default: game 1 and N random games per size tier (N = 12, about five
# seconds a game). --spoil: one table of the first game's record is altered;
# the gate must fire.
# Read-only; PERL5LIB must be empty.
use v5.42;
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long   ();
use Compress::Zlib ();
use Storable       ();
use Time::HiRes    ();
use Games::Sokoban::Solver::Fest::Analysis ();
STDOUT->autoflush(1);

my %opt = ('limit' => 12, 'gameids' => '', 'spoil' => 0);
Getopt::Long::GetOptions(\%opt, 'limit=i', 'gameids=s', 'spoil!') or die "usage: eq_fest_analysis.pl [--limit N] [--gameids L] [--spoil]\n";

my $db  = Gate::db('Sokoban');
my $sql = <<'SQL';
    SELECT g.gameid, g.game, g.analysis, d.size_tier
      FROM game_blob g JOIN game_data d USING (gameid)
     WHERE g.source = 'PARSER' AND g.game IS NOT NULL AND g.analysis IS NOT NULL
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

sub thawed ($blob) { return Storable::thaw(Compress::Zlib::uncompress($blob)) }

sub record_of ($game_blob) {
    my $record = Games::Sokoban::Solver::Fest::Analysis::prepare(thawed($game_blob));
    return thawed(Games::Sokoban::Solver::Fest::Analysis::analysis_record($record));
}

my %n = ('games' => 0, 'differ' => 0, 'refused' => 0);
my $failed = 0;

if ($opt{'spoil'}) {
    my ($gameid, $game_blob, $analysis_blob) = @{ $rows[0] };
    my $got = record_of($game_blob);
    my ($cell) = keys %{ $got->{'walk'} };
    delete $got->{'walk'}{$cell};
    my $want = thawed($analysis_blob);
    my @bad  = grep { Gate::canon($got->{$_}) ne Gate::canon($want->{$_}) } sort keys %{ { %$got, %$want } };
    if (@bad) { say "spoil: an altered walk table of game $gameid is reported (@bad) -- the gate fires" }
    else      { say 'spoil: NOT CAUGHT'; $failed = 1 }
}

my %time;
for my $row (@rows) {
    my ($gameid, $game_blob, $analysis_blob, $tier) = @$row;
    ++$n{'games'};
    my $t0  = Time::HiRes::time();
    my $got = eval { record_of($game_blob) };
    unless ($got) { say "REFUSED $gameid: " . (split /\n/, $@)[0]; ++$n{'refused'}; next }
    $time{$tier}[0] += Time::HiRes::time() - $t0;
    $time{$tier}[1]++;
    my $want = thawed($analysis_blob);
    my @bad  = grep { Gate::canon($got->{$_}) ne Gate::canon($want->{$_}) } sort keys %{ { %$got, %$want } };
    if (@bad) { say "game $gameid: keys differ (@bad)"; ++$n{'differ'} }
    printf {*STDERR} "\r%d  game %d tier %d: %.1f s", $n{'games'}, $gameid, $tier, Time::HiRes::time() - $t0;
}
print {*STDERR} "\n";

say 'preparation time per game by tier (seconds):';
printf "  %d %3d %8.2f\n", $_, $time{$_}[1], $time{$_}[0] / $time{$_}[1] for sort keys %time;
$failed = 1 if $n{'differ'} or $n{'refused'};
exit Gate::verdict($failed, %n);
