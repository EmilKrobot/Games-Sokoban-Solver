#!/usr/bin/env perl
# Festival::Analysis against the Sokoban project's stored Festival analyses:
# parse(game_blob.code, 36000) must equal thaw(game_blob.fest) field for field
# -- the blok key added by with_blok from the stored Parser blob, the two fuse
# flags left out (the stored blobs predate them) and ver left out (it carries
# the project module's version); key and stamp exactly. The games run one after
# another in one process, so a level leaving anything behind for the next would
# show. Then game 13858 with a budget of 1 s: both fuses must fire and be
# reported, and the hash must still freeze.
#
#   perl xt/eq_festival_analysis.pl [--limit N] [--gameids L] [--nofuse] [--spoil]
#
# Default: games 1, 16899, 30650 and N random games per size tier (N = 7).
# --spoil: one field of the first game's result is altered; the gate must fire.
# Read-only; PERL5LIB must be empty.
use v5.42;
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long   ();
use Compress::Zlib ();
use Storable       ();
use Time::HiRes    ();
use Games::Sokoban::Solver::Festival::Analysis ();
STDOUT->autoflush(1);

my %opt = ('limit' => 7, 'gameids' => '', 'fuse' => 1, 'spoil' => 0);
Getopt::Long::GetOptions(\%opt, 'limit=i', 'gameids=s', 'fuse!', 'spoil!')
    or die "usage: eq_festival_analysis.pl [--limit N] [--gameids L] [--nofuse] [--spoil]\n";

my $db  = Gate::db('Sokoban');
my $sql = <<'SQL';
    SELECT g.gameid, g.code, g.fest, g.game, d.size_tier
      FROM game_blob g JOIN game_data d USING (gameid)
     WHERE g.source = 'PARSER' AND g.fest IS NOT NULL AND g.game IS NOT NULL
SQL
my @rows;
if (length $opt{'gameids'}) {
    my @ids = grep { /\A\d+\z/ } split /[,\s]+/, $opt{'gameids'};
    @rows = @{ $db->selectall_arrayref("$sql AND g.gameid IN (" . join(',', @ids) . ') ORDER BY g.gameid') };
}
else {
    @rows = @{ $db->selectall_arrayref("$sql AND g.gameid IN (1, 16899, 30650) ORDER BY g.gameid") };
    for my $tier (1 .. 4) {
        push @rows, @{ $db->selectall_arrayref("$sql AND d.size_tier = ? AND g.gameid NOT IN (1, 16899, 30650) ORDER BY random() LIMIT ?", undef, $tier, $opt{'limit'}) };
    }
}

my %n = ('games' => 0, 'differ' => 0, 'refused' => 0, 'fuse' => 0);
my $failed = 0;
my %skip   = map { $_ => 1 } qw(hotspots_incomplete envelopes_incomplete ver);

sub thawed ($blob) { return Storable::thaw(Compress::Zlib::uncompress($blob)) }

sub differing ($got, $want) {
    my @keys = grep { !$skip{$_} } sort keys %{ { %$got, %$want } };
    return grep { Gate::canon($got->{$_}) ne Gate::canon($want->{$_}) } @keys;
}

if ($opt{'spoil'}) {
    my ($gameid, $code, $fest_blob, $game_blob) = @{ $rows[0] };
    my $got = Games::Sokoban::Solver::Festival::Analysis::parse($code, 36_000);
    Games::Sokoban::Solver::Festival::Analysis::with_blok($got, thawed($game_blob)->{'blok'});
    $got = Games::Sokoban::Solver::Festival::Analysis::thaw(Games::Sokoban::Solver::Festival::Analysis::freeze($got));
    $got->{'width'} += 1;
    my @bad = differing($got, Games::Sokoban::Solver::Festival::Analysis::thaw($fest_blob));
    if (@bad) { say "spoil: an altered width of game $gameid is reported (@bad) -- the gate fires" }
    else      { say 'spoil: NOT CAUGHT'; $failed = 1 }
}

my %time;
for my $row (@rows) {
    my ($gameid, $code, $fest_blob, $game_blob, $tier) = @$row;
    ++$n{'games'};
    my $t0  = Time::HiRes::time();
    my $got = eval { Games::Sokoban::Solver::Festival::Analysis::parse($code, 36_000) };
    unless ($got) { say "REFUSED $gameid: " . (split /\n/, $@)[0]; ++$n{'refused'}; next }
    $time{$tier}[0] += Time::HiRes::time() - $t0;
    $time{$tier}[1]++;
    Games::Sokoban::Solver::Festival::Analysis::with_blok($got, thawed($game_blob)->{'blok'});

    # Compared as the engine gets it: frozen and thawed, as the stored one was.
    # Storable in network order writes a double as text to 15 places, so
    # gamma_table (powers of 0.95) differs from a fresh double in the last bits.
    $got = Games::Sokoban::Solver::Festival::Analysis::thaw(Games::Sokoban::Solver::Festival::Analysis::freeze($got));
    my $want = Games::Sokoban::Solver::Festival::Analysis::thaw($fest_blob);
    my @bad  = differing($got, $want);
    if (@bad) { say "game $gameid: fields differ (@bad)"; ++$n{'differ'} }
    if ($got->{'hotspots_incomplete'} or $got->{'envelopes_incomplete'}) { say "game $gameid: a fuse fired under a budget of ten hours?!"; ++$n{'differ'} }
    printf {*STDERR} "\r%d  game %d tier %d: %.1f s", $n{'games'}, $gameid, $tier, Time::HiRes::time() - $t0;
}
print {*STDERR} "\n";

# The fuses, on game 104 under a budget already spent (-1): both fire at their
# first check and are reported, and the hash still freezes. A spent budget,
# not a short one: the analysis reads the clock in whole seconds, so under a
# budget of 1 s a fuse fires only if a second boundary falls inside its part
# (seen: game 104 analysed in 0.4 s had the envelope fuse fire and the hotspot
# fuse not). Game 104 because its floor has more than one corral in reverse
# mode -- on a level with one (13858, 3, 1) the envelope analysis does not run
# and its flag is rightly 0 whatever the budget.
if ($opt{'fuse'}) {
    my ($code) = $db->selectrow_array('SELECT code FROM game_blob WHERE gameid = 104');
    my $t0     = Time::HiRes::time();
    my $cut    = Games::Sokoban::Solver::Festival::Analysis::parse($code, -1);
    my $took   = Time::HiRes::time() - $t0;
    $n{'fuse'} = $cut->{'hotspots_incomplete'} + $cut->{'envelopes_incomplete'};
    if ($n{'fuse'} == 2) { printf "fuse: game 104 under a spent budget: both fuses fired and are reported (%.1f s)\n", $took }
    else                 { say "fuse: game 104 under a spent budget: hotspots $cut->{'hotspots_incomplete'}, envelopes $cut->{'envelopes_incomplete'} -- expected both"; $failed = 1 }
    my $ok = eval { Games::Sokoban::Solver::Festival::Analysis::freeze($cut); 1 };
    unless ($ok) { say "fuse: freeze refused the cut analysis: $@"; $failed = 1 }
    my $whole = Games::Sokoban::Solver::Festival::Analysis::parse($code, 36_000);
    if ($whole->{'hotspots_incomplete'} or $whole->{'envelopes_incomplete'}) { say 'fuse: game 104 with ten hours: a fuse fired?!'; $failed = 1 }
}

say 'analysis time per game by tier (seconds):';
printf "  %d %3d %8.2f\n", $_, $time{$_}[1], $time{$_}[0] / $time{$_}[1] for sort keys %time;
$failed = 1 if $n{'differ'} or $n{'refused'};
exit Gate::verdict($failed, %n);
