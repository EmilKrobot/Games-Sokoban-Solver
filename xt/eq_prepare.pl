#!/usr/bin/env perl
# The facade's prepare() against the Sokoban project's stored analyses, from
# the level's TEXT (zdroj.orig_code) the way the program reads it: code1 must
# equal zdroj.code1, the forced opening game_data.firststep, the Parser's
# analysis game_blob.game key for key (bloks by the rules of eq_parser.pl:
# equal where the pattern was done to its largest size, a subset of the stored
# table always), the Festival analysis game_blob.fest field for field, the Fest
# record game_blob.analysis key for key; the bloks dealt out to a POOL of
# workers must equal the serial ones when the table is complete and be a
# superset of them under a budget; and the stored first solution with the
# opening in front must play through full_path().
#
#   perl xt/eq_prepare.pl [--limit N] [--budget S] [--jobs N] [--gameids L] [--spoil]
#
# Default: game 1, games 36610 8245 4596 (long forced openings) and N random
# games per size tier (N = 3, so 16 games; the Festival analysis of a large
# level takes up to minutes). The bloks are complete (budget -1) for games of
# at most 8 boxes and under --budget seconds (60) above; the pool has --jobs
# workers (4). --spoil: the stored path WITHOUT the opening must not play on
# the first game that has one. Read-only; PERL5LIB must be empty.
use v5.42;
no warnings 'once';
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long                               ();
use Compress::Zlib                             ();
use Storable                                   ();
use Time::HiRes                                ();
use Games::Sokoban::Solver                     ();
use Games::Sokoban::Solver::Replay             ();
use Games::Sokoban::Solver::Festival::Analysis ();
STDOUT->autoflush(1);
my %opt = ('limit' => 3, 'budget' => 60, 'jobs' => 4, 'gameids' => '', 'spoil' => 0);
Getopt::Long::GetOptions(\%opt, 'limit=i', 'budget=f', 'jobs=i', 'gameids=s', 'spoil!')
    or die "usage: eq_prepare.pl [--limit N] [--budget S] [--jobs N] [--gameids L] [--spoil]\n";
my $db  = Gate::db('Sokoban');
my $sql = <<'SQL';
    SELECT z.gameid, z.orig_code, z.code1, g.game, g.fest, g.analysis, COALESCE(d.firststep, ''), d.size_tier, d.nbox,
           (SELECT path FROM firstbet f WHERE f.gameid = z.gameid AND f.status = 'SOLVED')
      FROM zdroj z JOIN game_blob g USING (gameid) JOIN game_data d USING (gameid)
     WHERE g.source = 'PARSER' AND g.game IS NOT NULL AND g.fest IS NOT NULL AND g.analysis IS NOT NULL
SQL
my @rows;

if (length $opt{'gameids'}) {
    my @ids = grep {/\A\d+\z/} split /[,\s]+/, $opt{'gameids'};
    @rows = @{ $db->selectall_arrayref("$sql AND z.gameid IN (" . join(',', @ids) . ') ORDER BY z.gameid') };
}
else {
    @rows = @{ $db->selectall_arrayref("$sql AND z.gameid IN (1, 36610, 8245, 4596) ORDER BY z.gameid") };
    for my $tier (1 .. 4) {
        push @rows,
            @{
                $db->selectall_arrayref(
                    "$sql AND d.size_tier = ? AND z.gameid NOT IN (1, 36610, 8245, 4596) ORDER BY random() LIMIT ?",
                    undef, $tier, $opt{'limit'})
             };
    }
}
sub thawed ($blob) {return Storable::thaw(Compress::Zlib::uncompress($blob))}

# the vectors of a blok table as a set of "bx,t,vector" strings
sub vector_set ($blok) {
    my %set;
    for my $bx (keys %$blok) {
        for my $t (keys %{ $blok->{$bx} }) {$set{ "$bx,$t," . unpack('H*', $_) } = 1 for @{ $blok->{$bx}{$t} }}
    }
    return \%set;
}
my %n = (
    'games'           => 0,
    'code1_differ'    => 0,
    'opening_differ'  => 0,
    'game_differ'     => 0,
    'blok_differ'     => 0,
    'blok_extra'      => 0,
    'pool_differ'     => 0,
    'fest_differ'     => 0,
    'analysis_differ' => 0,
    'path_fail'       => 0,
    'refused'         => 0,
    'complete'        => 0,
    'cut'             => 0,
    'no_path'         => 0
);
my $failed = 0;
my $pool   = Games::Sokoban::Solver::pool('jobs' => $opt{'jobs'});
say 'pool: ' . ($pool->threaded ? "$opt{'jobs'} threads" : 'serial');
if ($opt{'spoil'}) {
    my ($row) = grep {length $_->[6] and defined $_->[9]} @rows;
    if ($row) {
        my ($gameid, undef, $code1, undef, undef, undef, $pre, undef, undef, $path) = @$row;
        my $why = Games::Sokoban::Solver::Replay::check($code1, $path);
        if (defined $why) {
            say "spoil: game $gameid's stored path without its opening of "
                . length($pre)
                . " letters does not play ($why) -- the gate fires";
        }
        else {say 'spoil: NOT CAUGHT'; $failed = 1}
    }
    else {say 'spoil: no game with an opening and a path in the set'; $failed = 1}
}
for my $row (@rows) {
    my ($gameid, $orig, $code1, $game_blob, $fest_blob, $analysis_blob, $pre, $tier, $nbox, $path) = @$row;
    ++$n{'games'};
    my @rows_of = split /\n/, $orig, -1;
    my $budget  = $nbox <= 8 ? -1 : $opt{'budget'};
    my $t0      = Time::HiRes::time();
    my $p       = eval {Games::Sokoban::Solver::prepare('rows' => \@rows_of, 'blok_budget' => $budget, 'fest_budget' => 36_000)};
    unless ($p) {say "REFUSED $gameid: " . (split /\n/, $@)[0]; ++$n{'refused'}; next}
    my $t1 = Time::HiRes::time();
    my $pooled =
        Games::Sokoban::Solver::prepare('rows' => \@rows_of, 'blok_budget' => $budget, 'want' => ['game'], 'pool' => $pool);
    my $t2 = Time::HiRes::time();
    if ($p->{'code1'} ne $code1) {say "game $gameid: code1 differs"; ++$n{'code1_differ'}}

    if ($p->{'firststep'} ne $pre) {
        say "game $gameid: opening differs: ours '$p->{'firststep'}' stored '$pre'";
        ++$n{'opening_differ'};
    }
    if ($p->{'solved_by_opening'}) {say "game $gameid: solved by its opening -- nothing more to compare"; next}

    # the Parser's analysis, as the engines get it
    my $got  = thawed($p->{'game_blob'});
    my $want = thawed($game_blob);
    my %skip = map  {$_ => 1} qw(blok gate has_gate homes);
    my @bad  = grep {!$skip{$_} and Gate::canon($got->{$_}) ne Gate::canon($want->{$_})} sort keys %{ { %$got, %$want } };
    if (@bad) {say "game $gameid: game keys differ (@bad)"; ++$n{'game_differ'}}

    # the bloks: ours a subset of the stored, equal where complete
    my ($ours, $theirs, $pooled_set) =
        (vector_set($got->{'blok'}), vector_set($want->{'blok'}), vector_set($pooled->{'game'}{'blok'}));
    my @extra = grep {!$theirs->{$_}} keys %$ours;
    if (@extra) {say "game $gameid: " . scalar(@extra) . ' vector(s) the stored table does not have'; ++$n{'blok_extra'}}
    if ($p->{'blok_complete'}) {
        ++$n{'complete'};
        my @missing = grep {!$ours->{$_}} keys %$theirs;
        if (@missing) {say "game $gameid: complete, yet " . scalar(@missing) . ' stored vector(s) missing'; ++$n{'blok_differ'}}
        if (join("\0", sort keys %$pooled_set) ne join("\0", sort keys %$ours)) {
            say "game $gameid: the pool's bloks differ from the serial ones";
            ++$n{'pool_differ'};
        }
    }
    else {
        ++$n{'cut'};
        my @fewer = grep {!$pooled_set->{$_}} keys %$ours;
        if (@fewer) {
            say "game $gameid: the pool found " . scalar(@fewer) . ' vector(s) fewer than the serial run under the same budget';
            ++$n{'pool_differ'};
        }
        my @more = grep {!$theirs->{$_}} keys %$pooled_set;
        if (@more) {
            say "game $gameid: the pool found " . scalar(@more) . ' vector(s) the stored table does not have';
            ++$n{'blok_extra'};
        }
    }

    # the Festival analysis: fields but ver, the fuses and (unless complete) the bloks
    {
        my $f    = Games::Sokoban::Solver::Festival::Analysis::thaw($p->{'fest_blob'});
        my $w    = Games::Sokoban::Solver::Festival::Analysis::thaw($fest_blob);
        my %skip = map  {$_ => 1} 'ver', 'hotspots_incomplete', 'envelopes_incomplete', ($p->{'blok_complete'} ? () : 'blok');
        my @bad  = grep {!$skip{$_} and Gate::canon($f->{$_}) ne Gate::canon($w->{$_})} sort keys %{ { %$f, %$w } };
        if (@bad) {say "game $gameid: fest fields differ (@bad)"; ++$n{'fest_differ'}}
        if (@{ $p->{'fest_incomplete'} }) {
            say "game $gameid: a Festival fuse fired under a budget of ten hours?!";
            ++$n{'fest_differ'};
        }
    }

    # the Fest record (it carries the blok table, so that key only where complete)
    {
        my $a   = thawed($p->{'analysis_blob'});
        my $w   = thawed($analysis_blob);
        my @bad = grep {($p->{'blok_complete'} or $_ ne 'blok') and Gate::canon($a->{$_}) ne Gate::canon($w->{$_})}
            sort keys %{ { %$a, %$w } };
        if (@bad) {say "game $gameid: analysis keys differ (@bad)"; ++$n{'analysis_differ'}}
    }

    # the stored first solution through full_path
    if (defined $path) {
        my $full = eval {Games::Sokoban::Solver::full_path($p, $path)};
        unless (defined $full) {say "game $gameid: full_path refuses the stored path: " . (split /\n/, $@)[0]; ++$n{'path_fail'}}
        elsif  (length $full > length($pre) + length($path)) {
            say "game $gameid: full_path came out LONGER than opening + path";
            ++$n{'path_fail'};
        }
    }
    else {++$n{'no_path'}}
    printf "%3d  game %6d tier %d nbox %2d: %d patterns, bloks %s, serial %.1f s, pool %.1f s\n", $n{'games'}, $gameid, $tier,
        $nbox,
        scalar @{ $p->{'blok_report'} }, ($p->{'blok_complete'} ? 'complete' : 'CUT'), $t1 - $t0, $t2 - $t1;
} ## end for my $row (@rows)
$pool->close;
$pool->join;
$failed = 1
    if grep {$n{$_}}
    qw(code1_differ opening_differ game_differ blok_differ blok_extra pool_differ fest_differ analysis_differ path_fail refused);
exit Gate::verdict($failed, %n);
