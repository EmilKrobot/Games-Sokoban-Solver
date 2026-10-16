#!/usr/bin/env perl
# Code::prepare against the Code stage of the Sokoban project, on the games of
# its collection: the record it returns from zdroj.code1 must equal the stored
# game_blob.code_blob (thawed) key for key, its board game_blob.code, and its
# forced opening game_data.firststep.
#
#   perl xt/eq_code.pl [--limit N | --all] [--spoil]
#
# Default: 3000 random games plus 1, 36610, 8245, 4596 (long forced openings).
# --all: the whole collection (about a quarter of an hour).
# --spoil: one floor cell of the first game's code1 is made a wall before
# prepare; the gate must report that game.
#
# Read-only; PERL5LIB must be empty.
use v5.42;
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long                 ();
use Compress::Zlib               ();
use Storable                     ();
use Games::Sokoban::Solver::Code ();
STDOUT->autoflush(1);
my %opt = ('limit' => 3000, 'all' => 0, 'spoil' => 0);
Getopt::Long::GetOptions(\%opt, 'limit=i', 'all!', 'spoil!') or die "usage: eq_code.pl [--limit N | --all] [--spoil]\n";
my $db  = Gate::db('Sokoban');
my $sql = <<'SQL';
    SELECT z.gameid, z.code1, g.code, g.code_blob, COALESCE(d.firststep, '')
      FROM zdroj z JOIN game_blob g USING (gameid) JOIN game_data d USING (gameid)
     WHERE g.source = 'PARSER' AND g.code_blob IS NOT NULL
SQL
$sql .=
    $opt{'all'}
    ? ' ORDER BY z.gameid'
    : " AND (z.gameid IN (1, 36610, 8245, 4596) OR random() % 10 = 0) ORDER BY random() LIMIT $opt{'limit'}";
my $rows   = $db->selectall_arrayref($sql);
my %n      = ('games' => 0, 'record_differ' => 0, 'code_differ' => 0, 'opening_differ' => 0, 'refused' => 0, 'with_opening' => 0);
my $failed = 0;

# The fire test first, on its own: one floor cell walled, the record must differ.
if ($opt{'spoil'}) {
    my ($gameid, $code1, $code, $blob) = @{ $rows->[0] };
    substr($code1, index($code1, '0'), 1) = '9';
    my %got  = eval {Games::Sokoban::Solver::Code::prepare($code1)};
    my $want = Storable::thaw(Compress::Zlib::uncompress($blob));
    delete $want->{'md5'};
    if (!%got or Gate::canon(\%got) ne Gate::canon($want)) {
        say "spoil: a walled floor cell of game $gameid changes the record -- the gate fires";
    }
    else {say 'spoil: NOT CAUGHT'; $failed = 1}
}
for my $row (@$rows) {
    my ($gameid, $code1, $code, $blob, $pre) = @$row;
    ++$n{'games'};
    ++$n{'with_opening'} if length $pre;
    my %got = eval {Games::Sokoban::Solver::Code::prepare($code1)};
    unless (%got) {say "REFUSED $gameid: " . (split /\n/, $@)[0]; ++$n{'refused'}; next}
    my $want = Storable::thaw(Compress::Zlib::uncompress($blob));
    delete $want->{'md5'};
    my $differ = 0;

    if (Gate::canon(\%got) ne Gate::canon($want)) {
        my @keys = grep {Gate::canon($got{$_}) ne Gate::canon($want->{$_})} sort keys %{ { %got, %$want } };
        say "record differs: $gameid (keys @keys)";
        ++$n{'record_differ'};
        $differ = 1;
    }
    if ($got{'code'} ne $code)     {say "code differs: $gameid" unless $differ;                            ++$n{'code_differ'}}
    if ($got{'firststep'} ne $pre) {say "opening differs: $gameid ours '$got{'firststep'}' stored '$pre'"; ++$n{'opening_differ'}}
    print {*STDERR} "\r$n{'games'}" if $n{'games'} % 200 == 0;
} ## end for my $row (@$rows)
print {*STDERR} "\r";
$failed = 1 if $n{'record_differ'} or $n{'code_differ'} or $n{'opening_differ'} or $n{'refused'};
exit Gate::verdict($failed, %n);
