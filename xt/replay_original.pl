#!/usr/bin/env perl
# The stored solutions of the Sokoban project, read by this distribution's two
# readings of a path.
#
#   perl xt/replay_original.pl --what stored    [--limit N] [--spoil]
#   perl xt/replay_original.pl --what firststep [--limit N] [--spoil]
#
# --what stored: N random solved paths of bestbet and firstbet (default 2000),
#   each on the board it was found on (game_blob.code). This tree's
#   Path::rebuilt must give, letter for letter, what the project's own
#   Games::Sokoban::Path::rebuilt gives (the original, loaded from the Sokoban
#   tree after this tree's lib), and Replay::check must accept the path.
# --what firststep: EVERY firstbet SOLVED row and every bestbet row with a path,
#   played on the ORIGINAL level (zdroj.code1, the level as read with the
#   unreachable cells walled) with the forced opening game_data.firststep in
#   front -- what the program prints. Replay::check must accept every one. It
#   also counts how many would fail on zdroj.code0 (the level with the
#   unreachable cells kept as filler), the board the project's web export
#   replays on: a goal in a walled-off region stays a goal there.
# --spoil: before the real run, one letter of a path is flipped (stored) or the
#   forced opening is left off a game that has one (firststep); the gate must
#   catch it or it is not a gate.
#
# Read-only against D:\Sokoban_data\db\Sokoban.sqlite3; PERL5LIB must be empty.
use v5.42;
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long ();
use Games::Sokoban::Solver::Path   ();
use Games::Sokoban::Solver::Replay ();
STDOUT->autoflush(1);

my %opt = ('what' => 'stored', 'limit' => 2000, 'spoil' => 0);
Getopt::Long::GetOptions(\%opt, 'what=s', 'limit=i', 'spoil!') or die "usage: replay_original.pl --what stored|firststep [--limit N] [--spoil]\n";
$opt{'what'} =~ /\A(?:stored|firststep)\z/ or die "--what must be stored or firststep\n";

my $db = Gate::db('Sokoban');

if ($opt{'what'} eq 'stored') {
    push @INC, Gate::baseline_lib();
    require Games::Sokoban::Path;    # the original, after this tree's lib
    my $half = int($opt{'limit'} / 2);
    my $rows = $db->selectall_arrayref(<<"SQL");
        SELECT gameid, code, path, 'bestbet' FROM (
            SELECT b.gameid, g.code, b.path FROM bestbet b JOIN game_blob g USING (gameid)
             WHERE b.path IS NOT NULL AND b.path <> '' ORDER BY random() LIMIT $half)
        UNION ALL
        SELECT gameid, code, path, 'firstbet' FROM (
            SELECT f.gameid, g.code, f.path FROM firstbet f JOIN game_blob g USING (gameid)
             WHERE f.status = 'SOLVED' ORDER BY random() LIMIT $half)
SQL
    my %n = ('paths' => 0, 'differ' => 0, 'refused' => 0, 'died' => 0);
    my $failed = 0;

    if ($opt{'spoil'}) {
        my ($gameid, $code, $path) = @{ $rows->[0] };
        substr($path, int(length($path) / 2), 1) = 'X';
        my $err = Games::Sokoban::Solver::Replay::check($code, $path);
        my $ok  = eval { Games::Sokoban::Solver::Path::rebuilt(Games::Sokoban::Solver::Path::level($code), 'path' => $path); 1 };
        if (defined $err and !$ok) { say "spoil: a flipped letter in game $gameid is refused by both readings -- the gate fires" }
        else                       { say "spoil: NOT CAUGHT (check: " . ($err // 'accepted') . ", rebuilt: " . ($ok ? 'lived' : 'died') . ')'; $failed = 1 }
    }

    for my $row (@$rows) {
        my ($gameid, $code, $path, $table) = @$row;
        ++$n{'paths'};
        my %level = Games::Sokoban::Solver::Path::level($code);
        my $ours  = eval { Games::Sokoban::Solver::Path::rebuilt(%level, 'path' => $path) };
        unless (defined $ours) { say "DIED  $table $gameid: " . (split /\n/, $@)[0]; ++$n{'died'}; next }
        my $orig = Games::Sokoban::Path::rebuilt(Games::Sokoban::Path::level($code), 'path' => $path);
        if ($ours ne $orig) { say "DIFFER $table $gameid: ours " . length($ours) . ' letters, the original ' . length($orig); ++$n{'differ'} }
        if (defined(my $err = Games::Sokoban::Solver::Replay::check($code, $path))) { say "REFUSED $table $gameid: $err"; ++$n{'refused'} }
    }
    $failed = 1 if $n{'differ'} or $n{'refused'} or $n{'died'};
    exit Gate::verdict($failed, %n);
}

# --what firststep
my $rows = $db->selectall_arrayref(<<'SQL');
    SELECT f.gameid, z.code0, z.code1, COALESCE(d.firststep, ''), f.path, 'firstbet'
      FROM firstbet f JOIN zdroj z USING (gameid) JOIN game_data d USING (gameid)
     WHERE f.status = 'SOLVED'
    UNION ALL
    SELECT b.gameid, z.code0, z.code1, COALESCE(d.firststep, ''), b.path, 'bestbet'
      FROM bestbet b JOIN zdroj z USING (gameid) JOIN game_data d USING (gameid)
     WHERE b.path IS NOT NULL AND b.path <> ''
SQL
my %n = ('paths' => 0, 'refused' => 0, 'with_opening' => 0, 'fail_on_code0' => 0);
my $failed = 0;

if ($opt{'spoil'}) {
    my ($with) = grep { length $_->[3] } @$rows;
    die "spoil: no game with a forced opening in the sample\n" unless $with;
    my ($gameid, $code0, $code1, $pre, $path) = @$with;
    my $err = Games::Sokoban::Solver::Replay::check($code1, $path);
    if (defined $err) { say "spoil: game $gameid without its forced opening is refused ($err) -- the gate fires" }
    else              { say "spoil: NOT CAUGHT -- game $gameid replays without its opening"; $failed = 1 }
}

for my $row (@$rows) {
    my ($gameid, $code0, $code1, $pre, $path, $table) = @$row;
    ++$n{'paths'};
    ++$n{'with_opening'} if length $pre;
    if (defined(my $err = Games::Sokoban::Solver::Replay::check($code1, $pre . $path))) {
        say "REFUSED $table $gameid on code1: $err";
        ++$n{'refused'};
    }
    ++$n{'fail_on_code0'} if defined Games::Sokoban::Solver::Replay::check($code0, $pre . $path);
    print {*STDERR} "\r$n{'paths'}" if $n{'paths'} % 500 == 0;
}
print {*STDERR} "\r";
$failed = 1 if $n{'refused'};
exit Gate::verdict($failed, %n);
