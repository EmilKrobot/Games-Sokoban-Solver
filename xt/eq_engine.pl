#!/usr/bin/env perl
# An engine of the distribution against its original in the Sokoban project,
# both loaded into ONE process (the original from C:/Workspace/Sokoban/lib,
# appended to the end of @INC) and run on the project's stored analyses with
# the same limit and the same fixed hash seed. The copy only rewires the
# modules the engine leans on, so it must SEARCH alike:
#
#   Firstbet, FirstBack  where both solve: the path written again from its
#                        pushes equally long and the same number of positions;
#                        a structural verdict (NOCP, GIVEUP, UNSOLVABLE) the
#                        same on both sides; TIMEOUT / MEMCAP skipped (the
#                        clock decides them)
#   Festival, Fest       where both solve: the same rebuilt path; the modes
#                        divide the limit among their phases, so positions
#                        depend on the clock and are not compared
#
# Every SOLVED path of either side is replayed by Replay::check and rewritten
# by Path::rebuilt; a path that fails either is UNPLAYABLE. A solve that dies
# is the verdict DIE. Nothing here touches the database but to read it.
#
#   PERL_HASH_SEED=0 PERL_PERTURB_KEYS=0
#   perl xt/eq_engine.pl --engine Firstbet|FirstBack|Festival|Fest
#                        [--limit S] [--gameids L] [--modes M,M] [--blok 0|1] [--spoil]
#
# Default games: 1 76 582 2614 8958 15218 23988 42343 11624 34209 (the set of
# the project's promotion gate), limit 15 s. --blok sets $BLOK_REPLACES
# (Festival) or $BLOK (Fest) on both sides, default 1. --spoil: our first mode
# against the original's second on game 1 -- the gate must report a MISMATCH.
# PERL5LIB must be empty.
use v5.42;
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long ();
use Games::Sokoban::Solver::Path   ();
use Games::Sokoban::Solver::Replay ();
STDOUT->autoflush(1);

my %opt = ('engine' => '', 'limit' => 15, 'gameids' => '', 'modes' => '', 'blok' => 1, 'spoil' => 0);
Getopt::Long::GetOptions(\%opt, 'engine=s', 'limit=f', 'gameids=s', 'modes=s', 'blok=i', 'spoil!')
    or die "usage: eq_engine.pl --engine E [--limit S] [--gameids L] [--modes M,M] [--blok 0|1] [--spoil]\n";
my %known = ('Firstbet' => 'game', 'FirstBack' => 'game', 'Festival' => 'fest', 'Fest' => 'analysis');
my $engine = $opt{'engine'};
die "--engine must be one of: " . join(' ', sort keys %known) . "\n" unless $known{$engine};
Gate::need_fixed_hash_seed();

my $column = $known{$engine};
my $ours   = "Games::Sokoban::Solver::$engine";
my $theirs = "Games::Sokoban::$engine";
push @INC, Gate::baseline_lib();
for my $pkg ($ours, $theirs) {
    (my $file = "$pkg.pm") =~ s{::}{/}g;
    require $file;
}
die "the original was not loaded from the Sokoban tree\n" unless $INC{'Games/Sokoban/' . $engine . '.pm'} =~ m{Sokoban/lib}i;
die "the copy was not loaded from this tree\n" unless $INC{"Games/Sokoban/Solver/$engine.pm"} =~ m{Games-Sokoban-Solver}i;

# The modes: the original's own list for Festival and Fest, the project's
# Portfolio for Firstbet, the one mode of FirstBack.
my @modes;
if (length $opt{'modes'}) { @modes = split /,/, $opt{'modes'} }
elsif ($engine eq 'Firstbet')  { require Games::Sokoban::Portfolio; @modes = Games::Sokoban::Portfolio::firstbet_modes() }
elsif ($engine eq 'FirstBack') { @modes = ('FIRSTBACK') }
else { no strict 'refs'; @modes = &{"${theirs}::modes"}() }

# Run control the same on both sides: quiet, no memory net, the blok switch.
for my $pkg ($ours, $theirs) {
    no strict 'refs';
    ${"${pkg}::QUIET"}  = 2;
    ${"${pkg}::MAX_GB"} = 0;
    ${"${pkg}::BLOK_REPLACES"} = $opt{'blok'} if $engine eq 'Festival';
    ${"${pkg}::BLOK"}          = $opt{'blok'} if $engine eq 'Fest';
}

my %died;
sub qsolve ($pkg, @args) {
    my @r = do {
        local *STDERR;
        open STDERR, '>', \my $junk;
        no strict 'refs';
        eval { &{"${pkg}::solve"}(@args) };
    };
    return @r if @r;
    $died{"$args[0] $args[3] $pkg"} = (split /\n/, "$@")[0] // 'died without a word';
    return ('DIE', undef, 0, 0);
}

# The length of a path written again from its pushes, -1 when it does not play.
sub rebuilt ($code, $path) {
    return eval { Games::Sokoban::Solver::Path::rebuilt(Games::Sokoban::Solver::Path::level($code), 'path' => $path // '') } // undef;
}

my $db  = Gate::db('Sokoban');
my @ids = length $opt{'gameids'} ? grep { /\A\d+\z/ } split /[,\s]+/, $opt{'gameids'} : (1, 76, 582, 2614, 8958, 15218, 23988, 42343, 11624, 34209);
my %n   = ('ok' => 0, 'mismatch' => 0, 'skip' => 0, 'unplayable' => 0, 'died' => 0);
my $failed = 0;

sub blob_of ($gameid) {
    my ($blob, $code) = $db->selectrow_array("SELECT $column, code FROM game_blob WHERE gameid = ? AND source = 'PARSER'", undef, $gameid);
    die "game $gameid: no stored $column\n" unless defined $blob;
    return ($blob, $code);
}

# One pair of answers compared; returns 'ok', 'mismatch' or 'skip' and prints.
sub compare ($gameid, $mode, $code, $a, $b, $what_a = 'ours', $what_b = 'orig') {
    my ($ar, $ap, undef, $an) = @$a;
    my ($br, $bp, undef, $bn) = @$b;
    for my $side ([$what_a, $ar, $ap], [$what_b, $br, $bp]) {
        my ($who, $reason, $path) = @$side;
        next unless $reason eq 'SOLVED';
        my $err = Games::Sokoban::Solver::Replay::check($code, $path // '');
        $err //= 'rebuilt refuses it' unless defined rebuilt($code, $path);
        next unless defined $err;
        ++$n{'unplayable'};
        printf "UNPLAYABLE g=%-6d %-11s %s: %s\n", $gameid, $mode, $who, $err;
    }
    if ($ar ne 'SOLVED' or $br ne 'SOLVED') {
        return 'skip' if $ar eq $br and $ar ne 'DIE';
        return 'skip' if $ar =~ /\A(?:TIMEOUT|MEMCAP|FAILED)\z/ and $br =~ /\A(?:TIMEOUT|MEMCAP|FAILED)\z/;
        printf "REASON   g=%-6d %-11s ours=%-9s orig=%s\n", $gameid, $mode, $ar, $br;
        return 'mismatch';
    }
    my ($ra, $rb) = (rebuilt($code, $ap), rebuilt($code, $bp));
    my ($ka, $kb);
    if ($engine eq 'Firstbet' or $engine eq 'FirstBack') {
        ($ka, $kb) = (join('|', length($ra // ''), $an), join('|', length($rb // ''), $bn));
    }
    else { ($ka, $kb) = ($ra // '-', $rb // '-') }
    return 'ok' if $ka eq $kb;
    printf "MISMATCH g=%-6d %-11s ours=[%s] orig=[%s]\n", $gameid, $mode, $ka, $kb;
    return 'mismatch';
}

if ($opt{'spoil'}) {
    die "spoil needs two modes\n" unless @modes >= 2;
    my ($blob, $code) = blob_of(1);
    my @a = qsolve($ours,   1, $blob, $opt{'limit'}, $modes[0]);
    my @b = qsolve($theirs, 1, $blob, $opt{'limit'}, $modes[1]);
    my $verdict = compare(1, "$modes[0]/$modes[1]", $code, \@a, \@b);
    if ($verdict eq 'mismatch') { say "spoil: our $modes[0] against the original's $modes[1] on game 1 is reported -- the gate fires" }
    else                        { say "spoil: NOT CAUGHT ($verdict)"; $failed = 1 }
}

for my $gameid (@ids) {
    my ($blob, $code) = blob_of($gameid);
    for my $mode (@modes) {
        my @a = qsolve($ours,   $gameid, $blob, $opt{'limit'}, $mode);
        my @b = qsolve($theirs, $gameid, $blob, $opt{'limit'}, $mode);
        my $verdict = compare($gameid, $mode, $code, \@a, \@b);
        ++$n{$verdict};
        printf {*STDERR} "\r%d %-11s %-9s %-9s %s   ", $gameid, $mode, $a[0], $b[0], $verdict;
    }
}
print {*STDERR} "\n";
$n{'died'} = scalar keys %died;
say "DIED $_: $died{$_}" for sort keys %died;
$failed = 1 if $n{'mismatch'} or $n{'unplayable'} or $n{'died'};
exit Gate::verdict($failed, %n);
