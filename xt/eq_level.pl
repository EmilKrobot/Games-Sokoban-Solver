#!/usr/bin/env perl
# Level::normalize against the zdroj table of the Sokoban project: every level
# ever read into the project, decoded back to text and normalized here, must
# give the stored code0 and code1 byte for byte.
#
#   perl xt/eq_level.pl [--limit N] [--spoil]
#
# zdroj.orig_code is the level's text as it was read, rows joined by newlines
# (zdroj.pl's $Real_orig), so it is split on them and handed over as it is --
# zdroj kept the blanks on the right as width, and so does normalize (read()
# is what cuts them). Every row of
# the table takes part, isbig = 1 rows included (in the distribution the size
# is a note, not a refusal); zdroj holds no level with boxes and goals of
# different numbers (zdroj.pl skipped those), so no refusal is expected.
#
# --spoil changes one digit of a stored code1 before comparing; the gate must
# report it.
use v5.42;
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long ();
use Games::Sokoban::Solver::Level ();
STDOUT->autoflush(1);

my %opt = ('limit' => 0, 'spoil' => 0);
Getopt::Long::GetOptions(\%opt, 'limit=i', 'spoil!') or die "usage: eq_level.pl [--limit N] [--spoil]\n";

my $db  = Gate::db('Sokoban');
my $sql = 'SELECT gameid, orig_code, code0, code1, isbig, nbox, ncell FROM zdroj ORDER BY gameid';
$sql .= " LIMIT $opt{'limit'}" if $opt{'limit'};
my $sth = $db->prepare($sql);
$sth->execute;

my %n      = ('levels' => 0, 'code0_differ' => 0, 'code1_differ' => 0, 'refused' => 0, 'ring' => 0, 'isbig' => 0);
my $failed = 0;
my $spoiled = 0;

while (my ($gameid, $orig, $code0, $code1, $isbig, $nbox, $ncell) = $sth->fetchrow_array) {
    ++$n{'levels'};
    ++$n{'isbig'} if $isbig;
    my @rows = split /\n/, $orig, -1;    # as read, blanks on the right included: zdroj kept them as width
    my ($c0, $c1, $info) = eval { Games::Sokoban::Solver::Level::normalize(\@rows) };
    unless (defined $c1) { say "REFUSED $gameid: " . (split /\n/, $@)[0]; ++$n{'refused'}; next }
    ++$n{'ring'} if $info->{'ring'};
    if ($opt{'spoil'} and !$spoiled) {
        ++$spoiled;
        substr($code1, index($code1, '0'), 1) = '9';
        say "spoil: one digit of game $gameid's stored code1 changed -- it must be reported below";
    }
    if ($c0 ne $code0) { say "code0 differs: $gameid"; ++$n{'code0_differ'} }
    if ($c1 ne $code1) { say "code1 differs: $gameid"; ++$n{'code1_differ'} }
    if ($info->{'nbox'} != $nbox) { say "nbox differs: $gameid ours $info->{'nbox'} stored $nbox"; ++$n{'code1_differ'} }
    print {*STDERR} "\r$n{'levels'}" if $n{'levels'} % 1000 == 0;
}
print {*STDERR} "\r";
if ($opt{'spoil'}) {
    if ($n{'code1_differ'} == 1) { say 'spoil: the changed digit was the one difference reported -- the gate fires'; $n{'code1_differ'} = 0 }
    else                         { say 'spoil: NOT CAUGHT as the one difference'; $failed = 1 }
}
$failed = 1 if $n{'code0_differ'} or $n{'code1_differ'} or $n{'refused'};
exit Gate::verdict($failed, %n);
