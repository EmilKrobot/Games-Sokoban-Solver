# Every module of the distribution loads, and loads from THIS tree.
#
# The second half is the point: the author's machine carries another project's
# modules on PERL5LIB, among them a Games/Sokoban/Solver.pm that is not this
# one.  A module the distribution forgot to rename or to copy would be found
# there silently, so every %INC entry under Games/Sokoban/ must come from the
# directory this test loaded the main module from, and none of the other
# project's packages may be defined afterwards.
use v5.42;
use Test::More;
use Config;

ok($Config{'ivsize'} >= 8, 'perl has 64-bit integers (the pattern masks need them)');

# Grows with every step of the plan: one name per module of the distribution.
my @modules = (
    'Games::Sokoban::Solver',          'Games::Sokoban::Solver::Data',   'Games::Sokoban::Solver::Console',
    'Games::Sokoban::Solver::Memory',  'Games::Sokoban::Solver::Heap',   'Games::Sokoban::Solver::Munkres',
    'Games::Sokoban::Solver::Path',    'Games::Sokoban::Solver::Replay',
);

use_ok($_) for @modules;

my $main = $INC{'Games/Sokoban/Solver.pm'};
ok(defined $main, 'Games::Sokoban::Solver was loaded from a file');
(my $root = $main) =~ s{[\\/]Games[\\/]Sokoban[\\/]Solver\.pm\z}{};
$root =~ tr{\\}{/};
note("library root: $root");

for my $file (sort grep { m{\AGames/Sokoban/} } keys %INC) {
    (my $from = $INC{$file}) =~ tr{\\}{/};
    ok(index($from, $root) == 0, "$file comes from this tree, not from PERL5LIB ($from)");
}

ok(!defined &Handy::backline,          'nothing loaded the other project\'s Handy');
ok(!defined &Games::Munkres::assign,   'nothing loaded the other project\'s Games::Munkres');
ok(!Games::Numeric->can('new'),        'nothing loaded the other project\'s Games::Numeric');
ok(!defined &Games::Sokoban::Firstbet::solve, 'nothing loaded the other project\'s Firstbet');

# A file that is not a .pm travels with the modules and is installed beside
# them: this is what the data tables of the distribution rely on.
ok(-f "$root/Games/Sokoban/Solver/Data/README.txt", 'a non-.pm file under lib/ is installed beside the modules');

# The four tables, by size on disk (a line-ending conversion or a truncated
# copy changes it) and by what they hold once thawed.
my %table = (
    'hole_templates.stor'   => [2128,   50],
    'hole_pattern.stor'     => [13599,  120],
    'corridor_pattern.stor' => [175588, 225],
    'fest_patterns.stor'    => [37956,  2],
);
for my $name (sort keys %table) {
    my ($bytes, $entries) = @{ $table{$name} };
    my $file = Games::Sokoban::Solver::Data::path($name);
    is(-s $file, $bytes, "$name is $bytes bytes");
    my $ref = Games::Sokoban::Solver::Data::load($name);
    is(ref $ref, 'HASH', "$name thaws to a hash");
    is(scalar keys %$ref, $entries, "$name holds $entries entries");
}
{
    my $fest = Games::Sokoban::Solver::Data::load('fest_patterns.stor');
    is(scalar @{ $fest->{'patterns'} },      116, 'fest_patterns: 116 push patterns');
    is(scalar @{ $fest->{'pull_patterns'} }, 60,  'fest_patterns: 60 pull patterns');
}
ok(!eval { Games::Sokoban::Solver::Data::load('no_such.stor'); 1 }, 'a missing table dies');
like($@, qr/no table .*no_such\.stor/, '... naming the file');

done_testing;
