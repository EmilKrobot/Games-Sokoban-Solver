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
my @modules = ('Games::Sokoban::Solver');

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

done_testing;
