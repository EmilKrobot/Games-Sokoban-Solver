#!/usr/bin/env perl
# Console and Memory against the Handy.pm they were taken from.
#
#   perl xt/console_vs_handy.pl [--spoil]
#
# podil() must give Handy's string on 200 random (number, base) pairs with and
# without the decimals argument; used_gb() must be within 0.1 GiB of
# Handy::memory_usage() read a moment apart (both the whole machine's memory
# on this Windows box). --spoil compares podil against Handy's with one argument
# swapped, which must differ.
#
# Loads Handy from the Sokoban tree (after this tree's lib); PERL5LIB must be empty.
use v5.42;
use FindBin ();
use lib "$FindBin::Bin/../lib", "$FindBin::Bin/lib";
use Gate;
use Getopt::Long ();
use Games::Sokoban::Solver::Console ('podil');
use Games::Sokoban::Solver::Memory  ('used_gb', 'scope');
STDOUT->autoflush(1);
my %opt = ('spoil' => 0);
Getopt::Long::GetOptions(\%opt, 'spoil!') or die "usage: console_vs_handy.pl [--spoil]\n";
push @INC, Gate::baseline_lib();
require Handy;
srand(20261015);
my %n      = ('podil' => 0, 'podil_differ' => 0);
my $failed = 0;

if ($opt{'spoil'}) {
    my ($a1, $b1) = (37, 1000);
    if   (podil($a1, $b1) ne Handy::podil($b1, $a1)) {say 'spoil: swapped arguments differ from Handy -- the gate fires'}
    else                                             {say 'spoil: NOT CAUGHT'; $failed = 1}
}
for my $trial (1 .. 200) {
    my $number = int(rand 100000);
    my $base   = $trial % 10 == 0 ? 0 : int(rand 100000);
    for my $deci (undef, 0, 1, 2, 3) {
        ++$n{'podil'};
        my $ours   = podil($number, $base, $deci);
        my $theirs = Handy::podil($number, $base, $deci);
        if ($ours ne $theirs) {
            say "podil($number, $base, " . ($deci // 'undef') . "): ours '$ours', Handy '$theirs'";
            ++$n{'podil_differ'};
        }
    }
}
my $ours   = used_gb();
my $theirs = Handy::memory_usage();
$n{'used_gb'}      = $ours;
$n{'handy_memory'} = $theirs;
$n{'scope'}        = scope();
if (abs($ours - $theirs) > 0.1) {say "used_gb $ours against Handy::memory_usage $theirs: more than 0.1 GiB apart"; $failed = 1}
$failed = 1 if $n{'podil_differ'};
exit Gate::verdict($failed, %n);
