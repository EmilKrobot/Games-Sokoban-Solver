package Games::Sokoban::Solver::Memory;

# How much of the WHOLE MACHINE's memory is in use, in GiB -- the number the
# engines' memory net compares against their $MAX_GB.
#
# The quantity is the whole machine's, not this process's, on purpose: running
# out of memory is about the machine, and a solver that runs several searches at
# once in several threads has no process figure that would mean anything. So
# $MAX_GB is a whole-machine ceiling, and this module answers in the same unit on
# every platform where it can: Windows through one kernel call
# (GlobalMemoryStatusEx, about two microseconds), Linux through /proc/meminfo
# (MemTotal less MemAvailable). Where neither is available the answer is 0,
# which an engine reads as "below any ceiling" -- the net is off -- and this
# module says so once on STDERR.
#
# The answer is never undef: four engines compare it under
# `use warnings FATAL => 'uninitialized'`.
#
# Lineage: Handy::memory_usage of the Sokoban project (2026-08-27).

use v5.42;
use Exporter 'import';

our @EXPORT_OK = ('used_gb', 'total_gb', 'scope');
our $VERSION   = '0.01';

my $GIB = 1073741824;
my $Scope;    # 'system' once a probe has worked, 'none' when none does (announced once)
my $Read;     # the probe: returns (total, available) in bytes, or () when it failed

# Find the probe this machine has, once; try it once so that a probe that
# loads but does not answer is found out here and not inside a search.
sub _probe () {
    return $Read if defined $Scope;
    if ($^O eq 'MSWin32') {
        my $call = eval {
            require Win32::API;
            Win32::API->new('kernel32', 'GlobalMemoryStatusEx', 'P', 'N');
        };
        if ($call) {
            $Read = sub {

                # MEMORYSTATUSEX: dwLength, dwMemoryLoad, then seven 64-bit counts,
                # of which the first two are the total and the available physical memory.
                my $buf = pack 'L L Q Q Q Q Q Q Q', 64, (0) x 8;
                return () unless $call->Call($buf);
                my (undef, undef, $total, $avail) = unpack 'L L Q Q', $buf;
                return ($total, $avail);
            };
        }
    }
    elsif (-r '/proc/meminfo') {
        $Read = sub {
            open my $fh, '<', '/proc/meminfo' or return ();
            my ($total, $avail);
            while (my $line = <$fh>) {
                $total = $1 * 1024 if $line =~ /\AMemTotal:\s+(\d+)\s+kB/;
                $avail = $1 * 1024 if $line =~ /\AMemAvailable:\s+(\d+)\s+kB/;
            }
            close $fh;
            return (defined $total and defined $avail) ? ($total, $avail) : ();
        };
    }
    if ($Read and my @once = $Read->()) {
        $Scope = 'system';
    }
    else {
        $Scope = 'none';
        $Read  = undef;
        warn "Games::Sokoban::Solver::Memory: no way to read the machine's memory here -- the memory net is off\n";
    }
    return $Read;
}

# GiB of the machine's memory in use, three decimals; 0 when it cannot be read.
sub used_gb () {
    my $read = _probe() or return 0;
    my ($total, $avail) = $read->();
    return $total ? sprintf('%.3f', ($total - $avail) / $GIB) : 0;
}

# GiB of memory the machine has; 0 when it cannot be read.
sub total_gb () {
    my $read = _probe() or return 0;
    my ($total) = $read->();
    return $total ? sprintf('%.3f', $total / $GIB) : 0;
}

# 'system' when the numbers are the whole machine's, 'none' when there are none.
sub scope () {
    _probe();
    return $Scope;
}

1;

__END__

=head1 NAME

Games::Sokoban::Solver::Memory - the machine's memory in use, for the engines' memory net

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Memory ('used_gb', 'total_gb', 'scope');

    $Abort = 'MEMCAP' if $MAX_GB and used_gb() > $MAX_GB;
    my $suggested_ceiling = 0.8 * total_gb();
    say scope();     # 'system', or 'none' when nothing can be read here

=head1 DESCRIPTION

Every search engine of this distribution carries a memory net: a ceiling in
GiB above which it stops with the verdict C<MEMCAP> instead of running the
machine out of memory. The number it compares against is the B<whole
machine's> memory in use, read here: on Windows with one kernel call
(C<GlobalMemoryStatusEx> through L<Win32::API>), on Linux from
F</proc/meminfo> (C<MemTotal> less C<MemAvailable>). Both answer in the same
unit, so a ceiling means the same on both.

Where neither way exists the functions return 0, which no ceiling is below, so
the net is off; the module says so once on STDERR, and C<scope> reports
C<'none'>. The answer is never C<undef>.

=head1 FUNCTIONS

Nothing is exported by default; ask for the names.

=over 4

=item used_gb

GiB of the machine's memory in use, with three decimals, or 0.

=item total_gb

GiB of memory the machine has, or 0.

=item scope

C<'system'> when the numbers are the whole machine's, C<'none'> when they
cannot be read here.

=back

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
