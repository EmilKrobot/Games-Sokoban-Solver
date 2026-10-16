#!/usr/bin/env perl
# Every module lib/ and bin/ load against what Makefile.PL declares: a module
# that is neither in PREREQ_PM nor in the perl core (Module::CoreList) is
# missing from the declaration; a declared one nothing loads is dead weight.
# The distribution's own modules, pragmas and the optional branch (BerkeleyDB,
# Win32::*, the thread modules loaded at run time) are left out.
#
#   perl maint/prereqs.pl
use v5.42;
use FindBin ();
use File::Find ();
use Module::CoreList ();

my $root = "$FindBin::Bin/..";
my %used;
File::Find::find({
    'wanted' => sub {
        return unless /\.p[lm]\z/;
        open my $fh, '<', $File::Find::name or die "$File::Find::name: $!";
        while (my $line = <$fh>) {
            last if $line =~ /^__END__/;
            $used{$1} = 1 while $line =~ /(?:^|[;{]\s*)(?:use|require)\s+([A-Z][\w:]*)/g;    # `use` at the top, `require` inside a statement too
        }
        close $fh;
    },
    'no_chdir' => 1,
}, "$root/lib", "$root/bin");

open my $mk, '<', "$root/Makefile.PL" or die $!;
my $makefile = do { local $/; <$mk> };
close $mk;
my ($prereq) = $makefile =~ /PREREQ_PM\s*=>\s*\{(.*?)\n\s*\},/s or die 'no PREREQ_PM';
my %declared = map { $_ => 1 } $prereq =~ /'([\w:]+)'\s*=>/g;
my ($recommends) = $makefile =~ /recommends\s*=>\s*\{(.*?)\},/s;
my %recommended = map { $_ => 1 } ($recommends // '') =~ /'([\w:]+)'\s*=>/g;

my %skip = map { $_ => 1 } 'threads', 'threads::shared', 'Thread::Queue', 'BerkeleyDB';
my $failed = 0;
for my $m (sort keys %used) {
    next if $m =~ /\AGames::Sokoban::Solver\b/;
    next if $skip{$m} or $recommended{$m} or $m =~ /\AWin32::/;
    next if $declared{$m};
    my $core = Module::CoreList::first_release($m);
    if ($core) { say "core, undeclared: $m (since perl $core)" }
    else       { say "NOT DECLARED and not core: $m"; $failed = 1 }
}
for my $m (sort keys %declared) {
    next if $used{$m} or $m =~ /\A[a-z]/;    # a pragma is loaded as `use experimental ...`, not counted above
    say "declared, loaded by nothing: $m";
}
say $failed ? 'FAILED' : 'ALL OK';
exit $failed;
