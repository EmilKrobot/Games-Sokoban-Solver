#!/usr/bin/env perl
# Normalize each given text file to LF line endings, in place.
#
# This tree is LF in the working tree as well as in the repository (see
# .gitattributes): the tarball `make dist` builds is read by a Linux perl, and a
# CRLF shebang line is "bad interpreter" there. The editor tools of the
# author's Windows session may write CRLF; this puts a file right at once
# instead of waiting for a commit-and-checkout round trip through git.
#
# Idempotent: unifies any mix (LF or CRLF) to pure LF. Binaries (the Storable
# tables among them) are skipped.
#
#   perl maint/lf.pl FILE [FILE ...]
#   git ls-files | perl -ne 'chomp; print "$_\n" unless /\.stor$/' | xargs perl maint/lf.pl
use v5.42;
STDOUT->autoflush(1);

@ARGV or die "usage: perl maint/lf.pl FILE [FILE ...]\n";
for my $f (@ARGV) {
    if (!-f $f) { warn "skip $f: not a file\n"; next }
    if (-B $f)  { next }
    open my $in, '<:raw', $f or do { warn "skip $f: $!\n"; next };
    local $/;
    my $c = <$in>;
    close $in;
    (my $n = $c) =~ s/\r\n/\n/g;
    next if $n eq $c;
    open my $out, '>:raw', $f or do { warn "write $f: $!\n"; next };
    print {$out} $n;
    close $out;
    say "LF: $f";
}
