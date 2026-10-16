# The POD of every module and of the program parses (Test::Pod where it is
# installed), and every module has the sections perlmodstyle asks for.
use v5.42;
use Test::More;
use File::Find ();
my @files;
File::Find::find({ 'wanted' => sub {push @files, $File::Find::name if /\.(?:pm|pod|pl)\z/}, 'no_chdir' => 1 }, 'lib', 'bin');
@files = sort @files;
ok(@files >= 28, 'the modules, the two pod files and the program found (' . scalar(@files) . ')');
SKIP: {
    skip 'Test::Pod is not installed', scalar @files unless eval {require Test::Pod; Test::Pod->VERSION(1.22); 1};
    Test::Pod::pod_file_ok($_) for @files;
}

# A .pm whose POD lives in a .pod beside it is documented by that file.
my %pod_beside = map {s/\.pod\z/.pm/r => 1} grep {/\.pod\z/} @files;
for my $f (grep {/\.pm\z/} @files) {
    next if $pod_beside{$f};
    open my $fh, '<', $f or die "$f: $!";
    my $text = do {local $/; <$fh>};
    close $fh;
    my %head = map {$_ => 1} $text =~ /^=head1\s+(\S.*?)\s*$/mg;
    for my $want ('NAME', 'SYNOPSIS', 'DESCRIPTION', 'AUTHOR', 'COPYRIGHT AND LICENSE') {
        ok($head{$want}, "$f has =head1 $want");
    }
}
for my $f (grep {/\.pod\z/} @files) {
    open my $fh, '<', $f or die "$f: $!";
    my $text = do {local $/; <$fh>};
    close $fh;
    my %head = map {$_ => 1} $text =~ /^=head1\s+(\S.*?)\s*$/mg;
    ok($head{$_}, "$f has =head1 $_") for 'NAME', 'SYNOPSIS', 'DESCRIPTION', 'AUTHOR', 'COPYRIGHT AND LICENSE';
    unlike(
        $text,
        qr/\bGames::Sokoban::(?!Solver\b)\w|\bGames::Berkeley\b|\bHandy\b/,
        "$f names no module of the Sokoban project as if it were here"
    );
}
done_testing;
