#!/usr/bin/env perl
# WHAT DOES THE REST OF THE TREE REACH IN EACH MODULE? -- the distribution's
# form of the Sokoban project's ai/module_surface.pl --subs, over every module
# at once. For every sub a module declares: is it called anywhere (its own
# file included, by name, by &name, by ->name, by \&name or as a quoted word
# in a dispatch table)? For every `our`: who outside reaches it -- lib/ or
# bin/ (PRODUCTION: the contract), t/ or xt/ only (TESTS: a test's convenience
# is not a reason for a module to hand out its insides), or nobody (NOWHERE:
# plain `my`)? And two things that may not be in lib/ or bin/ at all: a name
# of the Sokoban project (Games::X that is not Games::Sokoban::Solver, Handy)
# and a bare exit (a module ends a search, not the program).
#
#   perl xt/surface.pl [--module F] [--all]
#
# The two hard rules fail the run (exit 1). Uncalled subs and unreached `our`
# are ADVICE, judged one by one: a sub may be a method the engine calls by
# name it builds at run time, an `our` may be a knob the author sets. --all
# prints every name with its readers, not only the findings. No database.
use v5.42;
use FindBin      ();
use File::Find   ();
use Getopt::Long ();
STDOUT->autoflush(1);
my %opt = ('module' => '', 'all' => 0, 'strict' => 0);
Getopt::Long::GetOptions(\%opt, 'module=s', 'all!', 'strict!') or die "usage: surface.pl [--module F] [--all] [--strict]\n";
my $root = "$FindBin::Bin/..";
$root =~ tr{\\}{/};

# every perl file of the tree, with the directory it belongs to
my @files;
for my $d ('lib', 'bin', 't', 'xt') {
    File::Find::find(
        {
            'wanted' => sub {
                return unless /\.(?:p[lm]|t)\z/;
                (my $path = $File::Find::name) =~ tr{\\}{/};
                push @files, [$d, $path];
            },
            'no_chdir' => 1,
        },
        "$root/$d"
    );
}
my %text;
for my $pair (@files) {
    open my $fh, '<:raw', $pair->[1] or die "$pair->[1]: $!";
    my $t = do {local $/; <$fh>};
    close $fh;
    $t =~ s/\r\n/\n/g;

    # POD and comments are prose: a name in them is not a reader (a # after a
    # sigil or inside a regex character class is code; a whole-line comment and
    # a comment set off by blanks are what is cut)
    $t =~ s/^=\w.*?^=cut\s*$//msg;
    $t =~ s/^=\w.*\z//ms;
    $t =~ s/^\s*#.*$//mg;
    $t =~ s/(?<=\s)\s#\s.*$//mg;
    $text{ $pair->[1] } = $t;
} ## end for my $pair (@files)
my @modules = grep {$_->[0] eq 'lib' and $_->[1] =~ /\.pm\z/} @files;
@modules = grep {$_->[1] =~ /\Q$opt{'module'}\E/} @modules if length $opt{'module'};
my $failed = 0;
my %n      = (
    'modules'     => 0,
    'subs'        => 0,
    'uncalled'    => 0,
    'our'         => 0,
    'our_tests'   => 0,
    'our_nowhere' => 0,
    'foreign'     => 0,
    'exit'        => 0
);

# --- the two hard rules, over lib/ and bin/ -----------------------------------------
for my $pair (grep {$_->[0] eq 'lib' or $_->[0] eq 'bin'} @files) {
    my ($d, $f) = @$pair;
    my $t = $text{$f};
    (my $short = $f) =~ s{\A\Q$root\E/}{};
    my $line = 0;
    for my $l (split /\n/, $t) {
        ++$line;
        (my $code = $l) =~ s/(?<![\$\@%\\])#.*//;    # a comment is not code (a # after a sigil is a variable)
        if ($code =~ /\bGames::(?!Sokoban::Solver\b)\w|\bHandy\b|\bGames::Sokoban::(?!Solver\b)\w/) {
            say "$short:$line: a name of the Sokoban project: $l";
            ++$n{'foreign'};
        }
        if ($code =~ /(?<![\w>\$:])exit\b(?!\s*=>)/ and $code !~ /\bPOSIX::_exit\b/ and $d eq 'lib') {
            say "$short:$line: a bare exit in a module: $l";
            ++$n{'exit'};
        }
    }
} ## end for my $pair (grep {$_->...})

# --- subs and ours, module by module -------------------------------------------------
for my $pair (@modules) {
    my ($d, $f) = @$pair;
    my $t = $text{$f};
    (my $short = $f) =~ s{\A\Q$root\E/}{};
    my ($pkg) = $t =~ /^package\s+([\w:]+)\s*[;{]/m or do {say "$short: no package line"; next};
    ++$n{'modules'};
    my @subs = $t =~ /^\s*sub\s+([A-Za-z_]\w*)/mg;
    my @ours;
    while ($t =~ /^\s*our\s+(\(.*?\)|[\$\@%][A-Za-z_]\w*)/msg) {
        my $decl = $1;
        push @ours, $decl =~ /[\$\@%]([A-Za-z_]\w*)/g;
    }
    my %seen;
    @subs = grep {!$seen{$_}++} @subs;
    %seen = ();
    @ours = grep {!$seen{$_}++ and $_ ne 'VERSION' and $_ ne 'EXPORT_OK'} @ours;    # the two every module has for perl itself
    $n{'subs'} += @subs;
    $n{'our'}  += @ours;

    # a sub's callers: the module's own text less its definition lines, then
    # every other file. A quoted word counts as a call (a dispatch table) unless
    # --strict, which then also lists the subs a quoted word alone vouches for.
    (my $own = $t) =~ s/^\s*sub\s+[A-Za-z_]\w*.*$//mg;
    my @uncalled;
    for my $s (grep {!/\A(?:BEGIN|END|DESTROY|import|AUTOLOAD)\z/} @subs) {
        my $call   = qr/(?:\b|&|\\&|->)\Q$s\E\s*(?:\(|\b)/;
        my $quoted = qr/['"]\Q$s\E['"]/;
        next if $own =~ $call;
        next if grep {$_->[1] ne $f and $text{ $_->[1] } =~ /(?:\Q$pkg\E::|&|->|\\&|::)\Q$s\E\b/} @files;
        my $by_word = ($own =~ $quoted or grep {$_->[1] ne $f and $text{ $_->[1] } =~ $quoted} @files) ? 1 : 0;
        next if $by_word and !$opt{'strict'};
        push @uncalled, $s . ($by_word ? ' (a quoted word only)' : '');
    }
    if (@uncalled) {
        ++$n{'uncalled'} for @uncalled;
        say "$short: " . scalar(@uncalled) . ' sub(s) called from nowhere: ' . join(' ', @uncalled);
    }

    # an our's readers outside the module, qualified or symbolic
    for my $o (@ours) {
        my %where;
        for my $other (grep {$_->[1] ne $f} @files) {
            my $u = $text{ $other->[1] };
            $where{ $other->[0] } = 1
                if $u =~ /\Q$pkg\E::\Q$o\E\b/
                or $u =~ /::\Q$o\E["'](?:\}|\))/
                or $u =~ /\{"\$\{?\w+\}?::\Q$o\E"\}/;
        }
        my $bucket = ($where{'lib'} or $where{'bin'}) ? 'PRODUCTION' : %where ? 'TESTS' : 'NOWHERE';
        ++$n{'our_tests'}   if $bucket eq 'TESTS';
        ++$n{'our_nowhere'} if $bucket eq 'NOWHERE';
        say "$short: our \$$o -> $bucket" . (%where ? ' (' . join(',', sort keys %where) . ')' : '')
            if $opt{'all'} or $bucket ne 'PRODUCTION';
    } ## end for my $o (@ours)
} ## end for my $pair (@modules)
$failed = 1 if $n{'foreign'} or $n{'exit'};
say(($failed ? 'FAILED' : 'ALL OK') . ' (' . join(', ', map {"$_ $n{$_}"} sort keys %n) . ')');
say 'Advice, not a verdict: an uncalled sub may be reached by a name built at run time, an our may be a knob.'
    if $n{'uncalled'}
    or $n{'our_tests'}
    or $n{'our_nowhere'};
exit $failed;
