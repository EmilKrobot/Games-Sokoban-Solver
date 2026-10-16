package Games::Sokoban::Solver::Config;

# THE SETTINGS OF THE PROGRAM: what each one means, its default, where the ini
# file lives, how it is read and written, the questions of the first run, and
# the three layers -- the defaults under the ini under the command line.
#
# The file is plain `key = value` lines with `;` or `#` comments, read by a
# parser of its own (Config::Tiny cuts a value at ' ; ', which a directory
# name may contain), and written with the meaning and the default of every key
# beside it, so that the file is its own documentation. The defaults are the
# author's panel: they are numbers in this file, changed by editing them.
use v5.42;
use warnings FATAL => 'uninitialized';
use Carp                           ();
use File::Path                     ();
use Games::Sokoban::Solver::Memory ();
our $VERSION = '0.01';
my $NAME = 'soko-solver';

# EVERY KEY, in the order of the file: its default (a value or a code that
# finds one on this machine), its check, and what it means.
my @KEYS = (
    ['jobs',         \&_jobs_default, 'int1',  'worker threads the race may take (1 = one task at a time, no threads)'],
    ['time',         60,              'secs',  'seconds for one mode of the race on a level (ORDER always has 30)'],
    ['optimal',      60,              'secs0', 'seconds for the proof of the shortest solution (0 = do not look for it)'],
    ['optimal_mode', 'DIAL',          'omode', 'the regime of the proof: DIAL, ASTAR or FIFO'],
    ['fest_budget',  120, 'secs', 'seconds for the Festival analysis of a level (two of its parts stop when it is spent)'],
    [
        'blok_budget', 30, 'budget',
        'seconds for the deadlock patterns of a level (0 = none, -1 = complete; calibrated: 30 recovers 57-99 % of them)'
    ],
    ['maxgb',    0, 'gb0', 'stop a search when the whole machine uses more than this many GB of memory (0 = no ceiling)'],
    ['berkeley', \&_berkeley_default,   'bool',  'keep the search of long runs on disk through BerkeleyDB (1) or in memory (0)'],
    ['berkeley_root',  \&_root_default, 'dir',   'where the BerkeleyDB stores live'],
    ['berkeley_cache', 0.5,             'cache', 'memory pool of one store in GB, at most 3'],
    ['berkeley_from',  600,             'secs0', 'from which limit in seconds a mode goes to disk (0 = always)'],
    ['pull',           1,               'int1',  'pull searches (BACKWARD, FIRSTBACK) in flight at once'],
    ['forward',        3,               'int1',  'forward modes of Firstbet in flight at once'],
    ['hold',           0,      'gb0',    'no counted mode starts while the machine uses more than this many GB (0 = off)'],
    ['format',         'path', 'format', 'what is printed for a level: path, sok, report or json'],
);
my %KEY = map {$_->[0] => $_} @KEYS;

# The questions of the first run, in order; a key not here is in the file with
# its default and is changed by editing it.
my @ASK = (
    ['jobs',           'How many threads may the solver take?'],
    ['time',           'How many seconds does one mode get for the first solution?'],
    ['optimal',        'How many seconds for the proof of the shortest solution (0 = none)?'],
    ['maxgb',          'A memory ceiling for the whole machine in GB (0 = none)?'],
    ['berkeley',       'Keep the search of long runs on disk through BerkeleyDB (1) or not (0)?'],
    ['berkeley_root',  'Where should the stores live?'],
    ['berkeley_cache', 'How large a memory pool for one store, in GB (at most 3)?'],
    ['berkeley_from',  'From which limit in seconds should a mode go to disk (0 = always)?'],
);

sub _processors () {
    return $ENV{'NUMBER_OF_PROCESSORS'} if ($ENV{'NUMBER_OF_PROCESSORS'} // '') =~ /\A\d+\z/;
    if (open my $fh, '<', '/proc/cpuinfo') {
        my $n = grep {/^processor\s*:/} <$fh>;
        close $fh;
        return $n if $n;
    }
    my $n = `nproc 2>/dev/null`;
    return $1 if defined $n and $n =~ /(\d+)/;
    return 1;
}

# processors - 1, at least 1, at most 8: the race is a CPU race, and one core
# is left to the caller and the system.
sub _jobs_default () {
    my $n = _processors() - 1;
    return $n < 1 ? 1 : $n > 8 ? 8 : $n;
}
sub _berkeley_default () {return eval {require BerkeleyDB; 1} ? 1 : 0}
sub _root_default ()     {return dir() . '/berkeley'}

=head1 NAME

Games::Sokoban::Solver::Config - the settings of soko-solver: defaults, the ini file, the questions

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Config ();

    my %cfg = Games::Sokoban::Solver::Config::defaults();
    my $ini = Games::Sokoban::Solver::Config::path();          # where the file lives
    my %cfg = Games::Sokoban::Solver::Config::resolve(\%cli);  # defaults < ini < command line
    Games::Sokoban::Solver::Config::ask(\%cfg, \*STDIN, \*STDOUT);
    Games::Sokoban::Solver::Config::save($ini, \%cfg);
    my %set   = Games::Sokoban::Solver::Config::load($ini);    # what the file says
    my @wrong = Games::Sokoban::Solver::Config::check(\%cfg);

=head1 DESCRIPTION

The settings of C<soko-solver.pl> in one place: what each one means, its
default, where the ini file lives, how the file is read and written, the
questions of the first run, and the three layers -- the defaults under the
file under the command line. The file is plain C<key = value> lines with C<;>
or C<#> comments, written with the meaning and the default of every key beside
it, so that it is its own documentation. The defaults are the author's panel:
numbers in this module, changed by editing them.

=head1 FUNCTIONS

=head2 names, describe

The keys in the order of the file, and the one-line meaning of a key.

=cut

sub names ()        {return map {$_->[0]} @KEYS}
sub describe ($key) {return ($KEY{$key} // Carp::croak("Config: no setting '$key'"))->[3]}

=head2 defaults

    my %cfg = defaults();

Every key with its default: the numbers of this file, plus three found on this
machine -- C<jobs> (the processors less one, 1 to 8), C<berkeley> (1 only when
the BerkeleyDB module loads), C<berkeley_root> (C<berkeley> under the
directory of the ini file).

=cut

sub defaults () {
    return map {$_->[0] => (ref $_->[1] eq 'CODE' ? $_->[1]->() : $_->[1])} @KEYS;
}

=head2 dir, path

    my $dir  = dir();     # the directory of the settings
    my $file = path();    # dir() . '/soko-solver.ini'

On Windows C<%APPDATA%\soko-solver>, elsewhere C<$XDG_CONFIG_HOME/soko-solver>
or C<~/.config/soko-solver>; C<SOKO_SOLVER_HOME> in the environment overrides
both.

=cut

sub dir () {
    my $dir = $ENV{'SOKO_SOLVER_HOME'};
    unless (defined $dir and length $dir) {
        if ($^O eq 'MSWin32') {$dir = ($ENV{'APPDATA'} // $ENV{'USERPROFILE'} // '.') . "/$NAME"}
        else {
            my $base = $ENV{'XDG_CONFIG_HOME'};
            $base = ($ENV{'HOME'} // '.') . '/.config' unless defined $base and length $base;
            $dir  = "$base/$NAME";
        }
    }
    $dir =~ tr{\\}{/};
    return $dir;
}
sub path () {return dir() . "/$NAME.ini"}

=head2 load

    my %from_file = load($file);

The keys the file sets, with their values as strings; a key the module does
not know is refused with its line, and so is a line that is not C<key = value>.
A missing file is an error too (the caller asks first).

=cut

sub load ($file) {
    open(my $fh, '<:raw', $file) or Carp::croak("Config: cannot read $file: $!");
    my %cfg;
    while (my $line = <$fh>) {
        $line =~ s/\A\xEF\xBB\xBF// if $. == 1;    # a byte order mark left by an editor
        $line =~ s/[\r\n]+\z//;
        next if $line =~ /^\s*(?:[;#]|\z)/;
        next if $line =~ /^\s*\[[^\]]*\]\s*\z/;    # a section heading is allowed and means nothing
        if ($line =~ /^\s*([A-Za-z_]\w*)\s*=\s*(.*?)\s*\z/) {
            my ($key, $value) = ($1, $2);
            Carp::croak("Config: $file line $.: no setting '$key'") unless $KEY{$key};
            $value =~ s/\A"(.*)"\z/$1/;            # a value may be quoted
            $cfg{$key} = $value;
            next;
        }
        Carp::croak("Config: $file line $.: not a 'key = value' line: $line");
    }
    close $fh;
    return %cfg;
} ## end sub load

=head2 save

    save($file, \%cfg);

The file, every key with its meaning and default in a comment above it; the
directory is made when it is missing. A hash that does not pass L</check> is
refused.

=cut

sub save ($file, $cfg) {
    my @wrong = check($cfg);
    Carp::croak("Config: refusing to write: " . join('; ', @wrong)) if @wrong;
    (my $dir = $file) =~ s{[\\/][^\\/]*\z}{};
    File::Path::make_path($dir) if length $dir and !-d $dir;
    open(my $fh, '>', $file) or Carp::croak("Config: cannot write $file: $!");
    print {$fh} "; $NAME settings -- the defaults under the command line; `$NAME --init` asks the questions again\n";
    my %default = defaults();
    for my $k (@KEYS) {
        my ($key) = @$k;
        print {$fh} "\n; $k->[3]\n; default: $default{$key}\n$key = " . ($cfg->{$key} // $default{$key}) . "\n";
    }
    close($fh) or Carp::croak("Config: cannot write $file: $!");
    return;
} ## end sub save

=head2 check

    my @problems = check(\%cfg);

Every value held to its kind: C<jobs>, C<pull>, C<forward> whole numbers of at
least 1; the seconds non-negative numbers (C<blok_budget> may be -1 for the
complete table); C<optimal_mode> one of DIAL, ASTAR, FIFO; C<format> one of
path, sok, report, json; C<berkeley> 0 or 1; C<berkeley_cache> between 0.001
and 3; C<maxgb> and C<hold> non-negative. Returns the problems as sentences.

=cut

my %CHECK = (
    'int1'   => sub ($v) {$v =~ /\A\d+\z/ && $v >= 1 ? undef : 'a whole number of at least 1'},
    'secs'   => sub ($v) {_num($v) && $v > 0         ? undef : 'a number of seconds above 0'},
    'secs0'  => sub ($v) {_num($v) && $v >= 0        ? undef : 'a number of seconds (0 for none)'},
    'budget' => sub ($v) {_num($v) && $v >= -1       ? undef : 'a number of seconds (0 for none, -1 for the complete table)'},
    'gb0'    => sub ($v) {_num($v) && $v >= 0        ? undef : 'a number of GB (0 for none)'},
    'bool'   => sub ($v) {$v eq '0' || $v eq '1'     ? undef : '0 or 1'},
    'dir'    => sub ($v) {length $v                  ? undef : 'a directory'},
    'cache'  => sub ($v) {_num($v) && $v >= 0.001 && $v <= 3   ? undef : 'a pool in GB between 0.001 and 3'},
    'omode'  => sub ($v) {$v =~ /\A(?:DIAL|ASTAR|FIFO)\z/      ? undef : 'DIAL, ASTAR or FIFO'},
    'format' => sub ($v) {$v =~ /\A(?:path|sok|report|json)\z/ ? undef : 'path, sok, report or json'},
);
sub _num ($v) {return $v =~ /\A-?(?:\d+\.?\d*|\.\d+)\z/ ? 1 : 0}

sub check ($cfg) {
    my @problems;
    for my $k (@KEYS) {
        my ($key, undef, $kind) = @$k;
        my $v = $cfg->{$key};
        push @problems, "$key is not set" and next unless defined $v;
        my $wrong = $CHECK{$kind}->($v);
        push @problems, "$key = '$v' is not $wrong" if defined $wrong;
    }
    push @problems, "unknown setting '$_'" for grep {!$KEY{$_}} sort keys %$cfg;
    return @problems;
}

=head2 resolve

    my %cfg = resolve(\%cli, 'ini' => $file, 'no_ini' => 0);

The three layers: the defaults, under them the ini file (C<ini>, or
L</"dir, path">; left out when it does not exist or C<no_ini> is set), under them
the command line (the keys of C<%cli> that are defined). The result is checked;
a wrong value dies naming it.

=cut

sub resolve ($cli, %opt) {
    my %cfg  = defaults();
    my $file = $opt{'ini'} // path();
    if (!$opt{'no_ini'} and -f $file) {
        my %from = load($file);
        $cfg{$_} = $from{$_} for keys %from;
    }
    for my $key (keys %$cli) {
        Carp::croak("Config: no setting '$key'") unless $KEY{$key};
        $cfg{$key} = $cli->{$key} if defined $cli->{$key};
    }
    my @wrong = check(\%cfg);
    Carp::croak('Config: ' . join('; ', @wrong)) if @wrong;
    return %cfg;
} ## end sub resolve

=head2 ask

    ask(\%cfg, \*STDIN, \*STDOUT);

The questions of the first run, each with the value the hash holds as the
offer (Enter takes it; C<maxgb> offers 80 % of the machine's memory where the
machine says how much it has). An answer that does not fit its kind is said and
asked again. The BerkeleyDB questions are asked only where the module loads;
without it C<berkeley> is set to 0 and the three others keep their values.

=cut

sub ask ($cfg, $in, $out) {
    my $total = Games::Sokoban::Solver::Memory::total_gb();
    my $berk  = _berkeley_default();
    print {$out} "The settings of $NAME. Enter takes the value offered in brackets.\n";
    for my $q (@ASK) {
        my ($key, $question) = @$q;
        if ($key =~ /\Aberkeley/ and !$berk) {
            $cfg->{'berkeley'} = 0;
            next;
        }
        my $offer = $cfg->{$key};
        $offer = sprintf('%d', 0.8 * $total) if $key eq 'maxgb' and $total and !$cfg->{'maxgb'};
        while (1) {
            print {$out} "$question [$offer] ";
            my $line = <$in>;
            $line = '' unless defined $line;
            $line =~ s/\A\s+|\s+\z//g;
            my $value = length $line ? $line : $offer;
            my $wrong = $CHECK{ $KEY{$key}[2] }->($value);
            unless (defined $wrong) {$cfg->{$key} = $value; last}
            print {$out} "  '$value' is not $wrong\n";
            last unless length $line;    # the offer itself cannot be wrong twice: keep what is there
        }
        last if $key eq 'berkeley' and !$cfg->{'berkeley'} and @ASK;    # no stores: the three store questions are moot
    } ## end for my $q (@ASK)
    return $cfg;
} ## end sub ask
1;
__END__

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
