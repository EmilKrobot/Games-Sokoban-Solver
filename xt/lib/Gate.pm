package Gate;

# The common kit of the author gates in xt/: what every gate must check before
# it can be believed, in one place, so that no gate forgets one of them.
#
# Every gate here compares a module of this distribution with its original in
# the Sokoban project, or with that project's database.  Three things can make
# such a comparison lie, and this module refuses to run under any of them:
#
#   * PERL5LIB set.  The Sokoban project's lib/ is on it and holds the
#     originals of every module copied here, and a Games/Sokoban/Solver.pm that
#     is not this distribution's.  A module this tree lacks would be found there
#     silently and the gate would compare the original with itself.
#   * a random hash seed, where a search is compared.  Perl's hash order decides
#     tie-breaks in the search, so two correct copies differ run to run unless
#     PERL_HASH_SEED and PERL_PERTURB_KEYS are 0 in the environment (perl reads
#     them at start-up; setting them inside the program is too late).
#   * a database opened for writing.  The project's databases are the ground
#     truth and a campaign of the author may be running on them; they are
#     opened read-only here, always.
#
# The gates that need the ORIGINAL module load it from the Sokoban tree; that
# directory is appended to the END of @INC by baseline_lib(), after this tree's
# lib/, so a name both trees have resolves to this tree.
use v5.42;
use Carp         ();
use Data::Dumper ();
our $VERSION = '0.01';
my $SOKOBAN = 'C:/Workspace/Sokoban';
my $DB_DIR  = $ENV{'SOKOBAN_DB_DIR'} // 'D:/Sokoban_data/db';

# Refused at load time: a gate that got this far with PERL5LIB set has already
# compiled against the wrong tree.
if (length($ENV{'PERL5LIB'} // '')) {
    die "Gate: PERL5LIB is set ($ENV{'PERL5LIB'}) -- the gates run with it EMPTY,"
        . " or a module this tree lacks is found in the Sokoban tree silently.\n"
        . "  PowerShell:  \$env:PERL5LIB=''\n";
}

# For a gate that compares a search: both environment variables must be '0'.
sub need_fixed_hash_seed () {
    for my $v ('PERL_HASH_SEED', 'PERL_PERTURB_KEYS') {
        my $set = $ENV{$v} // '';
        $set =~ s/^\s+|\s+$//g;
        next if $set eq '0';
        die "Gate: refusing to compare a search without deterministic hashing -- $v is not 0.\n"
            . "  PowerShell:  \$env:PERL_HASH_SEED='0'; \$env:PERL_PERTURB_KEYS='0'\n";
    }
    return;
}

# The Sokoban tree's lib/, appended to the END of @INC, for a gate that loads
# the original of a module beside its copy.  Returns the directory.
sub baseline_lib () {
    my $lib = "$SOKOBAN/lib";
    push @INC, $lib unless grep {$_ eq $lib} @INC;
    return $lib;
}
sub sokoban_dir () {return $SOKOBAN}

# A read-only handle on one of the project's databases ('Sokoban' or
# 'Patterns').  DBI and DBD::SQLite are author tools: they are not
# prerequisites of the distribution and are loaded only here.
sub db ($name) {
    require DBI;
    require DBD::SQLite;
    my $file = "$DB_DIR/$name.sqlite3";
    Carp::croak("Gate: no database $file") unless -f $file;
    return DBI->connect(
        "dbi:SQLite:dbname=$file",
        '', '',
        {
            'RaiseError'        => 1,
            'PrintError'        => 0,
            'sqlite_open_flags' => DBD::SQLite::OPEN_READONLY(),
        }
    );
} ## end sub db

# One canonical text for a data structure, so two structures compare as
# strings: sorted keys, no indentation, no variable name.
sub canon ($ref) {
    local $Data::Dumper::Sortkeys = 1;
    local $Data::Dumper::Indent   = 0;
    local $Data::Dumper::Terse    = 1;
    local $Data::Dumper::Deepcopy = 1;
    return Data::Dumper::Dumper($ref);
}

# The verdict line every gate ends with; the exit status follows it.
sub verdict ($failed, %count) {
    my $counts = join(', ', map {"$_ $count{$_}"} sort keys %count);
    say(($failed ? 'FAILED' : 'ALL OK') . ($counts ? " ($counts)" : ''));
    return $failed ? 1 : 0;
}
1;
__END__

=head1 NAME

Gate - the common kit of the author gates of Games::Sokoban::Solver

=head1 SYNOPSIS

    use lib 'xt/lib';
    use Gate;                      # dies when PERL5LIB is set

    Gate::need_fixed_hash_seed();  # for a gate that compares a search
    my $db = Gate::db('Sokoban');  # read-only
    push @INC, Gate::baseline_lib();   # the originals, after this tree's lib

    exit Gate::verdict($failed, 'ok' => $ok, 'bad' => $bad);

=head1 DESCRIPTION

Every gate in F<xt/> compares a module of this distribution with its original
in the Sokoban project, or with that project's database, and three things can
make such a comparison lie: a PERL5LIB that leads to the originals, a random
hash seed where a search is compared, and a database opened for writing. This
module refuses the first at load time and offers one function for each of the
other two, so that no gate has to carry those checks itself.

=head1 FUNCTIONS

=over 4

=item need_fixed_hash_seed

Dies unless C<PERL_HASH_SEED> and C<PERL_PERTURB_KEYS> are both C<0> in the
environment.

=item baseline_lib

Appends the Sokoban tree's F<lib/> to the end of C<@INC> and returns it.

=item db NAME

A read-only DBI handle on F<Sokoban.sqlite3> or F<Patterns.sqlite3> under the
project's database directory (C<SOKOBAN_DB_DIR> overrides it).

=item canon REF

The canonical Data::Dumper text of a structure (sorted keys, one line).

=item verdict FAILED, COUNTS

Prints C<ALL OK> or C<FAILED> with the counts and returns the exit status.

=back

=cut
