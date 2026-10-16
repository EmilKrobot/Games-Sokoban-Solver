use 5.042;
use strict;
use warnings;
use Config;

# The deadlock-pattern tables are 56-bit masks in plain integers and Storable
# records of 64-bit values; a perl built without 64-bit integers cannot run
# this distribution at all.  The wording makes CPAN Testers report NA, not FAIL.
die "OS unsupported: a perl with 64-bit integers (ivsize 8) is required\n" if $Config{'ivsize'} < 8;

use ExtUtils::MakeMaker 7.0;

WriteMakefile(
    NAME             => 'Games::Sokoban::Solver',
    VERSION_FROM     => 'lib/Games/Sokoban/Solver.pm',
    ABSTRACT_FROM    => 'lib/Games/Sokoban/Solver.pm',
    AUTHOR           => 'Jiri Broz <jiri.krobot.broz@gmail.com>',
    LICENSE          => 'perl_5',
    MIN_PERL_VERSION => '5.042000',

    EXE_FILES        => ['bin/soko-solver.pl'],

    PREREQ_PM => {

        # The one prerequisite outside the perl core: the priority queue of the
        # first-solution search (an XS module).
        'Array::Heap' => '3.22',

        # Core modules, declared so that cpanm and CPANTS see them.
        'Carp'           => 0,
        'Compress::Zlib' => 0,
        'Config'         => 0,
        'Digest::MD5'    => 0,
        'Exporter'       => 0,
        'Fcntl'          => 0,
        'File::Basename' => 0,
        'File::Path'     => 0,
        'Getopt::Long'   => 0,
        'JSON::PP'       => 0,
        'List::Util'     => '1.45',
        'POSIX'          => 0,
        'Pod::Usage'     => 0,
        'Scalar::Util'   => 0,
        'Storable'       => 0,
        'Term::ANSIColor' => 0,
        'Time::HiRes'    => 0,
        'constant'       => 0,
        'experimental'   => '0.032',
    },
    TEST_REQUIRES => {
        'Test::More' => '1.302',
    },
    META_MERGE => {
        'meta-spec' => { version => 2 },
        prereqs     => {
            runtime => {
                recommends => {

                    # Console width and colours on Windows; the whole-machine
                    # memory probe.  Every one of them is loaded inside an eval.
                    'Win32::API'           => 0,
                    'Win32::Console'       => 0,
                    'Win32::Console::ANSI' => 0,

                    # The optional on-disk search stores (--berkeley 1).
                    'BerkeleyDB' => '0.65',
                },
            },
        },
        resources => {
            repository => {
                type => 'git',
                url  => 'https://github.com/EmilKrobot/Games-Sokoban-Solver.git',
                web  => 'https://github.com/EmilKrobot/Games-Sokoban-Solver',
            },
            bugtracker => { web => 'https://github.com/EmilKrobot/Games-Sokoban-Solver/issues' },
        },
        no_index => { directory => [ 'xt', 'maint' ] },
    },
    test  => { TESTS => 't/*.t' },
    clean => { FILES => 'Games-Sokoban-Solver-*' },
);
