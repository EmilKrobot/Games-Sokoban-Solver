package Games::Sokoban::Solver::Portfolio;

# ONE HOME FOR THE POLICY OF THE RACE, and ONE ENGINE FACE FOR FOUR ENGINES.
#
# The policy: which modes exist (27, in four engines), in what order the race
# starts them, which of them has a limit of its own, which KIND a mode is for
# the caps on what runs at once, and which analysis each engine takes. The
# Sokoban project learned the hard way that a mode list copied into eight
# drivers drifts -- a mode promoted into an engine never reached three of them
# for eleven days -- so every list here is either a literal in ONE place or
# asked of the engine that owns it.
#
# The face: Games::Sokoban::Solver::Race calls ${engine}::solve($label, $blob,
# $limit, $mode) on one package, and two pools in one process deadlock (join
# waits on every thread there is), so the engine is a property of the TASK:
# solve() below routes by the NAME of the mode -- FF_* to Festival, E_* to
# Fest, FIRSTBACK to FirstBack, everything else to Firstbet (or to its
# BerkeleyDB twin when $BERK is on) -- and copies the race signal down and
# $LastFail back up. Every engine is loaded here, because the program always
# starts them all and the workers are clones of that moment.
#
# Lineage: Games::Sokoban::Portfolio 0.01 and Games::Sokoban::Tandem 0.02 of
# the Sokoban project, and the panel of waves of its driver wave_batch.pl
# (2026-10-13/14), which is where the order of the race comes from.

use v5.42;
use warnings FATAL => 'uninitialized';
no warnings 'once';
use Carp ();
use Games::Sokoban::Solver::Firstbet  ();
use Games::Sokoban::Solver::FirstBack ();
use Games::Sokoban::Solver::Festival  ();
use Games::Sokoban::Solver::Fest      ();

our $VERSION = '0.01';

# The race signal and the per-task control word, set by Race on THIS package
# (it is the engine it was given) and copied down to the engine a mode belongs
# to at call time; $LastFail carried back up the same way.
our ($LastFail, $RACE_FLAG, $RACE_GID, $CTL);

# $BERK = 1 sends Firstbet's modes to Games::Sokoban::Solver::Firstbet::Berk,
# the twin that keeps the search on disk; the caller loads that module (and
# sets its $CACHE and $STORE_PER_MODE) before the pool starts.
our $BERK = 0;

# The ten Firstbet modes. THE ORDER IS DATA, NOT TIDINESS: to a race it means
# nothing, to a caller that runs them one after another and stops at the first
# solve it is the whole cost, so the strongest go first.
my @FIRSTBET = qw(FEATURE PUSH_ASSIGN BACKWARD ORDER MOVE_SUM PUSH_SCORE ROUTE MOVE_SCORE FLOW CONVEYOR);

# The optimal solver's three regimes, in the order to try them on a level
# nothing has proved: DIAL is the cheapest per node and reports a lower bound,
# ASTAR proves the open boards DIAL cannot, FIFO proves least and mines best.
my @SOLVER = qw(DIAL ASTAR FIFO);

# THE ORDER OF THE RACE: the waves of the Sokoban project's driver for its
# unsolved levels, read off its matrix of every mode on every solved level
# (who solved most, then who adds most), one after another -- CONVEYOR last,
# because on most levels it answers NOCP at once and was never the only mode to
# solve a level.
my @RACE = qw(
    ORDER FF_BICON FF_BASE FF_REV FF_MAXDIST2 FF_GIRL FF_HF E_MAXDIST2 FIRSTBACK MOVE_SUM PUSH_ASSIGN
    FF_MAXDIST BACKWARD FEATURE MOVE_SCORE E_BICON E_MAXDIST E_HF E_REV E_BASE E_DRAGONFLY
    FLOW PUSH_SCORE ROUTE FF_DRAGONFLY E_GIRL CONVEYOR
);

# A mode with a limit of its own, whatever the race's: ORDER's 355 of 357
# solves of large levels came within 30 seconds.
my %OWN_LIMIT = ('ORDER' => 30);

# THE KINDS, for what may run at once: a pull search takes 9-15 GB of memory on
# a large level, a forward mode of Firstbet 2.5 (up to 7), the rest well under
# one (measured on the project's unsolved levels at 900 s). The default caps:
# one pull search and three forward modes in flight.
my %KIND = (
    (map { $_ => 'pull' } 'BACKWARD', 'FIRSTBACK'),
    (map { $_ => 'forward' } 'FEATURE', 'FLOW', 'MOVE_SCORE', 'MOVE_SUM', 'PUSH_ASSIGN', 'PUSH_SCORE', 'ROUTE'),
);
my %CAP = ('forward' => 3, 'pull' => 1);

=head1 NAME

Games::Sokoban::Solver::Portfolio - the 27 modes, the order of the race, and one engine face for four engines

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Portfolio ();

    my @order = Games::Sokoban::Solver::Portfolio::race_order();     # 27 names
    my $pkg   = Games::Sokoban::Solver::Portfolio::engine_for('FF_HF');
    my $what  = Games::Sokoban::Solver::Portfolio::blob_for('E_REV');  # 'analysis'
    my $kind  = Games::Sokoban::Solver::Portfolio::kind_of('FEATURE');  # 'forward'
    my $own   = Games::Sokoban::Solver::Portfolio::own_limit('ORDER');  # 30, or undef
    my @wrong = Games::Sokoban::Solver::Portfolio::consistent();        # () when every mode is in its place

    # as the engine of a Race pool
    my ($reason, $path, $secs, $nseen) = Games::Sokoban::Solver::Portfolio::solve($label, $blob, $limit, $mode);

=head1 SUBROUTINES

=head2 firstbet_modes, firstback_modes, festival_modes, fest_modes

The modes of each engine: Firstbet's ten (a literal here, in their order of
strength), FirstBack's one, Festival's eight and Fest's eight -- the last two
asked of the engines themselves, so this module can never disagree with them.

=cut

sub firstbet_modes ()  { return @FIRSTBET }
sub firstback_modes () { return ('FIRSTBACK') }
sub festival_modes ()  { return Games::Sokoban::Solver::Festival::modes() }
sub fest_modes ()      { return Games::Sokoban::Solver::Fest::modes() }

=head2 all_modes

All 27, engine by engine: Firstbet, FirstBack, Festival, Fest.

=cut

sub all_modes () { return (firstbet_modes(), firstback_modes(), festival_modes(), fest_modes()) }

=head2 race_order

The 27 modes in the order the race starts them (see the source for where the
order comes from).

=cut

sub race_order () { return @RACE }

=head2 solver_modes

The optimal solver's three regimes, C<DIAL ASTAR FIFO>, in the order to try
them.

=cut

sub solver_modes () { return @SOLVER }

=head2 own_limit

    my $secs = own_limit($mode);    # 30 for ORDER, undef for the others

A mode's own limit in seconds, whatever the race's, or undef.

=cut

sub own_limit ($mode) { return $OWN_LIMIT{$mode} }

=head2 kind_of, default_caps

    my $kind = kind_of($mode);           # 'pull', 'forward' or 'light'
    my %cap  = default_caps();           # (pull => 1, forward => 3)

The kind of a mode for the caps on what runs at once, and the default caps
(a kind not in them is not counted).

=cut

sub kind_of ($mode)  { return $KIND{$mode} // 'light' }
sub default_caps ()  { return %CAP }

=head2 engine_for, blob_for

    my $pkg  = engine_for($mode);    # the package whose solve() runs it
    my $what = blob_for($mode);      # 'game', 'fest' or 'analysis'

Routing by NAME, never by a table: C<FF_*> is Festival (its blob the frozen
Festival::Analysis), C<E_*> Fest (the packed Fest::Analysis record),
C<FIRSTBACK> FirstBack and everything else Firstbet (both take the Parser's
analysis) -- or Firstbet's BerkeleyDB twin when C<$BERK> is on.

=cut

sub engine_for ($mode) {
    return 'Games::Sokoban::Solver::Festival'  if $mode =~ m{\A FF_ }x;
    return 'Games::Sokoban::Solver::Fest'      if $mode =~ m{\A E_ }x;
    return 'Games::Sokoban::Solver::FirstBack' if $mode eq 'FIRSTBACK';
    return $BERK ? 'Games::Sokoban::Solver::Firstbet::Berk' : 'Games::Sokoban::Solver::Firstbet';
}

sub blob_for ($mode) {
    return 'fest'     if $mode =~ m{\A FF_ }x;
    return 'analysis' if $mode =~ m{\A E_ }x;
    return 'game';
}

=head2 solve

    my ($reason, $path, $secs, $nseen) = solve($label, $blob, $limit, $mode);

The engine face: the mode picks the engine, C<$RACE_FLAG> and C<$RACE_GID> are
copied down to it, C<$LastFail> is carried back up. C<$CTL>, set by Race per
task, may carry C<blok_replaces> (0 or 1: Festival's C<$BLOK_REPLACES> for this
level -- whether the Parser's blok table stands in for the engine's own
deadlock battery, which is right only when the table is complete) and C<blok>
(Fest's C<$BLOK>). Dies when the mode's engine is not loaded.

=cut

sub solve ($label, $blob, $limit = 60, $mode = undef) {
    Carp::confess('Portfolio::solve needs a mode -- it is what picks the engine') unless defined $mode && length $mode;
    my $pkg = engine_for($mode);
    Carp::confess("Portfolio::solve: mode $mode belongs to $pkg, which is not loaded -- load it before the pool starts")
        unless $pkg->can('solve');
    no strict 'refs';
    ${"${pkg}::RACE_FLAG"} = $RACE_FLAG;
    ${"${pkg}::RACE_GID"}  = $RACE_GID;
    if (ref $CTL eq 'HASH') {
        $Games::Sokoban::Solver::Festival::BLOK_REPLACES = $CTL->{'blok_replaces'} if defined $CTL->{'blok_replaces'} and $pkg =~ /Festival\z/;
        $Games::Sokoban::Solver::Fest::BLOK              = $CTL->{'blok'}          if defined $CTL->{'blok'} and $pkg =~ /Fest\z/;
    }
    my @r = &{"${pkg}::solve"}($label, $blob, $limit, $mode);
    $LastFail = ${"${pkg}::LastFail"} // q{};
    return @r;
}

=head2 consistent

    my @problems = consistent();

The lists held against each other: every mode of every engine exactly once in
the race order and nothing else there, every mode with a limit of its own or a
kind a real mode, every mode routed to a loaded package with a C<solve>. Returns
the problems as sentences, none when all is well.

=cut

sub consistent () {
    my @problems;
    my %all;
    ++$all{$_} for all_modes();
    my %race;
    ++$race{$_} for @RACE;
    push @problems, "mode $_ is in no engine's list but in the race order" for grep { !$all{$_} } sort keys %race;
    push @problems, "mode $_ is in the race order " . $race{$_} . ' times' for grep { $race{$_} > 1 } sort keys %race;
    push @problems, "mode $_ of an engine is not in the race order" for grep { !$race{$_} } sort keys %all;
    push @problems, "mode $_ is listed twice by the engines" for grep { $all{$_} > 1 } sort keys %all;
    push @problems, "$_ has a limit of its own but is no mode" for grep { !$all{$_} } sort keys %OWN_LIMIT;
    push @problems, "$_ has a kind but is no mode" for grep { !$all{$_} } sort keys %KIND;
    push @problems, "kind $_ has no cap" for grep { !$CAP{$_} } sort { $a cmp $b } keys %{ { map { $_ => 1 } values %KIND } };
    for my $mode (sort keys %all) {
        my $pkg = engine_for($mode);
        push @problems, "mode $mode routes to $pkg, which has no solve" unless $pkg->can('solve');
    }
    return @problems;
}

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
