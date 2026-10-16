package Games::Sokoban::Solver::FirstBack;

# FirstBack -- a pull search from the solved level towards the start, with
# short push attempts from the start towards whatever position the pulling
# offers. Born as an experiment of the Sokoban project (2026-10-02); this is
# the ONE variant its campaigns left standing (Games::Sokoban::FirstBack 0.07
# there), everything else is in that project's git.
#
#   solve($gameid, $gm, $limit) -> ($reason, $path, $seconds, $positions)
#
# $gm is the Parser's analysis in its blob() form, $gameid any integer the
# caller names the level by, $limit seconds (0 = no limit). Reasons:
# SOLVED, TIMEOUT, UNSOLVABLE (the pull search ran dry), IGNORE (a race was
# lost), MEMCAP. The module stores nothing; the result is the caller's.
#
# THE PULLING. Pull the boxes off the goals, as Firstbet's BACKWARD does --
# every pulled position is winnable by construction, so this search needs no
# deadlock test at all. A pulled position is scored by its boxes' way back to
# the cells the boxes START on: every box off a start cell against every free
# start cell, the pulls between the two added up; the smallest score is
# expanded first. (The same score is BACKWARD's own since Firstbet 3.6.) If the
# pulling reaches the start, that is the solution: it is a whole search by
# itself, and the pushing is help, not a condition.
#
# THE PUSHING. Each time a pulled position is nearer the start than any before
# it, and has stayed the nearest while $AGE more positions were pulled, a
# forward search is given $CAP expansions to push from the start towards THAT
# arrangement, scored like the PUSH_ASSIGN mode with the arrangement in place
# of the goals. The two searches MEET on any position the pulling has seen
# (same boxes, the player in the same region): the solution is the pushes to
# that position and then the pulls from it back to the solved level, replayed
# as pushes.
#
# WHEN THE PULLING STAGNATES. A best position that nothing replaces would be
# tried once and never again -- game 19564 showed it: solved in 0.1 s when the
# first attempt met, and a TIMEOUT with one attempt in three million pulled
# positions when it did not. So once the best position has been tried and
# $STALE more positions have been pulled without a better one turning up, it
# is tried AGAIN with twice the expansions, and after twice that many pulled
# positions again with four times, and so on: the wait and the attempt both
# double. The repeat is not the same search over: it is longer, and it can
# meet on everything pulled in the meantime. A new best position puts the
# doubling back to its start.
#
# Every attempt starts again from the start, but it keeps what the earlier
# ones learnt about the game: %Tahy (the surviving children of every position
# expanded) and %MemBad (the dead positions) are facts about positions, not
# about targets, so a position met again is only re-scored.
#
# WHAT THE CAMPAIGNS SAID (fb-1 to fb-11, bs-1; 2026-10-03 and 04).
#   * Every game solved for the first time by anything -- 34509, 1101, 14757,
#     42738 -- fell to the PULLING with this score; none needed the pushing.
#   * The pushing is kept for games like 19564: with these attempts 7 solved
#     of 7 runs, by pulling alone 0 of 3. On 80 paired games at 300 s the
#     attempts solved everything the pulling solved, plus that game, and lost
#     none, for about a tenth of the positions.
#   * MORE pushing is worse. Cap 1000 doubled the time on 34509, cap 4000 lost
#     it. One continuing push search with a share of the clock (0.03) took
#     half the pulling and met nothing in 185 runs on 37 games -- whether
#     scored by the matching, by a plain sum over all pairs (0.04), run as
#     Firstbet's ROUTE towards the goals or as direct carrying of the boxes in
#     the manner of ORDER (0.05). A forward expansion costs about eleven pulls
#     (class key, corral, frozen test); the score is 4 % of it.
#   * The other pull scores (the same pairs squared, a matching, steps on foot
#     to the nearest start cell) solved nothing this one did not.
# All of that code is in git, at "FirstBack 0.05" and before.
#
# CARVED OUT OF Firstbet.pm 3.5 -- its state is lexical, so nothing of it can
# be reached from outside and what is needed is copied: the blob loading, the
# class keys, the reachability floods, the whole deadlock battery (blok, wall,
# corridor, hole, frozen clusters, the matching filters, the diagonal rule),
# the corral restriction, the move generator, BACKWARD's pull tables and its
# tail replay. NOT taken: the other modes, the scorers, the goal-delivery
# macros and the fill chains -- those aim at the goals and would lead a search
# away from the arrangement it is pushing towards. The battery stays whole: it
# is about reaching the GOALS, and the line of play built here still ends on
# them.
#
# HOW THE FILE IS BUILT (USER 2026-10-04). Two procedures carry everything:
# solve() -- the game out of the blob, the pulling, the ending, the teardown --
# and push_attempt() -- one attempt, with the move generator and the whole
# deadlock battery written out in it. A procedure exists here only if it has
# more than one line AND is called from more than one place; whatever was
# called from one place is written out where it was called. So the battery can
# no longer be compared with Firstbet's sub by sub: a fix made there has to be
# carried over by hand.

our $VERSION = '0.01';

use v5.42;
use warnings FATAL => 'uninitialized';
no warnings 'recursion';
use Carp           ('confess');
use Time::HiRes    ('tv_interval', 'gettimeofday');
use Storable       ('thaw', 'dclone');
use Compress::Zlib;
use Term::ANSIColor;
use Games::Sokoban::Solver::Console ('backline', 'backlinen', 'podil');
use Games::Sokoban::Solver::Data    ();
use Games::Sokoban::Solver::Heap    ();
use Games::Sokoban::Solver::Memory  ();
use Games::Sokoban::Solver::Munkres ();
use Games::Sokoban::Solver::Path    ();

# ---- the outside contract, as in Firstbet.pm
our $QUIET = 0;                 # 0 everything, 1 no transient progress, 2 nothing
our ($RACE_FLAG, $RACE_GID);    # a Race worker's cooperative cancellation
our $MAX_GB = 0;                # GiB of the WHOLE machine's RAM in use; 0 = off

# ---- the three numbers of the pushing; tuned by editing them here
my $CAP   = 250;       # forward expansions per attempt; 0 = no attempts, pull only
my $AGE   = 50;        # pull expansions the best position has to stay the best before it is tried
my $STALE = 50_000;    # pull expansions without a better position before the tried one is tried again; 0 = never

my $BIG    = 1_000_000;    # "cannot" in a matching's matrix
my $SCREEN = 6;            # seconds between two progress lines
my $ENDING = '%-12s %5d %3d %4d %-10s %6d %6d %12.4f %8s %8s %8s %8s %9s';

# ---- the corridor and hole pattern tables, read once per process
my $corridors = Games::Sokoban::Solver::Data::load('corridor_pattern.stor');
my $holes     = Games::Sokoban::Solver::Data::load('hole_pattern.stor');

# Only what more than one procedure touches is declared at file scope; solve()
# loads all of it and hands it back at its end. What one procedure alone uses
# is a `my` inside it.

# ---- the game
my (@Cg, %Cm, %Cmk, @Goal, @IsWall, @Maze, %Pis, @Target, $W);

# the length of the pack template's player part, the template, the solved
# layout, the start position
my ($ManOff, $pu, $SolvedLay, $Start);

# ---- the deadlock data of the game
my ($BlokVec, $Corridor, $Hole, $Wall);
my ($Match_active, %ReachG, %ReachW, %Rev, %Selective);

# ---- the forward search: what is dead, who is whose father, whose children
# survived
my (%MemBad, %Parent, %Tahy);
my (@Blk, @Buf, $PaintId, @Vis);               # paint(): the player's region of the position being expanded
my (@Buf_fr, $PaintId_fr, @Vis_fr);            # paint_fr(): the frozen test's own
my (@Buf_c, %CanonMap, $PaintId_c, @Vis_c);    # class keys

# the offered arrangement: pushes to each of its cells, a flag per cell, its
# cells
my (@DistTo, @IsTgt, @Tgt);

# ---- the pull search: the pulled positions by box layout, and by key
my (%Blay, %Bseen);

##############################################################################
# ===== Paths =================================
##############################################################################

# The player's shortest walk from $m to $target among the boxes @$baggage, as
# step letters.
sub cesta($m, $target, $baggage) {
    my ($bh, $bt, $x, $p, @buf, %path);
    %path     = ($m, '');
    $path{$_} = undef foreach @$baggage;
    $buf[0]   = $m;
    ($bh, $bt) = (0, 1);
    while ($bh != $bt) {
        $x = $buf[$bh++];
        $p = $path{$x};
        foreach my $t (@{ $Cg[$x] }) {
            if (not exists $path{$t}) {
                $path{$t} = $p . $Pis{ $t - $x };
                return $path{$t} if $t == $target;
                $buf[$bt++] = $t;
            }
        }
    }
    die 'NO PATH';
} ## end sub cesta

# The player's steps along the %Parent chain to $best, AND the cell he is left
# on. His true cell is derived, never read from a class key: after a push he
# stands where the box was.
sub get_path($best) {

    # the chain itself, from the start down to $best
    my $p      = $best;
    my @postup = $p;
    my %vidi   = ($p, 1);
    while (($p = $Parent{$p})) {
        confess 'INFINITE CYCLE!' if $vidi{$p}++;
        unshift @postup, $p;
    }
    confess 'NOT A START' unless $Start eq $postup[0];

    # father and son differ by one box: where it stood and where it stands
    my (@sb, @fb, $source, $target, %fh, %sh, $path, $man, $cell);
    ($cell, @fb) = unpack($pu, shift @postup);
    $path = '';
    foreach my $son (@postup) {
        (undef, @sb) = unpack($pu, $son);
        %fh = map(($_, 1), @fb);
        %sh = map(($_, 1), @sb);
        ($source) = grep((!$sh{$_}), @fb);
        confess("SOURCE @fb  |  @sb") unless defined $source;
        ($target) = grep((!$fh{$_}), @sb);
        confess("TARGET @fb  |  @sb") unless defined $target;
        $man = $Cm{$source}{$target};
        confess("$source -> $target") unless defined $man;
        $path .= ($cell == $man ? '' : cesta($cell, $man, \@fb)) . uc $Pis{ $target - $source };
        $cell = $source;
        @fb   = @sb;
    }
    return ($path, $cell);
} ## end sub get_path

# The pushes that undo a pull chain, from the node $key back to its seed --
# which is forward order, towards the solved level.
sub build_tail($key) {
    my @tail;
    while (length(my $v = $Bseen{$key})) {
        push @tail, [unpack('nn', $v)];
        $key = substr($v, 4);
    }
    return \@tail;
}

# Replay such a tail as pushes from $pos, the player's walk worked out afresh
# at every seam.
sub stitch_tail($pos, $tail) {
    my ($man, @boxes) = unpack($pu, $pos);
    my $path = '';
    for my $push (@$tail) {
        my ($from, $to) = @$push;
        my $stance = $Cm{$from}{$to};
        confess("tail stance $from -> $to") unless defined $stance;
        $path .= cesta($man, $stance, \@boxes) if $man != $stance;
        $path .= uc $Pis{ $to - $from };
        @boxes = grep($_ != $from, @boxes);
        my $i = 0;
        ++$i while $i < @boxes && $boxes[$i] < $to;
        splice(@boxes, $i, 0, $to);
        $man = $from;
    }
    return $path;
} ## end sub stitch_tail

##############################################################################
# ===== What both procedures stand on =========
##############################################################################

# The class key: the region of $man with @$bag as walls, named by its smallest
# cell.
sub canon_key($man, $bag) {
    ++$PaintId_c;
    $Vis_c[$_]   = $PaintId_c for @$bag;
    $Vis_c[$man] = $PaintId_c;
    $Buf_c[0]    = $man;
    my $bt  = 1;
    my $min = $man;
    for (my $bh = 0; $bh < $bt; ++$bh) {
        my $x = $Buf_c[$bh];
        foreach my $t (@{ $Cg[$x] }) {
            next if $Vis_c[$t] == $PaintId_c;
            $Vis_c[$t]    = $PaintId_c;
            $Buf_c[$bt++] = $t;
            $min          = $t if $t < $min;
        }
    }
    return pack($pu, $min, @$bag);
} ## end sub canon_key

# The player's region with the boxes @baggage: its cells marked in @Vis, the
# boxes in @Blk, both with a new $PaintId.
sub paint($man, @baggage) {
    ++$PaintId;
    $Blk[$_]   = $PaintId for @baggage;
    $Vis[$man] = $PaintId;
    $Buf[0]    = $man;
    my $bt = 1;
    for (my $bh = 0; $bh < $bt; ++$bh) {
        my $x = $Buf[$bh];
        foreach my $t (@{ $Cg[$x] }) {
            next if $Vis[$t] == $PaintId || $Blk[$t] == $PaintId;
            $Vis[$t] = $PaintId;
            $Buf[$bt++] = $t;
        }
    }
} ## end sub paint

# The same flood in arrays of its own (@Vis_fr, $PaintId_fr), for whoever must
# not disturb paint()'s: the cells of @baggage are walls here and carry the
# mark too.
sub paint_fr($man, @baggage) {
    ++$PaintId_fr;
    $Vis_fr[$_]   = $PaintId_fr for @baggage;
    $Vis_fr[$man] = $PaintId_fr;
    $Buf_fr[0]    = $man;
    my $bt = 1;
    for (my $bh = 0; $bh < $bt; ++$bh) {
        my $x = $Buf_fr[$bh];
        foreach my $t (@{ $Cg[$x] }) {
            next if $Vis_fr[$t] == $PaintId_fr;
            $Vis_fr[$t] = $PaintId_fr;
            $Buf_fr[$bt++] = $t;
        }
    }
} ## end sub paint_fr

# A position is dead: with it its cached children, and its father if that
# leaves him none.
sub set_bad($pozice) {
    return if exists $MemBad{$pozice};
    $MemBad{$pozice} = 1;
    my @bads;
    if (my $cached = delete $Tahy{$pozice}) {
        @bads = @$cached;
    }
    if (my $father = delete $Parent{$pozice}) {
        if (my $list = $Tahy{$father}) {
            my @kept = grep($_ ne $pozice, @$list);
            if (@kept) {$Tahy{$father} = \@kept}
            else {
                delete $Tahy{$father};
                unshift @bads, $father;
            }
        }
    }
    set_bad($_) foreach @bads;
} ## end sub set_bad

# --- the corral restriction --------------------------------------------------
#
# An area the player cannot enter, with boxes on its edge that can only be
# pushed INTO it and work left inside: those pushes have to be made sooner or
# later and nothing done elsewhere changes them, so only the edge boxes may be
# pushed now. Rides on paint(): @Vis is the player's region, @Blk the boxes.
#
# The stamp arrays are never cleared: a cell belongs to the current flood when
# it carries the current number -- $CGen for one position's areas (@CStamp,
# with the area's number in @CComp), $CTag for one candidate corral (@CInC),
# $CTouchGen for one reading of its edge boxes (@CTouch).
my (@CComp, @CFloor, @CInC, @CStamp, @CTouch, @Nb4, @Nb8);
my ($CGen, $CTag, $CTouchGen) = (0, 0, 0);

# The boxes on the corral's boundary, left stamped in @CTouch under a new
# $CTouchGen. Only a boundary box blocks anything below; every other box is
# treated as absent.
sub _corral_boxes($ccells) {
    ++$CTouchGen;
    my @edge;
    for my $p (@$ccells) {
        foreach my $q (@{ $Nb8[$p] }) {
            next if $Blk[$q] != $PaintId or $CTouch[$q] == $CTouchGen;
            $CTouch[$q] = $CTouchGen;
            push @edge, $q;
        }
    }
    return \@edge;
}

# --- the score against the offered arrangement --------------------------------
#
# PUSH_ASSIGN's score with the arrangement in place of the goals: every box
# that is not on a cell of it matched to one free cell of it, the pushes added
# up as cheaply as the matching allows. Lower is better.
sub value_target($t_bag) {
    my @bag = grep {!$IsTgt[$_]} keys %$t_bag;
    return 0 unless @bag;
    my @free = grep {!exists $t_bag->{$_}} @Tgt;
    return $DistTo[$free[0]][$bag[0]] // $BIG if @bag == 1;
    my @matrix;
    for my $t (@free) {
        my $row = $DistTo[$t];
        push @matrix, [map {$row->[$_] // $BIG} @bag];
    }
    return Games::Sokoban::Solver::Munkres::assign(\@matrix);
}

##############################################################################
# ===== The two searches ======================
##############################################################################

my $Ftries = 0;    # push attempts of the whole solve
my $Fpops  = 0;    # forward expansions of the whole solve
my $Fseen  = 0;    # forward positions seen, all attempts together

# ONE ATTEMPT of the forward search: from the start towards the arrangement of
# the pulled position $bkey, at most $cap expansions. $check is asked every
# hundred forward expansions and says why to stop, or ''. Returns (path, '')
# on a solution, (undef, reason) when told to stop, (undef, '') otherwise.
sub push_attempt($bkey, $cap, $check) {

    # the arrangement to push towards: its cells, and for each of them how
    # many pushes take a box there from every cell -- one walk backwards over
    # the push graph, the player not asked about, kept for the whole solve
    $IsTgt[$_] = 0 foreach @Tgt;
    (undef, @Tgt) = unpack($pu, $bkey);
    foreach my $t (@Tgt) {
        $IsTgt[$t] = 1;
        next if defined $DistTo[$t];
        my @d;
        $d[$t] = 0;
        my @q  = ($t);
        my $bh = 0;
        while ($bh < @q) {
            my $x = $q[$bh++];
            for my $c (@{ $Rev{$x} // [] }) {
                next if defined $d[$c];
                $d[$c] = $d[$x] + 1;
                push @q, $c;
            }
        }
        $DistTo[$t] = \@d;
    } ## end foreach my $t (@Tgt)

    # a fresh search from the start: only %Tahy and %MemBad are carried over
    # from the attempts before
    %Parent = ($Start => '');
    my $Pex = 'Games::Sokoban::Solver::Heap'->new;    # what waits, the lowest score first
    $Pex->add($Start, 0);
    ++$Ftries;
    my ($nopen, $pops, $path, $stop) = (1, 0, undef, '');
LMAIN: while ($nopen) {
        last if $pops >= $cap;
        my $pozice = $Pex->next;
        --$nopen;
        next if exists $MemBad{$pozice};
        confess "\nNO PARENT FOR POSITION!" unless exists $Parent{$pozice};
        ++$pops;

        # THE MOVE GENERATOR: the pushes of $pozice that survive the deadlock
        # battery, left in @tahy as a flat list (child class key, score, ...).
        # A position that turns out dead leaves the list empty. A position
        # expanded before -- in an earlier attempt -- already knows its
        # surviving children (%Tahy): candidate enumeration, the battery, the
        # matching and the frozen check depend on the position alone, so only
        # the dead filter and the score are redone.
        my @tahy;
    MOVES: {
            my ($man,    @baggage) = unpack($pu, $pozice);
            my (@nomove, @children);
            my $skipped = 0;
            my %bags    = map(($_, 1), @baggage);
            paint($man, @baggage);

            # expanded before: its surviving children are known
            if (defined(my $cached = $Tahy{$pozice})) {
                foreach my $ch (@$cached) {
                    next if exists $MemBad{$ch};
                    my (undef, @nb) = unpack($pu, $ch);
                    my %nbag = map(($_, 1), @nb);
                    push @tahy, $ch, value_target(\%nbag);
                    push @children, $ch;
                }
                if    (!@children)            {delete $Tahy{$pozice}; set_bad($pozice)}
                elsif (@children != @$cached) {$Tahy{$pozice} = [@children]}
                last MOVES;
            }

            # the boxes as a bit string: the blok patterns are tested against it
            my $vb = '';
            vec($vb, $_, 1) = 1 foreach @baggage;

            # THE CORRAL RESTRICTION: the boxes the search may still touch, left in
            # $callow -- undef when no corral holds. It rides on the paint() above.
            my $callow;
        CORRAL: {
                ++$CGen;

                # the areas the player cannot enter, numbered from 1, each with its
                # cells
                my $nc    = 0;
                my @areas = (undef);
                for my $p (@CFloor) {
                    next if $Vis[$p] == $PaintId or $Blk[$p] == $PaintId or $CStamp[$p] == $CGen;
                    my $c = ++$nc;
                    my @s = ($p);
                    $CStamp[$p] = $CGen;
                    $CComp[$p]  = $c;
                    for (my $i = 0; $i < @s; ++$i) {
                        foreach my $t (@{ $Cg[$s[$i]] }) {
                            next if $CStamp[$t] == $CGen or $Vis[$t] == $PaintId or $Blk[$t] == $PaintId;
                            $CStamp[$t] = $CGen;
                            $CComp[$t]  = $c;
                            push @s, $t;
                        }
                    }
                    $areas[$c] = \@s;
                } ## end for my $p (@CFloor)
                last CORRAL unless $nc;

                # those a box can be pushed into right now
                my @cand = (0) x ($nc + 1);
                foreach my $bx (@baggage) {
                    foreach my $t (@{ $Cmk{$bx} }) {
                        next if $Blk[$t] == $PaintId;
                        my $st = $Cm{$bx}{$t};
                        next unless defined $st          and $Vis[$st] == $PaintId;
                        next unless $CStamp[$t] == $CGen and $CComp[$t];
                        $cand[$CComp[$t]] = 1;
                    }
                }

                # each candidate corral in turn, grown by the corrals its edge boxes
                # would have to be pushed out of: the first that holds decides
            CAND: for my $c0 (1 .. $nc) {
                    next unless $cand[$c0];
                    ++$CTag;
                    my @used = (0) x ($nc + 1);
                    $used[$c0] = 1;
                    my @ccells = @{ $areas[$c0] };
                    $CInC[$_] = $CTag foreach @ccells;
                    my $cboxes = _corral_boxes(\@ccells);
                    my $active = 0;
                    for my $p (@ccells) {$active = 1, last if $Target[$p]}

                    if (!$active) {
                        for my $box (@$cboxes) {$active = 1, last unless $Target[$box]}
                    }
                    next CAND unless $active;
                EXPAND: while (1) {
                        my $add;
                    BOX: for my $box (@$cboxes) {
                            my ($in, $out) = (0, 0);
                            foreach my $q (@{ $Nb4[$box] }) {
                                if    ($CInC[$q] == $CTag)        {$in  = 1}
                                elsif ($CTouch[$q] != $CTouchGen) {$out = 1}
                            }
                            next unless $in and $out;
                            foreach my $t (@{ $Cmk{$box} }) {
                                next if $CTouch[$t] == $CTouchGen;
                                my $st = $Cm{$box}{$t};
                                next unless defined $st;
                                next if $CTouch[$st] == $CTouchGen;
                                if ($CInC[$t] == $CTag and $CInC[$st] != $CTag) {
                                    my $c = $CStamp[$st] == $CGen ? $CComp[$st] : 0;
                                    if ($c and !$used[$c]) {$add = $c; last BOX}
                                }
                                elsif ($CInC[$t] != $CTag and $CInC[$st] != $CTag) {
                                    my $c = $CStamp[$t] == $CGen ? $CComp[$t] : 0;
                                    if ($c and !$used[$c]) {$add = $c; last BOX}
                                }
                            }
                        } ## end BOX: for my $box (@$cboxes)
                        last EXPAND unless defined $add;
                        $used[$add] = 1;
                        push @ccells, @{ $areas[$add] };
                        $CInC[$_] = $CTag foreach @{ $areas[$add] };
                        $cboxes = _corral_boxes(\@ccells);
                    } ## end EXPAND: while (1)

                    # sealed? a push with both stance and landing outside breaks the argument
                    for my $box (@$cboxes) {
                        foreach my $t (@{ $Cmk{$box} }) {
                            next if $CTouch[$t] == $CTouchGen or $CInC[$t] == $CTag;
                            my $st = $Cm{$box}{$t};
                            next unless defined $st;
                            next if $CTouch[$st] == $CTouchGen or $CInC[$st] == $CTag;
                            next CAND;
                        }
                    }

                    # and every push INTO it must be his to make right now
                    for my $box (@$cboxes) {
                        foreach my $t (@{ $Cmk{$box} }) {
                            next if $CTouch[$t] == $CTouchGen or $CInC[$t] != $CTag;
                            my $st = $Cm{$box}{$t};
                            next unless defined $st;
                            next if $CTouch[$st] == $CTouchGen or $CInC[$st] == $CTag;
                            next CAND unless $Vis[$st] == $PaintId;
                        }
                    }
                    my %allowed;
                    for my $box (@$cboxes) {
                        foreach my $t (@{ $Cmk{$box} }) {
                            next if $CTouch[$t] == $CTouchGen or $CInC[$t] != $CTag;
                            my $st = $Cm{$box}{$t};
                            next unless defined $st;
                            next               if $CTouch[$st] == $CTouchGen or $CInC[$st] == $CTag;
                            $allowed{$box} = 1 if $Vis[$st] == $PaintId;
                        }
                    }
                    if (%allowed) {$callow = \%allowed; last CORRAL}
                } ## end CAND: for my $c0 (1 .. $nc)
            } ## end CORRAL:

            # THE CANDIDATE PUSHES: every box to every cell it can be pushed
            # to from where the player can stand. A box the corral forbids is
            # counted as movable, and not pushed.
            foreach my $bx (@baggage) {
                my $movable = 0;
                my $cskip   = $callow && !$callow->{$bx};
                delete $bags{$bx};
                vec($vb, $bx, 1) = 0;
                foreach my $t (@{ $Cmk{$bx} }) {
                    next if exists $bags{$t};
                    my $s = $Cm{$bx}{$t};
                    next unless $Vis[$s] == $PaintId;
                    ++$movable;
                    next if $cskip;
                    my @nb = grep($_ != $bx, @baggage);
                    my $i  = 0;
                    ++$i while $i < @nb && $nb[$i] < $t;
                    splice(@nb, $i, 0, $t);
                    my $child = $CanonMap{ pack($pu, $bx, @nb) } //= canon_key($bx, \@nb);
                    next if exists $MemBad{$child};

                    # a class already alive in this attempt: it stays in the cached
                    # list, and is not worked out again
                    if (exists $Parent{$child}) {
                        ++$skipped;
                        push @children, $child;
                        next;
                    }
                    $bags{$t} = 1;
                    vec($vb, $t, 1) = 1;

                    # THE DEADLOCK BATTERY on the child, the box now on $t
                    my $dead = 0;
                BAD: {
                        # blok: boxes standing together that can never be taken apart
                        if (my $bvs = $BlokVec->{$bx} && $BlokVec->{$bx}{$t}) {
                            foreach my $pv (@$bvs) {
                                if (($vb &. $pv) eq $pv) {$dead = 1; last BAD}
                            }
                        }

                        # wall: more boxes along a stretch than it can let go
                        if ($Wall) {
                            if (defined(my $rules = $Wall->{$t})) {
                                foreach my $rule (@$rules) {
                                    my $n = 0;
                                    foreach my $cell (@{ $rule->[1] }) {
                                        ++$n if exists $bags{$cell};
                                    }
                                    if ($n > $rule->[0]) {$dead = 1; last BAD}
                                }
                            }
                        }

                        # corridor: two boxes in a plain one, or a filling its pattern
                        # table does not know
                        if ($Corridor) {
                            if (defined(my $cor = $Corridor->{$bx} && $Corridor->{$bx}{$t})) {
                                if ($cor->[2] =~ /^0+$/a) {
                                    my $n = 0;
                                    foreach my $cell (@{ $cor->[0] }) {
                                        ++$n if exists $bags{$cell};
                                    }
                                    if ($n > 1) {$dead = 1; last BAD}
                                }
                                else {
                                    $Maze[$_] =~ tr/03/47/ foreach keys %bags;
                                    my $str = join('', @Maze[@{ $cor->[0] }]);
                                    $Maze[$_] =~ tr/47/03/ foreach keys %bags;
                                    confess("UNKNOWN Coridor pattern $$cor[2]") unless exists $corridors->{ $cor->[2] };
                                    unless (($corridors->{ $cor->[2] }{ $cor->[1] } // {})->{$str}) {$dead = 1; last BAD}
                                }
                            } ## end if (defined(my $cor = ...))
                        } ## end if ($Corridor)

                        # hole: a filling its pattern table does not know
                        if ($Hole) {
                            if (defined(my $hole = $Hole->{$bx} && $Hole->{$bx}{$t})) {
                                $Maze[$_] =~ tr/03/47/ foreach keys %bags;
                                my $str = join('', @Maze[@{ $hole->[0] }]);
                                $Maze[$_] =~ tr/47/03/ foreach keys %bags;
                                confess("UNKONWN Hole pattern $$hole[1]") unless exists $holes->{ $hole->[1] };
                                unless ($holes->{ $hole->[1] }{$str}) {$dead = 1; last BAD}
                            }
                        }

                        # the matching: can every box still be given a goal of its
                        # own? Asked only when the box landed on a cell that reaches
                        # fewer goals than there are.
                        if ($Match_active && $Selective{$t}) {
                            my %union;
                            for my $box (@nb) {
                                my $rg = $ReachG{$box} or last BAD;    # missing data: never prune
                                $union{$_} = 1 for keys %$rg;
                            }
                            if (keys %union < @nb) {$dead = 1; last BAD}
                            my @matrix;
                            for my $box (@nb) {
                                my $rg = $ReachG{$box};
                                push @matrix, [map {$rg->{$_} ? 0 : $BIG} @Goal];
                            }
                            $dead = 1 if Games::Sokoban::Solver::Munkres::assign(\@matrix) >= $BIG;
                        }
                    } ## end BAD:
                    if ($dead) {set_bad($child)}
                    else {
                        push @tahy, $child, value_target(\%bags);
                        push @children, $child;
                    }

                    # the box off $t again, whatever the verdict was
                    delete $bags{$t};
                    vec($vb, $t, 1) = 0;
                } ## end foreach my $t (@{ $Cmk{$bx}...})
                $bags{$bx} = 1;
                vec($vb, $bx, 1) = 1;
                push @nomove, $bx unless $movable;
            } ## end foreach my $bx (@baggage)

            # the surviving children, kept for the attempts to come
            $Tahy{$pozice} = [@children] if @children;

            # THE FROZEN CLUSTER among the boxes that had no legal push: those that
            # stay unpushable even with the others of the cluster counted as walls.
            # One of them off its goal, or a goal shut off behind them, and the
            # position is dead.
            my @frozen_set;
            if (@nomove) {
                my %frozen = map(($_, 1), @nomove);
                while (1) {
                    my @still_frozen = ();
                    paint_fr($man, keys %frozen);
                    foreach my $bx (keys %frozen) {
                        my $movable = 0;
                        foreach my $t (@{ $Cmk{$bx} }) {
                            next if exists $frozen{$t};
                            my $stance = $Cm{$bx}{$t};
                            next if exists $frozen{$stance};
                            next unless $Vis_fr[$stance] == $PaintId_fr;
                            $movable = 1;
                            last;
                        }
                        push @still_frozen, $bx unless $movable;
                    }
                    last if scalar @still_frozen == scalar %frozen;
                    %frozen = map(($_, 1), @still_frozen);
                } ## end while (1)
                for my $box (keys %frozen) {
                    unless ($Target[$box]) {
                        set_bad($pozice);
                        @tahy = ();
                        last MOVES;
                    }
                }
                @frozen_set = keys %frozen;
                if (@frozen_set) {
                    for my $g (grep {!exists $bags{$_}} @Goal) {
                        if ($Vis_fr[$g] != $PaintId_fr) {
                            set_bad($pozice);
                            @tahy = ();
                            last MOVES;
                        }
                    }
                }
            } ## end if (@nomove)

            # the diagonal rule and the matching on the board it leaves
            if (@Goal) {
                my %wall = map(($_, 1), @frozen_set);

                # THE DIAGONAL RULE (Festival's fix_diagonals): a diagonal chain of
                # sealed empty pockets, anchored at both ends and carrying no goal,
                # turns the boxes on its flanks into walls -- repeated until no box
                # is added.
                while (1) {
                    my %w     = %wall;
                    my $rows  = int(@Maze / $W);
                    my $ncell = scalar @Maze;

                    # the cells beside the boxes ...
                    my %cand;
                    for my $box (keys %bags) {
                        $cand{ $box - $W } = 1;
                        $cand{ $box + $W } = 1;
                        $cand{ $box - 1 }  = 1;
                        $cand{ $box + 1 }  = 1;
                    }

                    # ... of them the pockets: empty, off the player's region,
                    # shut in on all four sides by wall or box
                    my (@inner, @pocket);
                    for my $p (keys %cand) {
                        next if $p < 0 || $p >= $ncell;
                        my $i = int($p / $W);
                        my $j = $p % $W;
                        next if $i < 1 || $i > $rows - 2 || $j < 1 || $j > $W - 2;
                        next if $IsWall[$p] || $w{$p} || $bags{$p};
                        next if $Vis[$p] == $PaintId;    # the player's own region
                        my $n = $p - $W;
                        next unless $IsWall[$n] || $w{$n} || $bags{$n};
                        $n = $p + $W;
                        next unless $IsWall[$n] || $w{$n} || $bags{$n};
                        $n = $p + 1;
                        next unless $IsWall[$n] || $w{$n} || $bags{$n};
                        $n = $p - 1;
                        next unless $IsWall[$n] || $w{$n} || $bags{$n};
                        $inner[$p] = 1;
                        push @pocket, $p;
                    } ## end for my $p (keys %cand)

                    # the diagonal chains of pockets, down to the right and
                    # down to the left, each anchored at both of its ends
                    my (@dr, @dl, @chain);
                    for my $p (@pocket) {
                        my $i = int($p / $W);
                        my $j = $p % $W;
                        for my $dir (1, -1) {
                            my $up = $dir == 1 ? $p - $W - 1 : $p - $W + 1;
                            my $sd = $dir == 1 ? $p - 1      : $p + 1;
                            next
                                unless ($IsWall[$up] || $w{$up} || $bags{$up})
                                || (($IsWall[$p - $W] || $w{ $p - $W }) && ($IsWall[$sd] || $w{$sd}));
                            my $k = 1;
                            ++$k while $inner[($i + $k) * $W + $j + $dir * $k];
                            my $ep = ($i + $k) * $W + $j + $dir * $k;
                            my $ed = $dir == 1 ? $ep - 1 : $ep + 1;
                            next
                                unless ($IsWall[$ep] || $w{$ep} || $bags{$ep})
                                || (($IsWall[$ep - $W] || $w{ $ep - $W }) && ($IsWall[$ed] || $w{$ed}));
                            if   ($dir == 1) {$dr[$p] = $k}
                            else             {$dl[$p] = $k}
                        } ## end for my $dir (1, -1)
                        push @chain, $p if $dr[$p] || $dl[$p];
                    } ## end for my $p (@pocket)

                    # walls go down as the scan proceeds, in row-major order
                    for my $p (sort {$a <=> $b} @chain) {
                        my $i = int($p / $W);
                        my $j = $p % $W;
                        for my $set ([$dr[$p], 1], [$dl[$p], -1]) {
                            my ($k, $dir) = @$set;
                            next unless $k;
                            my $goal = 0;
                            for my $n (0 .. $k - 1) {$goal = 1 if $Target[($i + $n) * $W + $j + $dir * $n]}
                            next if $goal;
                            for my $n (0 .. $k - 1) {
                                my $c = ($i + $n) * $W + $j + $dir * $n;
                                $w{ $c - 1 } = 1;
                                $w{ $c + 1 } = 1;
                            }
                            my $t  = ($i - 1) * $W + $j;
                            my $td = $t - $dir;
                            $w{$td} = 1 if $IsWall[$td] || $w{$td} || $bags{$td};
                            $w{$t}  = 1;
                            my $e = ($i + $k) * $W + $j + $dir * $k;
                            $w{$e} = 1 if $IsWall[$e] || $w{$e} || $bags{$e};
                            $w{ $e - $dir } = 1;
                        } ## end for my $set ([$dr[$p], ...])
                    } ## end for my $p (sort {$a <=>...})

                    # only boxes are reported; did the set of walls grow?
                    my $grew = 0;
                    for my $c (grep {$bags{$_}} keys %w) {
                        $grew = 1 unless $wall{$c}++;
                    }
                    last unless $grew;
                } ## end while (1)
                if (%wall) {

                    # a box turned into a wall off its goal stays off it
                    for my $box (keys %wall) {
                        unless ($Target[$box]) {
                            set_bad($pozice);
                            @tahy = ();
                            last MOVES;
                        }
                    }

                    # THE MATCHING ON THE WALLED BOARD: with those boxes as walls,
                    # can every other box still be given a goal of its own?
                    my $walled_dead = 0;
                WALLED: {
                        my $key = join(',', sort {$a <=> $b} keys %wall);

                        # which cells can still reach each goal once %wall are
                        # walls; kept per wall set
                        my $wr = $ReachW{$key} //= do {
                            my %by_goal;
                            for my $g (@Goal) {
                                next if $wall{$g};
                                my %seen = ($g => 1);
                                my @q    = ($g);
                                while (@q) {
                                    my $t = shift @q;
                                    for my $c (@{ $Rev{$t} // [] }) {
                                        next if $seen{$c} || $wall{$c};
                                        my $s = $Cm{$c}{$t};
                                        next if !defined $s || $wall{$s};
                                        $seen{$c} = 1;
                                        push @q, $c;
                                    }
                                }
                                $by_goal{$g} = \%seen;
                            } ## end for my $g (@Goal)
                            \%by_goal;
                        };
                        my @free = grep {!$wall{$_}} @baggage;
                        last WALLED unless @free;
                        my @g = grep {!$wall{$_}} @Goal;
                        if (@free > @g) {$walled_dead = 1; last WALLED}
                        my (@matrix, %union);
                        for my $box (@free) {
                            my $rg = $ReachG{$box} or last WALLED;    # missing data: never prune
                            my @row;
                            for my $goal (@g) {
                                my $ok = ($rg->{$goal} && $wr->{$goal} && $wr->{$goal}{$box}) ? 1 : 0;
                                $union{$goal} = 1 if $ok;
                                push @row, $ok ? 0 : $BIG;
                            }
                            push @matrix, \@row;
                        }
                        if (keys %union < @free) {$walled_dead = 1; last WALLED}
                        $walled_dead = 1 if Games::Sokoban::Solver::Munkres::assign(\@matrix) >= $BIG;
                    } ## end WALLED:
                    if ($walled_dead) {
                        set_bad($pozice);
                        @tahy = ();
                        last MOVES;
                    }
                } ## end if (%wall)
            } ## end if (@Goal)

            # nothing new is not the same as dead: every candidate may have been a
            # class already alive
            set_bad($pozice) if !@tahy and !$skipped;
        } ## end MOVES:

        # THE CHILDREN: each new one is linked to its father, asked whether
        # it ends the solve, and queued
        foreach my ($child, $score)(@tahy) {
            next if exists $MemBad{$child} or exists $Parent{$child};
            $Parent{$child} = $pozice;
            my $lay = substr($child, $ManOff);

            # every goal filled: the pushing has solved it by itself. (The rare
            # game with more goals than boxes has no one layout to compare.)
            if (
                defined $SolvedLay
                ? $lay eq $SolvedLay
                : do {
                    my (undef, @lb) = unpack($pu, $child);
                    my %on = map(($_, 1), @lb);
                    !grep {!exists $on{$_}} @Goal;
                }
               )
            {
                ($path) = get_path($child);
                last LMAIN;
            }

            # the pull search has seen these boxes: is one of its players in
            # this player's region?
            if (defined(my $men = $Blay{$lay})) {
                my (undef, @nb) = unpack($pu, $child);
                foreach my $m (unpack('n*', $men)) {
                    my $bk = pack($pu, $m, @nb);
                    next if ($CanonMap{$bk} //= canon_key($m, \@nb)) ne $child;
                    my ($front, $cell) = get_path($child);
                    $path = $front . stitch_tail(pack($pu, $cell, @nb), build_tail($bk));
                    last LMAIN;
                }
            }
            $Pex->add($child, $score);
            ++$nopen;
        } ## end foreach my ($child, $score)...
        last if !(++$Fpops % 100) and $stop = $check->();
    } ## end LMAIN: while ($nopen)
    $Fseen += scalar %Parent;
    return ($path, $stop);
} ## end sub push_attempt

# THE WHOLE SOLVE: the game out of the blob, the pull search with the push
# attempts hung on it, the ending and the teardown. Returns ($reason, $path,
# $seconds, $positions). The fourth argument every engine is called with (the
# mode) has nothing to choose here, so it is taken and not named.
sub solve($gameid, $gm, $limit, $ = undef) {

    # ---- the game, from the blob
    my %Game = %{ thaw(uncompress($gm)) };
    my $maze = $Game{'code'};
    $maze =~ tr/,//d;
    $maze =~ tr/45678/00233/;
    @Maze       = split(//a, $maze, 0);
    @IsWall     = map {$_ eq '9' ? 1 : 0} @Maze;
    @Goal       = @{ $Game{'goal'} };
    @Target     = (0) x scalar @Maze;
    $Target[$_] = 1 foreach @Goal;
    %Cm         = %{ $Game{'cm'} };
    %Cmk        = %{ $Game{'cmk'} };
    @Cg         = ();
    $Cg[$_]     = $Game{'cg'}{$_} foreach keys %{ $Game{'cg'} };
    $W          = $Game{'w'};
    %Pis        = (-1, 'l', 1, 'r', $W, 'd', -$W, 'u');
    my @Baggage = @{ $Game{'baggage'} };    # the cells the boxes start on

    # blok: the blob carries trimmed bit vectors, taken as they are
    {
        my %vec;
        my $src = $Game{'blok'} // {};
        foreach my $bx (keys %$src) {
            my $row = $src->{$bx};
            foreach my $t (keys %$row) {
                my @vs;
                foreach my $p (@{ $row->{$t} }) {
                    die "array blok pattern -- the Parser writes bit vectors" if ref $p;
                    push @vs, $p;
                }
                $vec{$bx}{$t} = \@vs;
            }
        }
        $BlokVec = \%vec;
    }

    # the hole, wall and corridor data, where the game has any
    $Hole     = $Game{'has_hole'}     ? dclone($Game{'hole'})     : undef;
    $Wall     = $Game{'has_wall'}     ? dclone($Game{'walls'})    : undef;
    $Corridor = $Game{'has_corridor'} ? dclone($Game{'corridor'}) : undef;

    # the corral restriction's geometry: the floor cells, their four and their
    # eight neighbours, and the stamp arrays at zero
    {
        @CFloor = ();
        @Nb4    = ();
        @Nb8    = ();
        my $n     = scalar @Maze;
        my @floor = (0) x $n;
        for my $p (0 .. $n - 1) {
            next if $Maze[$p] eq '9' or $Maze[$p] eq '1';
            $floor[$p] = 1;
            push @CFloor, $p;
        }
        for my $p (@CFloor) {
            my $col = $p % $W;
            my (@n4, @n8);
            for my $d (-$W - 1, -$W, -$W + 1, -1, 1, $W - 1, $W, $W + 1) {
                my $q = $p + $d;
                next if $q < 0 or $q >= $n or !$floor[$q];
                next if abs(($q % $W) - $col) > 1;
                push @n8, $q;
                push @n4, $q if $d == -1 or $d == 1 or $d == -$W or $d == $W;
            }
            $Nb4[$p] = \@n4;
            $Nb8[$p] = \@n8;
        }
        @CComp  = (0) x $n;
        @CInC   = (0) x $n;
        @CStamp = (0) x $n;
        @CTouch = (0) x $n;
        ($CGen, $CTag, $CTouchGen) = (0, 0, 0);
    }

    # the forward search's stores empty, the flood arrays at zero
    %Parent     = ();
    %Tahy       = ();
    %MemBad     = ();
    %CanonMap   = ();
    $PaintId    = 0;
    $PaintId_fr = 0;
    $PaintId_c  = 0;
    @Blk        = (0) x scalar @Maze;
    @Vis        = (0) x scalar @Maze;
    @Vis_fr     = (0) x scalar @Maze;
    @Vis_c      = (0) x scalar @Maze;

    # a position is the player's cell and the box cells, packed; the solved
    # layout is one string when there are as many goals as boxes
    $pu        = $Game{'vzp'};
    $Start     = pack($pu, $Game{'player'}, @Baggage);
    $ManOff    = length pack($pu, 0);
    $SolvedLay = (@Goal == @Baggage) ? pack($pu, sort {$a <=> $b} @Goal) : undef;

    # the matching filter's reachable-goal sets, from the blob's push table
    %ReachG    = ();
    %Selective = ();
    {
        my $zr = $Game{'steps'} // {};
        for my $c (keys %$zr) {
            my $row = $zr->{$c};
            for my $g (keys %$row) {
                my $v = $row->{$g};
                $ReachG{$c}{$g} = 1 if defined $v && $v ne 'Inf';
            }
        }
        $ReachG{$_}{$_} = 1 foreach @Goal;    # a box on its goal reaches it

        # a cell that reaches fewer goals than there are is selective; the
        # matching is worth asking only when one of them is no goal itself
        $Match_active = 0;
        for my $c (keys %ReachG) {
            next unless keys %{ $ReachG{$c} } < @Goal;
            $Selective{$c} = 1;
            $Match_active = 1 unless $Target[$c];
        }
    }

    # the reverse push graph: the walled matching and the distances to a
    # target cell both walk it
    %Rev    = ();
    %ReachW = ();
    for my $c (keys %Cmk) {
        push @{ $Rev{$_} }, $c foreach @{ $Cmk{$c} };
    }
    @Tgt    = ();
    @IsTgt  = (0) x scalar @Maze;
    @DistTo = ();

    # ---- the pull search's tables
    %Bseen = ();
    %Blay  = ();
    my $StartBoxKey = pack($pu, sort {$a <=> $b} @Baggage);
    my @IsStart     = (0) x scalar @Maze;
    $IsStart[$_] = 1 foreach @Baggage;

    # the transposition of %Cm: a push from -> c with the player on
    # $Cm{from}{c} is a pull of the box on c back to from, after which the
    # player stands there
    my (%Pull, %PullMan);
    for my $from (keys %Cm) {
        my $tb = $Cm{$from};
        for my $c (keys %$tb) {
            push @{ $Pull{$c} }, $from;
            $PullMan{$c}{$from} = $tb->{$c};
        }
    }

    # $PullTo[$s][$x]: how many pulls bring a box from cell x to the start
    # cell s, that is, how many pushes take one from s to x -- one walk over
    # the push graph per start cell, the player not asked about. $Far stands
    # in for "cannot": the largest number in the table and one more.
    my @PullTo;
    my $Far = 0;
    for my $s (@Baggage) {
        my @d;
        $d[$s] = 0;
        my @q  = ($s);
        my $bh = 0;
        while ($bh < @q) {
            my $x = $q[$bh++];
            for my $t (@{ $Cmk{$x} // [] }) {
                next if defined $d[$t];
                $d[$t] = $d[$x] + 1;
                $Far = $d[$t] if $d[$t] > $Far;
                push @q, $t;
            }
        }
        $PullTo[$s] = \@d;
    } ## end for my $s (@Baggage)
    ++$Far;

    # ---- the pull search, with the push attempts hung on it
    my $timer = [gettimeofday()];
    my ($counter, $bc, $nopen, $MaxOpen) = (0, 0, 0, 0);
    my ($cas, $tick) = (time(), time());
    ($Ftries, $Fpops, $Fseen) = (0, 0, 0);

    # the run controls, on three periods as in Firstbet: the limit promptly,
    # the race flag once a second, memory and the progress line on the screen
    # interval. Returns the reason to stop, or ''.
    my ($best_key, $best_h, $best_since, $tried);
    my ($again_at, $again_mult);    # the stagnation retry: at which pull count, with how many times $CAP
    my $check = sub () {
        my $doba = tv_interval($timer);
        return 'TIMEOUT' if $limit and $doba > $limit;
        my $now = time();
        return '' if $now == $tick;
        $tick = $now;
        return 'IGNORE' if $RACE_FLAG && $RACE_GID && $RACE_FLAG->{$RACE_GID};
        return ''       if $now - $cas < $SCREEN;
        $cas = $now;
        $QUIET
            or backline(
                sprintf '%-11s %8d ... %12d %9d  %s  %6s %12.2f %12.0f %12.0f  try %d push %d',
                'FIRSTBACK', $gameid, $counter, $nopen,
                podil($nopen, $MaxOpen),
                $best_h // '-',
                $doba,
                $bc / $doba,
                $counter / $doba,
                $Ftries, $Fpops
            );
        return $MAX_GB && Games::Sokoban::Solver::Memory::used_gb() > $MAX_GB ? 'MEMCAP' : '';
    }; ## end $check = sub

    my @goals = sort {$a <=> $b} @Goal;
    my %Q;                             # the open list: h -> [keys], FIFO inside a bucket
    my $Hq = 'Games::Sokoban::Solver::Heap'->new;    # the live buckets, the smallest h on top
    my ($found, $path);
    my $reason = 'UNSOLVABLE';

    # THE SEEDS: the solved level, once for every region of its free floor --
    # the player may stand in any of them when the level is solved. %reps
    # holds one cell of each (a hash: its key order is the order of the seeds).
    my %reps;
    {
        my %seen;
        for my $s (grep {defined $Cg[$_]} 0 .. $#Cg) {
            next if $Target[$s] || exists $seen{$s};
            $reps{$s} = 1;
            my @st = ($s);
            $seen{$s} = 1;
            while (@st) {
                my $x = pop @st;
                for my $y (@{ $Cg[$x] }) {
                    next if $Target[$y] || exists $seen{$y};
                    $seen{$y} = 1;
                    push @st, $y;
                }
            }
        }
    }
    for my $m (keys %reps) {
        my $pos = pack($pu, $m, @goals);
        next if exists $Bseen{$pos};
        $Bseen{$pos} = '';
        $Blay{ substr($pos, $ManOff) } .= pack('n', $m);
        if (pack($pu, @goals) eq $StartBoxKey) {
            paint_fr($m, @goals);
            if ($Vis_fr[$Game{'player'}] == $PaintId_fr) {$found = $pos; last}
        }

        # the score of a pulled position: every box off a start cell against
        # every free start cell, the pulls added up (the goals carry the boxes
        # here, so the free start cells are those that are no goal)
        my $h = 0;
        if (my @off = grep {!$IsStart[$_]} @goals) {
            for my $s (grep {!$Target[$_]} @Baggage) {
                my $row = $PullTo[$s];
                $h += $row->[$_] // $Far for @off;
            }
        }
        $best_h = $h if !defined $best_h or $h < $best_h;    # the root is never offered
        push @{ $Q{$h} //= do {$Hq->add($h, $h); []} }, $pos;
        ++$nopen;
    } ## end for my $m (keys %reps)
    $MaxOpen = $nopen;

    # THE PULL LOOP: the position with the smallest score is expanded -- every
    # box pulled to every cell it can be pulled to -- until one of the pulled
    # positions is the start, or a push attempt meets one of them.
PULL: while (!defined $found && $nopen) {
        my $h0     = $Hq->peek;
        my $bucket = $Q{$h0};
        my $pos    = shift @$bucket;
        unless (@$bucket) {delete $Q{$h0}; $Hq->next}
        --$nopen;
        my ($man, @boxes) = unpack($pu, $pos);
        paint($man, @boxes);
        my %bag = map(($_, 1), @boxes);
    GEN: for my $c (@boxes) {
            my $dests = $Pull{$c} or next;
            for my $to (@$dests) {
                ++$bc;
                next if exists $bag{$to};
                next unless $Vis[$to] == $PaintId;
                my $ma = $PullMan{$c}{$to};
                next if exists $bag{$ma};
                my @nb = grep($_ != $c, @boxes);
                my $i  = 0;
                ++$i while $i < @nb && $nb[$i] < $to;
                splice(@nb, $i, 0, $to);
                my $npos = pack($pu, $ma, @nb);
                next if exists $Bseen{$npos};
                $Bseen{$npos} = pack('nn', $to, $c) . $pos;    # the undoing push, then the parent
                $Blay{ substr($npos, $ManOff) } .= pack('n', $ma);

                # the boxes are where they start: is the player's start cell
                # in this player's region?
                if (pack($pu, @nb) eq $StartBoxKey) {
                    paint_fr($ma, @nb);
                    if ($Vis_fr[$Game{'player'}] == $PaintId_fr) {$found = $npos; last GEN}
                }

                # the same score: the child's boxes are the parent's (%bag)
                # with the one on $c now on $to
                my $h = 0;
                if (my @off = grep {!$IsStart[$_]} @nb) {
                    for my $s (@Baggage) {
                        next if $s == $to or $s != $c && exists $bag{$s};
                        my $row = $PullTo[$s];
                        $h += $row->[$_] // $Far for @off;
                    }
                }
                if ($h < $best_h) {
                    ($best_key, $best_h, $best_since, $tried) = ($npos, $h, $counter, 0);
                }
                push @{ $Q{$h} //= do {$Hq->add($h, $h); []} }, $npos;
                ++$nopen;
                $MaxOpen = $nopen if $nopen > $MaxOpen;
            } ## end for my $to (@$dests)
        } ## end GEN: for my $c (@boxes)
        ++$counter;
        last if defined $found;

        # the best pulled position has stayed the best long enough: push
        # towards it. (paint() and the forward search share @Vis, but this
        # position's expansion is over.)
        if ($CAP and defined $best_key and !$tried and $counter - $best_since >= $AGE) {
            $tried = 1;
            ($again_at, $again_mult) = ($counter + $STALE, 2);
            ($path, my $stop) = push_attempt($best_key, $CAP, $check);
            if (defined $path) {$reason = 'SOLVED'; last PULL}
            if ($stop)         {$reason = $stop;    last PULL}
        }

        # nothing better has turned up since it was tried: try it again,
        # twice as long, and wait twice as long for the next time
        elsif ($STALE and $tried and $counter >= $again_at) {
            my $cap = $CAP * $again_mult;
            $again_at = $counter + $STALE * $again_mult;
            $again_mult *= 2;
            ($path, my $stop) = push_attempt($best_key, $cap, $check);
            if (defined $path) {$reason = 'SOLVED'; last PULL}
            if ($stop)         {$reason = $stop;    last PULL}
        }
        if (!($counter % 200) and my $stop = $check->()) {$reason = $stop; last}
    } ## end PULL: while (!defined $found &&...)

    # the pull search got to the start by itself
    if (defined $found) {
        $path   = stitch_tail($Start, build_tail($found));
        $reason = 'SOLVED';
    }
    $path //= '';

    # THE FINISHED PATH IS WRITTEN AGAIN FROM ITS PUSHES (0.07, USER 2026-10-12),
    # by the one procedure every engine of the project passes its path through
    # while the level is still in memory (Games::Sokoban::Path): the pushes up
    # to the one after which every goal is under a box, those that only take
    # the boxes away and bring them back left out where it shortens the path,
    # a shortest walk to each. Both ways a path arises here -- the pulls played
    # backwards, a push attempt that met them -- walk with cesta() and end on
    # the solved level, and all 4 629 solved paths of matrix fm-1 come back
    # letter for letter; the call is here because the rule is every engine's,
    # and because it plays the path before it is returned.
    $path = Games::Sokoban::Solver::Path::rebuilt(
        'path'   => $path,
        'width'  => $W,
        'floor'  => [grep {$Maze[$_] ne '9' and $Maze[$_] ne '1'} 0 .. $#Maze],
        'goals'  => \@Goal,
        'boxes'  => \@Baggage,
        'player' => $Game{'player'},
    ) if $reason eq 'SOLVED';
    my $doba = tv_interval($timer);
    $doba = 0.000001 if $doba < 0.000001;    # it divides below
    my $nseen = scalar(%Bseen) + $Fseen;     # taken before the teardown empties %Bseen
    if ($QUIET <= 1) {
        state $colour = { 'SOLVED', 'bright_green', 'TIMEOUT', 'bright_yellow', 'IGNORE', 'white' };
        backlinen(
            Term::ANSIColor::colored(
                sprintf($ENDING,
                    'FIRSTBACK',   $gameid,
                    $Game{'nbox'}, $Game{'ncell'},
                    $reason, ($reason eq 'SOLVED' ? length($path) : $limit),
                    scalar($path =~ tr/DLRU//),   $doba,
                    sprintf('%.0f', $bc / $doba), sprintf('%.0f', ($counter + $Fpops) / $doba),
                    $MaxOpen,                     $nopen,
                    $nseen),
                $colour->{$reason} // 'bright_red'
            )
        );
    } ## end if ($QUIET <= 1)

    # ---- everything this solve built at file scope, handed back (undef, not
    # = (): an emptied hash keeps its buckets). The return values are in hand.
    undef @Blk;
    undef @Buf;
    undef @Buf_c;
    undef @Buf_fr;
    undef @Cg;
    undef @DistTo;
    undef @Goal;
    undef @IsTgt;
    undef @IsWall;
    undef @Maze;
    undef @Target;
    undef @Tgt;
    undef @Vis;
    undef @Vis_c;
    undef @Vis_fr;
    undef @CComp;
    undef @CFloor;
    undef @CInC;
    undef @CStamp;
    undef @CTouch;
    undef @Nb4;
    undef @Nb8;
    undef %Blay;
    undef %Bseen;
    undef %CanonMap;
    undef %Cm;
    undef %Cmk;
    undef %MemBad;
    undef %Parent;
    undef %Pis;
    undef %ReachG;
    undef %ReachW;
    undef %Rev;
    undef %Selective;
    undef %Tahy;
    $BlokVec = $Corridor = $Hole = $Wall = undef;
    return ($reason, $path, $doba, $nseen);
} ## end sub solve
1;
