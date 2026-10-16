package Games::Sokoban::Solver::Fest;
our $VERSION = '0.01';

# The engine half of the Festival rewrite (Games::Sokoban::Fest 1.03 of the
# Sokoban project).  Games::Sokoban::Solver::Fest::Analysis prepares the level
# and hands it over; everything that asks a question of a POSITION is here.
#
# Conventions: subs are named for what they answer, not for what the C
# transcription called them, and each carries a
#
#     # was: <old name> (Festival.pm:NNNN)
#
# line pointing back into the original.
#
# THERE ARE NO ACCESSOR SUBS IN THIS FILE, on purpose.  "Is this cell blocked"
# is three hash lookups and is written out as three hash lookups wherever it
# is asked:
#
#     $Wall{$q} or $frozen->{$q} or $box->{$q}
#
# so that what a test asks can be read where it asks it.  Two things make that
# possible, and both are arranged elsewhere so that nothing here has to check:
#
#   * a neighbour is always a cell number -- a floor cell or a wall cell --
#     because no level has floor on the rim of its rectangle (FestDev.pm
#     refuses one that does);
#   * every cell in cg, cm, cp and side, key or value, is a floor cell, so
#     code that walks those maps -- the player's region, the sides of a box,
#     every push and pull -- never asks about walls at all, as Firstbet never
#     does.  Only the tests that look at a SHAPE -- a corner, a full 2x2 block,
#     a diagonal, room to manoeuvre -- go by direction (%N, %N8), and only
#     they mention %Wall: there the wall is part of what is being asked.
use v5.42;
use Carp           ();
use Compress::Zlib ();
use List::Util ('min');
use Scalar::Util                    ();
use Storable                        ();
use Time::HiRes                     ();
use Games::Sokoban::Solver::Memory  ();
use Games::Sokoban::Solver::Munkres ();
use Games::Sokoban::Solver::Path    ();
no warnings('recursion');

# The whole of the outside world's business with this module: hand solve() the
# level's record as Fest::Analysis::analysis_record packs it, with a budget and
# a mode, and it takes the level itself.  solve() has the shape every engine
# of this distribution has (Firstbet's), so a Race pool can run it;
# run() is the same with everything a mode has to tell, for a caller that
# wants more than the verdict.  Nothing is exported: both are called by their
# full names.
# Run control, the other half of that contract (as in Festival.pm).  $BLOK
# turns the blok test on in every mode (what run() takes as $opt->{'blok'}).
# $MAX_GB is the memory net against the WHOLE machine's RAM in use, in GiB,
# 0 = off: a search that crosses it stops as MEMCAP.  $RACE_FLAG and
# $RACE_GID are set by a Race worker: when another mode has solved the game,
# the search stops as IGNORE.  $LastFail is why the last solve() stopped
# short, as the mode told it ('' when it has nothing to say).
our ($BLOK, $LastFail, $MAX_GB, $RACE_FLAG, $RACE_GID) = (0, '', 0);

# Why the running solve was stopped from outside ('' = it was not), the
# second the race flag was last looked at, and when memory is looked at next.
# Reset by solve().
my ($Abort, $Next_poll, $Tick) = ('', 0, 0);

# ASKED BY EVERY SEARCH LOOP beside its clock: has the run been stopped from
# outside?  Once it has, it stays stopped, so a mode that goes on to its next
# phase leaves that at once too.  The race flag is a shared hash, looked at
# once a second; memory is one kernel call, looked at every eight.
sub run_aborted () {
    return 1 if $Abort;
    my $now = time;
    return 0 if $now == $Tick;
    $Tick = $now;
    if ($RACE_FLAG and $RACE_GID and $RACE_FLAG->{$RACE_GID}) {
        $Abort = 'IGNORE';
        return 1;
    }
    return 0 if $now < $Next_poll;
    $Next_poll = $now + 8;
    $Abort     = 'MEMCAP' if $MAX_GB and Games::Sokoban::Solver::Memory::used_gb() > $MAX_GB;
    return $Abort ? 1 : 0;
}

# The level, out of its RECORD -- the one Fest::Analysis builds and this file
# never does.  What the Parser's analysis holds as it stands
# (%Blok %Cg %Cm %Floor %Goal %Start $Sok0 $Width), what can be read off the
# shape (%Cp %D %Goal_hole %Impossible %N %N8 %Pattern %Pattern_at %Room
# @Room_area %Side %Tunnel_pull %Tunnel_push %Walk %Wall), what only a search
# can find (%Mpdb %Pull_mpdb @Envelope $Snail), and what the modes need of
# the level (%Blocks %Goals_away %Goals_near $Girl_context $Room_links0).  Set
# by take_level() and never written anywhere else.
my (
    %Blocks,      %Blok,        %Cg,         %Cm,         %Cp,         %D,    %Floor,
    %Goal,        %Goal_hole,   %Goals_away, %Goals_near, %Impossible, %Mpdb, %N,
    %N8,          %Pattern,     %Pattern_at, %Pull_mpdb,  %Room,       %Side, %Start,
    %Tunnel_pull, %Tunnel_push, %Walk,       %Wall
   );
my (@Envelope, @Room_area);
my ($Girl_context, $Room_links0, $Snail, $Sok0, $Width);

# What a search leaves behind, cleared by take_level() so that one process
# can run one game after another.
my (%Base_landing, %Dead_cache, %Far_pulls, @Stuck);

# The stamp a record has to carry: Fest::Analysis's $ANALYSIS_STAMP, which is
# bumped whenever what a record holds changes shape or meaning.
my $RECORD_STAMP = 'fest record 2';

# TAKE A LEVEL: its record, PACKED as Fest::Analysis::analysis_record packs
# it, unpacked here into the variables
# above, and what the searches of the last level left behind is forgotten.  A
# record with another stamp is refused, never guessed at.
sub take_level ($blob) {
    my $record = Storable::thaw(Compress::Zlib::uncompress($blob) // Carp::confess('take_level: the blob does not uncompress'));
    Carp::confess("take_level: record stamped '" . ($record->{'stamp'} // '(none)') . "', this engine reads '$RECORD_STAMP'")
        if ($record->{'stamp'} // '') ne $RECORD_STAMP;
    %Blok         = %{ $record->{'blok'} };
    %Cg           = %{ $record->{'cg'} };
    %Cm           = %{ $record->{'cm'} };
    %Floor        = %{ $record->{'floor'} };
    %Goal         = %{ $record->{'goal'} };
    %Start        = %{ $record->{'start'} };
    $Sok0         = $record->{'sok0'};
    $Width        = $record->{'width'};     # for "same row / same column", and for the one test that looks past a run's last cell
    %Cp           = %{ $record->{'cp'} };
    %D            = %{ $record->{'d'} };
    %Goal_hole    = %{ $record->{'goal_hole'} };
    %Impossible   = %{ $record->{'impossible'} };
    %N            = %{ $record->{'n'} };
    %N8           = %{ $record->{'n8'} };
    %Pattern      = %{ $record->{'pattern'} };
    %Pattern_at   = %{ $record->{'pattern_at'} };
    %Room         = %{ $record->{'room'} };
    @Room_area    = @{ $record->{'room_area'} };
    %Side         = %{ $record->{'side'} };
    %Tunnel_pull  = %{ $record->{'tunnel_pull'} };
    %Tunnel_push  = %{ $record->{'tunnel_push'} };
    %Walk         = %{ $record->{'walk'} };
    %Wall         = %{ $record->{'wall'} };
    %Mpdb         = %{ $record->{'mpdb'} };
    %Pull_mpdb    = %{ $record->{'pull_mpdb'} };
    @Envelope     = @{ $record->{'envelope'} };
    $Snail        = $record->{'snail'};
    %Blocks       = %{ $record->{'blocks'} };
    %Goals_away   = %{ $record->{'goals_away'} };
    %Goals_near   = %{ $record->{'goals_near'} };
    $Girl_context = $record->{'girl_context'};
    $Room_links0  = $record->{'room_links0'};
    %Base_landing = ();                              # worked out per set of bases, when first asked for
    %Dead_cache   = ();                              # what the small searches for dead positions have found out
    %Far_pulls    = ();                              # ... and the distance test, per set of walls
    @Stuck        = ();                              # ... and the stuck patterns a search has learnt
    return;
} ## end sub take_level

# ---------------------------------------------------------------------------
# The view
# ---------------------------------------------------------------------------
#
# A VIEW is what the byte board used to be, taken apart into the things it was
# carrying at once:
#
#   box     => {cell => 1}   the boxes -- the position itself
#   sok     => cell          where the player stands
#   frozen  => {cell => 1}   cells the engine is TEMPORARILY treating as walls
#   reach   => {cell => 1}   the player's region
#   base    => {cell => 1}   only in the backward search that takes boxes off
#                            the board: the starting cells still waiting for a
#                            box (see "Bases")
#
# frozen is the one that repays reading twice.  The old code wallified a cell
# by ASSIGNING the WALL byte, which silently threw away the fact that the cell
# held a box and, if it was a goal, that it was a goal.  Here the box set stays
# true, and the two places where "a frozen box is a wall, not a box" decides
# something say so themselves (dead_push, dead_on_arrival), as does the one
# place where a goal under a frozen box no longer counts (live_cells).
#
# Two rules keep reach honest, so that $reach->{$q} can be asked bare:
# set_reach never floods into a frozen cell, and whoever freezes a free cell
# takes it out of reach (close_hole is the only one that does).
# was: expand_sokoban_cloud (Festival.pm:365) and flood_mask (349)
#
# The SOKOBAN bit was never one cell.  It was the whole region the player can
# walk, flooded over the board after every move, and read back at 47 places as
# "can the player get here".  The old flood is a fixpoint of string shifts --
# the cloud shifted by one cell and by one row, masked with the free cells --
# which is why Festival has to keep the whole w*h rectangle in the first place:
# a neighbour is +-1 and +-Width only if the rows are laid out end to end.
# Over the neighbour map it is an ordinary queue walk.
#
# The player's own cell is in the region even when a box stands on it (the old
# seed is written into the cloud before the free mask is applied) -- but not
# when it is frozen, since a frozen cell answers every question as a wall.
sub set_reach ($v) {
    my ($box, $frozen) = @$v{ 'box', 'frozen' };
    my %seen = ($v->{'sok'} => 1);
    my @q    = ($v->{'sok'});
    my $bh   = 0;
    while ($bh < @q) {
        foreach my $nb (@{ $Cg{ $q[$bh++] } }) {
            next if $seen{$nb} or $frozen->{$nb} or $box->{$nb};
            $seen{$nb} = 1;
            push @q, $nb;
        }
    }
    delete $seen{ $v->{'sok'} } if $frozen->{ $v->{'sok'} };
    $v->{'reach'} = \%seen;
    return $v;
} ## end sub set_reach

# The free floor, cut into regions by the boxes and the frozen cells: returns
# ({cell => region number}, [[cells of region 0], [cells of region 1], ...]),
# the regions numbered in the order of their smallest cell.
#
# was: mark_connectivities (Festival.pm:757), and get_connectivity (745) for
# the mere count
sub regions ($v) {
    my ($box,    $frozen) = @$v{ 'box', 'frozen' };
    my (%region, @cells_of);
    foreach my $start (sort {$a <=> $b} keys %Floor) {
        next if defined $region{$start} or $frozen->{$start} or $box->{$start};
        my $id = @cells_of;
        my @q  = ($start);
        $region{$start} = $id;
        my $bh = 0;
        while ($bh < @q) {
            foreach my $nb (@{ $Cg{ $q[$bh++] } }) {
                next if defined $region{$nb} or $frozen->{$nb} or $box->{$nb};
                $region{$nb} = $id;
                push @q, $nb;
            }
        }
        push @cells_of, \@q;
    } ## end foreach my $start (sort {$a...})
    return (\%region, \@cells_of);
} ## end sub regions

# Which rooms are still joined to which, with the boxes standing as they do:
# returns {room}{room} = 1, both ways.  Two rooms are joined when one can be
# walked to from the other without passing through a third -- over corridor
# cells, which belong to no room, or straight across where they touch.
#
# It is worked out room by room, and the rule for a room the boxes have cut in
# pieces is the original's and a harsh one: a link counts only if EVERY piece
# of the room has it.  One more oddity is kept as well: a neighbouring room
# counts as seen the moment one of its cells is met, even if a box stands on
# that very cell.
#
# was: get_current_graph (Festival.pm, Festival_Parser.pm:3173) over rooms_bfs
# (3143), a rooms x rooms matrix of 0/1
sub room_links ($v) {
    my ($box, $frozen) = @$v{ 'box', 'frozen' };
    my $nrooms = @Room_area;
    my (%link, %done, %met_room);
    foreach my $i (0 .. $nrooms - 1) {
        $link{$i}{$_} = 1 foreach grep {$_ != $i} 0 .. $nrooms - 1;
    }
    foreach my $start (sort {$a <=> $b} keys %Room) {
        next if $done{$start} or $frozen->{$start} or $box->{$start};
        my $mine = $Room{$start};
        $met_room{$mine} = 1;
        my %seen = ($start => 1);
        my %met;
        my @q  = ($start);
        my $bh = 0;
        $done{$start} = 1;

        while ($bh < @q) {
            foreach my $nb (@{ $Cg{ $q[$bh++] } }) {
                if (defined $Room{$nb} and $Room{$nb} != $mine) {
                    $met{ $Room{$nb} } = 1;
                    next;
                }
                next if $seen{$nb} or $done{$nb} or $frozen->{$nb} or $box->{$nb};
                $seen{$nb} = 1;
                $done{$nb} = 1 if defined $Room{$nb};
                push @q, $nb;
            }
        }
        foreach my $other (grep {!$met{$_}} 0 .. $nrooms - 1) {
            delete $link{$mine}{$other};
            delete $link{$other}{$mine};
        }
    } ## end foreach my $start (sort {$a...})
    foreach my $i (grep {!$met_room{$_}} 0 .. $nrooms - 1) {
        delete $link{$i};
        delete $link{$_}{$i} foreach keys %link;
    }
    return \%link;
} ## end sub room_links

# How many joins between rooms the boxes have broken, against the empty level
# ($Room_links0, worked out once per level by FestDev and kept in the record).
# The search scores a position by it: boxes that cut the rooms apart are boxes
# in the way.
#
# was: score_rooms (Festival.pm), against @Base_graph
sub rooms_cut_apart ($v) {
    return 0 if @Room_area <= 1;
    my $now  = room_links($v);
    my $lost = 0;
    foreach my $i (keys %$Room_links0) {
        $lost += grep {!$now->{$i}{$_}} keys %{ $Room_links0->{$i} };
    }
    return $lost / 2;
}

# The region the player is in, as one number: its smallest cell.  Computed
# when asked and never stored, because freezing can take the smallest cell
# out of the region and a stored number would then be stale.
sub region_of ($v) {
    return min(keys %{ $v->{'reach'} }) // -1;
}

# The identity of a position: which cells hold boxes, and which region the
# player is in.  Two player cells of one region are the same position.
#
# was: unpack('q', Digest::MD5::md5($brd)) (Festival.pm:390).  That hashed the
# whole board -- walls, goals, bases and the deadlock zone included -- and the
# module then had to undo it: get_hash_without_bases (3601) exists only to
# strip the BASE bits back out before hashing.  Here what belongs to identity
# is a line of code instead of a mask.
#
# In the search that takes boxes off the board the bases still waiting are part
# of the position: two lines of play that have sent different boxes home may
# hold the same boxes and still not have the same future.
sub poskey ($v) {
    my $key = join(',', sort {$a <=> $b} keys %{ $v->{'box'} }) . '|' . region_of($v);
    $key .= '|' . join(',', sort {$a <=> $b} keys %{ $v->{'base'} }) if $v->{'base'};
    return $key;
}

# ---------------------------------------------------------------------------
# The leaf predicates
# ---------------------------------------------------------------------------
# Can the box on p be pushed ACROSS the direction d -- and pushed on from there
# for one more cell?  Both directions across d are tried; each needs the push
# and the push after it to be pushes of the level (cm), the two landing cells
# free, and the player's cell on the far side free.
#
# was: can_be_pushed_sideways (Festival.pm:1121), same name kept -- it already
# said what it answers.  The original asks the bare geometry; stepping aside
# is a push, and a push the level's map does not have is in no solution, so
# here the map is asked (USER 2026-10-01).  The one caller keeps a box that
# cannot step aside in its deadlock zone, so this can only make a zone bigger.
sub can_be_pushed_sideways ($v, $p, $d) {
    my ($box, $frozen) = @$v{ 'box', 'frozen' };
    my $cm = $Cm{$p} or return 0;
    foreach my $e (($d + 1) & 3, ($d + 3) & 3) {
        my $to     = $N{$p}[$e];
        my $stance = $cm->{$to} // next;
        next if $frozen->{$to} or $box->{$to};
        my $beyond = $N{$to}[$e];
        next     if !defined(($Cm{$to} // {})->{$beyond}) or $frozen->{$beyond} or $box->{$beyond};
        return 1 if !($frozen->{$stance} or $box->{$stance});
    }
    return 0;
}

# Is the box on p stuck in a full 2x2 block?
#
# was: is_box_2x2_frozen_at_index (Festival.pm:1424)
#
# The old version walked the four possible top-left anchors of a 2x2 square
# containing p; the same four squares are the four DIAGONAL neighbours of p
# with the two cells between.  In the ring of eight the diagonals are the odd
# indices and their two neighbours in the ring are the other cells of that
# square.
sub is_frozen_in_square ($v, $p) {
    my ($box, $frozen) = @$v{ 'box', 'frozen' };
    my $n8 = $N8{$p};
    foreach my $k (1, 3, 5, 7) {
        return 1 if 3 == grep {$Wall{$_} or $frozen->{$_} or $box->{$_}} @$n8[$k - 1, $k, ($k + 1) & 7];
    }
    return 0;
}

# Does the box on p touch a free cell the player cannot reach?  That is the
# cheap sign of a corral: the box is part of what walls the player out.
#
# was: box_touches_unreachable_square (Festival.pm:2425)
sub touches_unreachable ($v, $p) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    foreach my $q (@{ $N8{$p} }) {
        next     if $Wall{$q} or $frozen->{$q} or $box->{$q};
        return 1 if !$reach->{$q};
    }
    return 0;
}

# Has the box that has just arrived on p completed one of the library's
# deadlock patterns?  The library was laid over the level by the parser; what
# is left to ask of each placement whose window covers p is whether its boxes
# are there, its empty cells are empty and on the right side of the player's
# reach, and its frozen cells are frozen.
#
# A pattern is about a box being walled off from the player, so nothing is
# looked at unless the box touches a free cell he cannot get to.  In a pull
# search two more things must hold: the player is shut into a region of at
# most four cells, and it is not the region he started the level in -- a pull
# search runs backwards, and being shut in where the real game BEGINS is how
# every solution looks from that end.
#
# was: check_all_patterns (Festival.pm:2536), which returned the number of the
# pattern or -1; nobody ever used the number.
sub pattern_dead ($v, $p, $pull) {
    return 0 if !touches_unreachable($v, $p);
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    if ($pull) {
        return 0 if keys %$reach > 4 or $reach->{$Sok0};
        foreach my $i (@{ $Pattern_at{'pull'}{$p} // [] }) {
            my $need = $Pattern{'pull'}[$i];
            next if grep {!$box->{$_} or $frozen->{$_}} @{ $need->{'box'} };
            next if grep {!$frozen->{$_}} @{ $need->{'frozen'} };
            next if grep {!$reach->{$_}} @{ $need->{'reach'} };
            return 1;
        }
        return 0;
    }
    foreach my $i (@{ $Pattern_at{'push'}{$p} // [] }) {
        my $need = $Pattern{'push'}[$i];
        next if grep {!$box->{$_} or $frozen->{$_}} @{ $need->{'box'} };
        next if grep {!$frozen->{$_}} @{ $need->{'frozen'} };
        next if grep {$box->{$_} or $frozen->{$_} or $reach->{$_}} @{ $need->{'void'} };
        return 1;
    }
    return 0;
} ## end sub pattern_dead

# Would pushing the box on p one cell in direction d kill it on the spot?  Four
# shapes are looked for, all of them on the three cells ahead of the landing
# cell and the two beside it:
#
#   * the landing cell is one no box may ever stand on (impossible{});
#   * it is a corner -- a wall straight ahead and a wall on either side -- and
#     not a goal;
#   * there is a box straight ahead and the pair is wedged between two walls
#     set diagonally across it, one beside the landing cell and one beside the
#     box ahead on the other side; neither box could ever move again, so both
#     have to be on goals;
#   * the push completes a full 2x2 block with a box in it that is not on a
#     goal.
#
# "Wall" here is a wall or a frozen cell, and "box" is a box that is NOT
# frozen: a frozen box has already been judged, and it stands on a goal or the
# position would not have got this far.
#
# was: deadlock_in_direction (Festival.pm:2338), which found the five cells
# with $Delta_p arithmetic and the two squares through a per-direction anchor
# table, @Square_place_p.  The ring of eight neighbours holds all of them: a
# direction d sits at ring index 2d, the cells beside it at 2d+-2 and the two
# diagonals ahead at 2d+-1 -- and the two squares are simply "landing cell,
# cell ahead, and the pair on one side".
sub dead_push ($v, $p, $d) {
    my ($box, $frozen) = @$v{ 'box', 'frozen' };
    my $np = $N{$p}[$d];
    return 1 if $Wall{$np} or $Impossible{$np};
    my $r  = 2 * $d;
    my $n8 = $N8{$np};
    my ($ahead, $right, $left) = @$n8[$r, ($r + 2) & 7, ($r + 6) & 7];
    my ($ahead_right, $ahead_left) = @$n8[($r + 1) & 7, ($r + 7) & 7];
    my %is_wall = map {$_ => ($Wall{$_} or $frozen->{$_})} $ahead, $right, $left, $ahead_right, $ahead_left;

    if (!$Goal{$np} and $is_wall{$ahead}) {
        return 1 if $is_wall{$right} or $is_wall{$left};
    }
    if ($box->{$ahead} and !$frozen->{$ahead}) {
        if (($is_wall{$right} and $is_wall{$ahead_left}) or ($is_wall{$left} and $is_wall{$ahead_right})) {
            return 1 if !$Goal{$np} or !$Goal{$ahead};
        }
    }

    # the boxes as they would stand after the push
    my %after = %$box;
    delete $after{$p};
    $after{$np} = 1;
    foreach my $square ([$np, $ahead, $right, $ahead_right], [$np, $ahead, $left, $ahead_left]) {
        next     if grep {!($Wall{$_} or $frozen->{$_} or $after{$_})} @$square;
        return 1 if grep {$after{$_} and !$frozen->{$_} and !$Goal{$_}} @$square;
    }
    return 0;
} ## end sub dead_push

# Is there anything at all the player can do with the box on p right now?
# Pushing needs a free landing cell, the player behind the box, and a push that
# does not kill the box at once; pulling needs the player beside the box and a
# free cell for him to step back onto.
#
# was: box_can_be_moved (Festival.pm:3253).  It is the door in front of the
# move generator -- box_moves is only ever called for a box that passed.  It
# reads cm and cp, so like every predicate over the maps it may say no where
# the original said yes, and never the other way round.
sub can_be_moved ($v, $p, $pull) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    return 0 if !$box->{$p} or $frozen->{$p};
    if ($pull) {
        my $cp = $Cp{$p} or return 0;
        foreach my $to (keys %$cp) {
            next if !$reach->{$to};
            my $back = $cp->{$to};
            return 1 if !$frozen->{$back} and !$box->{$back};
        }
        return 0;
    }
    my $cm = $Cm{$p} or return 0;
    foreach my $d (0 .. 3) {
        my $to     = $N{$p}[$d];
        my $stance = $cm->{$to} // next;
        next     if $frozen->{$to} or $box->{$to} or !$reach->{$stance};
        return 1 if !dead_push($v, $p, $d);
    }
    return 0;
} ## end sub can_be_moved

# ---------------------------------------------------------------------------
# Making a move
# ---------------------------------------------------------------------------
#
# A move says which box moves, where it lands, and where the player is left
# standing.  The old one also carried a DIRECTION for the player (two bits,
# read back as $to + $Delta_p[$m->{sokoban_position}]), which is the same fact
# written as an offset because there was no room for a cell number.  Here it is
# the cell.
#
# Where the player ends up is not the same fact in the two directions, and the
# maps already know it:
#
#   push from -> to : he was standing on cm{from}{to} and walks into `from`
#   pull from -> to : he was standing on `to` and steps back to cp{from}{to}
sub start_view () {
    return set_reach({ 'box' => {%Start}, 'frozen' => {}, 'sok' => $Sok0 });
}

# One push, if it can be made in this view: the map has it, the landing cell
# is free and the player can get behind the box.
sub push_move ($v, $from, $to) {
    my $cm     = $Cm{$from} or return undef;
    my $stance = $cm->{$to} // return undef;
    return undef if $v->{'frozen'}{$to} or $v->{'box'}{$to} or !$v->{'reach'}{$stance};
    return { 'from' => $from, 'to' => $to, 'man' => $from, 'pull' => 0 };
}

# One pull: the map has it, the player can get to the cell the box will land
# on, and the cell he steps back onto is free.
sub pull_move ($v, $from, $to) {
    my $cp   = $Cp{$from} or return undef;
    my $back = $cp->{$to} // return undef;
    return undef if !$v->{'reach'}{$to} or $v->{'frozen'}{$back} or $v->{'box'}{$back};
    return { 'from' => $from, 'to' => $to, 'man' => $back, 'pull' => 1 };
}

# Make the move, and hand back a NEW view -- the old one is left alone, so a
# search can keep it.
#
# was: apply_move (Festival.pm:3303).  That one took the board apart and put it
# back together with six vec writes and a whole-board re-flood: clear the
# player bit everywhere, clear the box bit here, set it there, set the player
# bit on one cell, flood.  Three of those six writes only existed to undo what
# the representation had done to itself.
#
# The frozen set is NOT carried over.  It belongs to the analysis that was
# being run on the position, not to the position -- and the old code says the
# same thing by wallifying a COPY and applying moves to the original.
#
# A KILL move takes a box off the board altogether: some of the auxiliary
# searches do that to a box they have decided is no longer part of the
# question.  The player does not move; his region grows into whatever the box
# was shutting off, from wherever he already was -- which, for a player who is
# "everywhere", is from every region at once.
#
# A BASE move (only in a view that has bases) is a pull that ends on a base:
# the box has come home to a cell a box starts on, and both leave the board --
# the box and the base.  The player is left where the pull left him, and his
# region is flooded without the box.
sub apply ($v, $m) {
    my %box = %{ $v->{'box'} };
    delete $box{ $m->{'from'} };
    if ($m->{'isbase'}) {
        my %base = %{ $v->{'base'} };
        delete $base{ $m->{'to'} };
        return set_reach({ 'box' => \%box, 'frozen' => {}, 'sok' => $m->{'man'}, 'base' => \%base });
    }
    if ($m->{'kill'}) {
        my %reach = %{ $v->{'reach'} };
        my @q     = keys %reach;
        my $bh    = 0;
        while ($bh < @q) {
            foreach my $nb (@{ $Cg{ $q[$bh++] } }) {
                next if $reach{$nb} or $box{$nb};
                $reach{$nb} = 1;
                push @q, $nb;
            }
        }
        return { 'box' => \%box, 'frozen' => {}, 'sok' => $v->{'sok'}, 'reach' => \%reach };
    }
    $box{ $m->{'to'} } = 1;
    my $after = { 'box' => \%box, 'frozen' => {}, 'sok' => $m->{'man'} };
    $after->{'base'} = $v->{'base'} if $v->{'base'};
    return set_reach($after);
} ## end sub apply

# ---------------------------------------------------------------------------
# Freezing: the cells the engine decides to treat as walls
# ---------------------------------------------------------------------------
#
# was: turn_fixed_boxes_into_walls (Festival.pm:2405) and the family under it
#
# Before generating moves, Festival takes a COPY of the board and hammers walls
# into it: boxes that can never move again, pockets the player can enter but
# never use, boxes frozen against each other.  Each member of the family used
# to hand the next one a whole new board string; here they all add to one set
# and say whether they added anything, and the loop is the same loop.
#
#
# freeze_envelopes is the odd one out: it applies rules prepared by the level
# analysis instead of looking at the board, and it runs once, before the loop.
sub freeze_fixed ($v) {
    freeze_envelopes($v);
    my $changed = 1;
    while ($changed) {
        $changed = 0;
        $changed |= freeze_2x2($v);
        $changed |= close_hole($v);
        $changed |= freeze_immovable($v);
        $changed |= freeze_diagonals($v);
        $changed |= freeze_crystaline($v);
    }
    return $v;
}

# An ENVELOPE is a rule the level analysis worked out in advance: a ring of
# cells round some corner of the level such that, once something stands on
# every one of them and the player is outside, the boxes of the ring can never
# be got at again.  The analysis proved it by trying -- it set the ring up and
# searched for a way to finish the level from there -- so here it is only
# looked up: every cell of the ring taken, and the player's region inside the
# region the rule allows.
#
# It is a third kind of knowledge beside the static (true of the level) and the
# dynamic (worked out on this position): a static CONDITION, prepared once and
# laid on a position when it comes.
#
# was: fix_boxes_using_envelopes (Festival.pm:1299) with
# matches_envelope_pattern (1286) and wallify_boxes_using_pattern (1278)
sub freeze_envelopes ($v) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    my $changed = 0;
    foreach my $rule (@Envelope) {
        next if grep {!$frozen->{$_} and !$box->{$_}} @{ $rule->{'box'} };
        next if grep {!$rule->{'allowed'}{$_}} keys %$reach;
        foreach my $p (@{ $rule->{'box'} }) {
            next if $frozen->{$p};
            $frozen->{$p} = 1;
            $changed = 1;
        }
    }
    return $changed;
}

# Every cell of a fully blocked 2x2 block is a cell nothing will ever move
# through, so the boxes in it become walls.
#
# was: turn_2x2_to_walls (Festival.pm:1307).  That one walked every anchor of
# the rectangle; only a block holding a box can change anything, so this walks
# the boxes instead -- the same four blocks, reached from the other end.
sub freeze_2x2 ($v) {
    my ($box, $frozen) = @$v{ 'box', 'frozen' };
    my $changed = 0;
    foreach my $p (keys %$box) {
        next if $frozen->{$p};
        my $n8 = $N8{$p};
        foreach my $k (1, 3, 5, 7) {
            my @rest = @$n8[$k - 1, $k, ($k + 1) & 7];
            next if 3 != grep {$Wall{$_} or $frozen->{$_} or $box->{$_}} @rest;
            foreach my $c ($p, @rest) {
                next if !$box->{$c} or $frozen->{$c};
                $frozen->{$c} = 1;
                $changed = 1;
            }
            last;
        }
    }
    return $changed;
} ## end sub freeze_2x2

# A free cell with at most one side that is not wall is a pocket: the player
# can step in, but no box can ever be parked there and nothing can pass
# through, so it is wall.  Goal cells are never closed, and a pocket the player
# can reach is only closed when its one open side is reachable too -- that is,
# not while he is standing in it with a box in the mouth.
#
# was: close_holes (Festival.pm:1331).  It closes ONE hole per call and lets
# the caller loop, which is kept here because closing one can open the next;
# cells are taken in numeric order, which is the row-by-row order of the old
# scan.
sub close_hole ($v) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    foreach my $p (sort {$a <=> $b} keys %Floor) {
        next if $box->{$p} or $frozen->{$p} or $Goal{$p};
        my @open = grep {!$frozen->{$_}} @{ $Cg{$p} };
        next if @open > 1;
        next if $reach->{$p} and !(@open and $reach->{ $open[0] });
        $frozen->{$p} = 1;
        delete $reach->{$p};
        return 1;
    }
    return 0;
}

# Take away every box that could be pushed somewhere without dying at once,
# again and again, each removal making room for the next.  The boxes that are
# left when nothing more can be taken away can never be pushed by anybody, in
# any order, and they become walls.
#
# was: turn_immovable_boxes_to_walls (Festival.pm:2392) over
# remove_all_pushable_boxes (2373)
#
# "Could be pushed" asks nothing about the player: the cell behind the box has
# to be free, not reachable.  That is deliberate -- the player's region is a
# fact about this moment, and the question is about every moment to come.
#
# Removing a box can only make other boxes pushable, never the reverse (every
# test below is "is something in the way"), so the order of removal does not
# matter and the boxes left over are the same whichever box goes first.
#
# It reads cm, so a push the level's own geometry has ruled out does not count
# as a way to move the box -- which can only freeze MORE than the original did
# (measured: 1.2 % more cells).
sub freeze_immovable ($v) {
    my $frozen  = $v->{'frozen'};
    my %left    = map {$_ => 1} grep {!$frozen->{$_}} keys %{ $v->{'box'} };
    my $rest    = { 'box' => \%left, 'frozen' => $frozen };
    my $removed = 1;
    while ($removed) {
        $removed = 0;
    BOX: foreach my $p (keys %left) {
            my $cm = $Cm{$p} or next;
            foreach my $d (0 .. 3) {
                my $to     = $N{$p}[$d];
                my $stance = $cm->{$to} // next;
                next if $frozen->{$to} or $left{$to} or $frozen->{$stance} or $left{$stance};
                next if dead_push($rest, $p, $d);
                delete $left{$p};
                $removed = 1;
                next BOX;
            }
        }
    } ## end while ($removed)
    my $changed = 0;
    foreach my $p (keys %left) {
        $frozen->{$p} = 1;
        $changed = 1;
    }
    return $changed;
} ## end sub freeze_immovable

# A DIAGONAL VOID: a run of empty cells lying corner to corner, each of them
# walled in on all four sides and out of the player's reach, with the run
# capped at both ends.  Nothing can ever pass through such a chain, so the
# boxes lining it can never move again and become walls.
#
# was: fix_diagonals (Festival.pm:1402) with mark_diags (886),
# diag_has_no_targets (977) and wallify_diag_void (947)
#
# The old three between them read the board 40-odd times through offsets built
# out of $Width, and the two directions are written out twice, once with
# $Width+1 and once with $Width-1, differing only in a handful of +1/-1 signs.
# Here a run is walked along one index of the ring of eight -- 3 is down and to
# the right, 5 down and to the left -- and every other cell the test looks at
# is a ring neighbour of the run's first or last cell.
#
# The runs are found ONCE, up front, and then the walling is applied to them
# one after another, as the original does.  Only boxes are ever frozen here and
# the cells of a run are empty, so one run's walling cannot change another
# run's cells or the goals on them.
sub freeze_diagonals ($v) {
    my ($box, $frozen) = @$v{ 'box', 'frozen' };
    my $changed = 0;
    foreach my $run (@{ diagonal_voids($v) }) {
        my ($cells, $diag) = @$run;
        next if grep {$Goal{$_}} @$cells;
        my ($first,  $last) = @$cells[0, -1];
        my ($behind, $end)  = ($N8{$first}[$diag == 3 ? 7 : 1], $N8{$last}[$diag]);

        # the cells flanking each void cell left and right, the cell above the
        # run and the cell below it
        my @line = map {@{ $N8{$_} }[6, 2]} @$cells;
        push @line, $N8{$first}[0], $N8{$last}[4];

        # the two corner caps -- they count only if something stands there;
        # the run may have been capped by a pair of walls instead
        push @line, grep {$frozen->{$_} or $box->{$_}} $behind, $end;
        foreach my $q (@line) {
            next if !$box->{$q} or $frozen->{$q};
            $frozen->{$q} = 1;
            $changed = 1;
        }
    } ## end foreach my $run (@{ diagonal_voids...})
    return $changed;
} ## end sub freeze_diagonals

# Every diagonal run, as [[its cells, top to bottom], ring index it runs
# along].
#
# The two ends are NOT capped by the same test, and the difference is easy to
# read past in the original.  At the head, what has to be blocked is the cell
# one diagonal step BEFORE the run.  At the foot, it is the first cell that is
# not a void -- the run's own next step.  Both fall back on the same
# alternative: the two cells flanking that corner on the run's side are both
# wall (a real wall or a frozen cell, not a box).
sub diagonal_voids ($v) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    my %void;
    foreach my $p (keys %Floor) {
        next if $box->{$p} or $frozen->{$p} or $reach->{$p};
        next if grep {!($Wall{$_} or $frozen->{$_} or $box->{$_})} @{ $N{$p} };
        $void{$p} = 1;
    }
    my @runs;
    foreach my $p (sort {$a <=> $b} keys %void) {
        foreach my $diag (3, 5) {
            my ($behind, $side) = $diag == 3 ? @{ $N8{$p} }[7, 6] : @{ $N8{$p} }[1, 2];
            my $up = $N8{$p}[0];
            next
                if !($Wall{$behind} or $frozen->{$behind} or $box->{$behind})
                and !(($Wall{$up} or $frozen->{$up}) and ($Wall{$side} or $frozen->{$side}));
            my @cells = ($p);
            push @cells, $N8{ $cells[-1] }[$diag] while $void{ $N8{ $cells[-1] }[$diag] };
            my $last = $cells[-1];
            my $end  = $N8{$last}[$diag];
            my ($beside, $below) = @{ $N8{$last} }[$diag == 3 ? 2 : 6, 4];
            next
                if !($Wall{$end} or $frozen->{$end} or $box->{$end})
                and !(($Wall{$beside} or $frozen->{$beside}) and ($Wall{$below} or $frozen->{$below}));
            push @runs, [\@cells, $diag];
        } ## end foreach my $diag (3, 5)
    } ## end foreach my $p (sort {$a <=>...})
    return \@runs;
} ## end sub diagonal_voids

# Put a box on every goal -- the solved position, with the walls as they now
# stand -- and take away every box that could still be pulled off its goal.
# What is left standing is crystalline: boxes that, once home, can never be
# moved again.  A box already standing on one of those cells is a wall.
#
# was: fix_crystaline (Festival.pm:1365).  The original has to carry the input
# board alongside the hypothetical one and compare them cell by cell at the
# end, because writing WALL into the hypothetical board destroyed the record of
# which cells had held a box.  Here the hypothetical boxes are their own set
# and the real ones are never touched.
#
# "Could be pulled off" is asked of cp: a pull the map does not have undoes a
# push that is in no solution, so it is no way for the last box to have come
# home.  (The original asks the bare geometry.)  Why what is left is safe to
# wall in: take the LAST push of a solution that puts a box on a cell of the
# set.  The cell it comes from and the cell the player pushes from are both
# empty afterwards, so neither is in the set -- a cell of the set left empty
# would need a later push into the set -- and neither is frozen; then that
# box could have been pulled off, and its cell would not be in the set.
sub freeze_crystaline ($v) {
    my ($box, $frozen) = @$v{ 'box', 'frozen' };
    my %home    = map {$_ => 1} grep {!$frozen->{$_}} keys %Goal;
    my $removed = 1;
    while ($removed) {
        $removed = 0;
    HOME: foreach my $p (keys %home) {
            my $cp = $Cp{$p} or next;
            foreach my $to (keys %$cp) {
                next if $frozen->{$to} or $home{$to};
                my $beyond = $cp->{$to};
                next if $frozen->{$beyond} or $home{$beyond};
                delete $home{$p};
                $removed = 1;
                next HOME;
            }
        }
    }
    my $changed = 0;
    foreach my $p (keys %home) {
        next if !$box->{$p};
        $frozen->{$p} = 1;
        $changed = 1;
    }
    return $changed;
} ## end sub freeze_crystaline

# ---------------------------------------------------------------------------
# Where boxes can travel, on a board with no boxes on it
# ---------------------------------------------------------------------------
# side{p}{q} on a board that has temporary walls on it.  Frozen cells cut
# regions apart that the bare level leaves joined, so the static map is only
# good for a view with nothing frozen.
#
# was: zones_around_place (Festival.pm:776) as init_shift (1504) calls it --
# once per cell, for every graph it builds.  The walk is the one FestDev.pm
# uses to build the static map; it is repeated here rather than called, so
# that the engine needs nothing of FestDev but the data.
sub sides_in ($v, $p) {
    my $frozen = $v->{'frozen'};
    return $Side{$p} if !%$frozen;
    my %label;
    my $next = 0;
    foreach my $start (@{ $Cg{$p} }) {
        next if $frozen->{$start} or defined $label{$start};
        my $mark = $next++;
        my %seen = ($start => 1);
        my @q    = ($start);
        my $bh   = 0;
        while ($bh < @q) {
            foreach my $nb (@{ $Cg{ $q[$bh++] } }) {
                next if $nb == $p or $seen{$nb} or $frozen->{$nb};
                $seen{$nb} = 1;
                push @q, $nb;
            }
        }
        foreach my $other (@{ $Cg{$p} }) {
            $label{$other} = $mark if $seen{$other};
        }
    } ## end foreach my $start (@{ $Cg{$p...}})
    return \%label;
} ## end sub sides_in

# How many pushes (or pulls) it takes to bring a box from ANY of the seed cells
# to each cell it can get to, on a board that has the view's frozen cells for
# walls and no boxes at all -- whatever boxes the view holds are ignored.
# Returns {cell => pushes}; a cell that is not there cannot be reached.
#
# was: the whole family over build_graph (Festival.pm:1573) and
# do_graph_iterations (1592) --
#
#   find_targets_of_a_group (1693), find_targets_of_a_board_input (1710)
#       push, and only the key set is wanted: where can these boxes go
#   find_sources_of_a_group (1676), find_sources_of_a_board_input (1719)
#       pull, key set: where can a box come from to land on one of these
#   find_distance_from_a_group (1746)
#       either direction, the numbers themselves
#   find_targets_of_place_without_init_graph (1730) with make_holes_inactive
#       (1480): one seed, push, $strict set
#
# Those were five subs because the answer came back painted on a board, and a
# board of marks, a board of distances and "a board of marks that always
# includes the seeds" are three different boards.  As a hash they are one.
# (The originals count a seed as reached even when it is walled in on all four
# sides and nothing could ever stand beside it; this does not.  A caller that
# wants the seeds in the set has them already.)
#
# It is the walk that built the distance table -- over (cell, side of the box
# the player is on) -- with three differences: many seeds, either direction,
# and the sides taken from the view.
#
# The numbers are true minima.  The original's are not always: its relaxation
# charges a round for walking round the box, so a route with many changes of
# side can lose the race to a longer one.  The SET of cells reached is the
# same either way.
#
# $strict leaves out one kind of seed: the player standing in a dead-end
# pocket behind the box.  He can only be there if he is there NOW -- once a
# box stands in the mouth of the pocket nobody gets in -- so unless the view
# says he is in the pocket and cut off from the box's cell, that side of the
# box is not a place to start pushing from.  The matching test wants this; the
# others never ask.
#
# $side is a place to keep the sides of the cells between calls: they depend
# on the frozen cells only, so a caller that asks many questions of one board
# hands in the same hash every time and pays for each cell once.
sub box_spread ($v, $seeds, $pull, $strict = 0, $side = {}) {
    my $frozen = $v->{'frozen'};
    my $map    = $pull ? \%Cp : \%Cm;
    my (%d, %seen, @q);
    foreach my $p (@$seeds) {
        next if !$Floor{$p} or $frozen->{$p};
        my $label = $side->{$p} //= sides_in($v, $p);
        foreach my $stance (keys %$label) {
            next if $strict and stance_in_dead_pocket($v, $p, $stance);
            next if $seen{"$p/$label->{$stance}"}++;
            $d{$p} = 0;
            push @q, [$p, $label->{$stance}, 0];
        }
    }
    my $bh = 0;
    while ($bh < @q) {
        my ($p, $s, $n) = @{ $q[$bh++] };
        my $label = $side->{$p} //= sides_in($v, $p);
        foreach my $to (keys %{ $map->{$p} // {} }) {
            my $other = $map->{$p}{$to};    # pushing: where he pushes from; pulling: where he steps back to
            next if $frozen->{$to} or $frozen->{$other};

            # he has to be on the right side of the box to begin with: behind
            # it to push, on the cell it will be pulled onto to pull
            next if $label->{ $pull ? $to : $other } != $s;

            # and he is left on the cell the box came from, or stepped back
            my $land = ($side->{$to} //= sides_in($v, $to))->{ $pull ? $other : $p };
            next if $seen{"$to/$land"}++;
            $d{$to} //= $n + 1;
            push @q, [$to, $land, $n + 1];
        }
    } ## end while ($bh < @q)
    return \%d;
} ## end sub box_spread

# Is the stance beside this box a dead-end pocket the player is not in?
#
# was: make_holes_inactive (Festival.pm:1480), which struck such (cell, side)
# vertices out of the graph after it was built
sub stance_in_dead_pocket ($v, $box_cell, $stance) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    return 0 if $box->{$stance};
    return 0 if 1 != grep {!$frozen->{$_}} @{ $Cg{$stance} };
    return 0 if $reach->{$stance} and !$reach->{$box_cell};
    return 1;
}

# ---------------------------------------------------------------------------
# What a Festival move is
# ---------------------------------------------------------------------------
#
# Not one push.  A Festival move takes ONE box and carries it as far as it
# will go -- any number of pushes, round corners, with the player walking round
# the box in between -- while every other box stays where it is.  So "the moves
# of a position" is, for every box, the set of places that box can be taken to,
# and generating them is a small search of its own, run once per box.
#
# What distinguishes two outcomes of that small search is where the box ends
# up AND which region the player is left in, because those two together are
# the position that results.  The box arriving on the same cell from two sides
# is one move if the player can walk from one side to the other, and two moves
# if the box cuts him off.  That pair -- (cell of the box, region of the
# player) -- is the state of the search below.
#
# The original ran the same search over a graph of Index_num*4 vertices, one
# per (cell, DIRECTION the player stands in), and joined the directions of one
# region afterwards with a "shift" table of Index_num*16 entries that it
# rebuilt by flooding the board after every push (update_shift, 1762).  Since
# it stamps all directions of a region in the same breath, its vertices fall
# into exactly the classes used here; the direction it reports for a move is
# whichever one arrived first -- and since "the first macro that ..." decides
# things further on, box_moves walks in the original's order so that "first"
# is the same one.
# The cells a box may be on and still get to SOME goal, given the walls as
# they now stand -- frozen boxes included, the other boxes ignored, and no
# thought for where the player is.  It is walked backwards from the goals:
# a box can come to p from `from` if the push from -> p exists and neither the
# cell it starts on nor the cell the player pushes from is frozen.
#
# was: get_srcs_of_all_targets (Festival.pm:796), the push half of
# get_possible_places (4890)
#
# THIS IS THE DYNAMIC HALF OF "IMPOSSIBLE", and the half that carries weight.
# The record's %Impossible is computed once, on the empty level.  This one is
# computed for every position, after the freezing, and shrinks with every box
# that freezes: a goal under a frozen box is taken for good and is no longer
# somewhere to go, and a frozen box is a wall in the way.  Everything outside
# the set is a landing cell from which the box could never be brought home.
sub live_cells ($v) {
    my $frozen = $v->{'frozen'};
    my @q      = grep {!$frozen->{$_}} keys %Goal;
    my %ok     = map  {$_ => 1} @q;
    my $bh     = 0;
    while ($bh < @q) {
        my $cp = $Cp{ $q[$bh++] } or next;
        foreach my $from (keys %$cp) {
            next if $ok{$from} or $frozen->{$from} or $frozen->{ $cp->{$from} };
            $ok{$from} = 1;
            push @q, $from;
        }
    }
    return \%ok;
} ## end sub live_cells

# Would a box arriving on the free cell p be dead at once, the other boxes
# standing as they do?  Two shapes:
#
#   * a corner -- two walls at right angles -- that is not a goal;
#   * the last free cell of a 2x2 block whose other three cells are taken,
#     unless everything that would then be stuck is on a goal: p itself and
#     every box among the three that is not frozen already.
#
# $box is the set of the OTHER boxes: the box being moved has been lifted off,
# or it would count as one of the three that make its own neighbour a dead
# cell.
#
# was: mark_deadlock_2x2 (Festival.pm:2275), which swept every 2x2 anchor of
# the rectangle and painted a whole board of marks for the generator to
# consult.  Asked of one cell it is the four squares that contain p, which the
# ring of eight neighbours already has: a diagonal at an odd index, and the
# two cells between it and p on either side of it.
#
# Static corners never get this far -- they are avoid cells and have no edge
# in cm.  The corners found here are the ones the frozen boxes make.
sub dead_on_arrival ($box, $frozen, $p) {
    my $n8 = $N8{$p};
    foreach my $k (1, 3, 5, 7) {
        my ($side1, $corner, $side2) = @$n8[$k - 1, $k, ($k + 1) & 7];
        return 1 if !$Goal{$p} and ($Wall{$side1} or $frozen->{$side1}) and ($Wall{$side2} or $frozen->{$side2});
        next     if 3 != grep {$Wall{$_} or $frozen->{$_} or $box->{$_}} $side1, $corner, $side2;
        return 1 if !$Goal{$p};
        return 1 if grep {$box->{$_} and !$frozen->{$_} and !$Goal{$_}} $side1, $corner, $side2;
    }
    return 0;
}

# The cells the box on `from` may land on, or pass over, in this position.
# $live is live_cells() of the position when pushing, and undef when pulling:
# a pull search runs backwards from the goals, so "can still get home" is not
# a question it asks.
#
# was: set_current_impossible (Festival.pm:2310), turned inside out.  The
# original builds a board of the cells that are FORBIDDEN and every reader
# negates it; the set of cells that are allowed is the thing actually wanted.
sub landing_cells ($v, $from, $pull, $live) {
    my $frozen = $v->{'frozen'};
    my %rest   = %{ $v->{'box'} };
    delete $rest{$from};
    my %ok;
    foreach my $p (keys %Floor) {
        next if $Impossible{$p} or $frozen->{$p};
        if (!$pull) {
            next if !$live->{$p};
            next if !$rest{$p} and dead_on_arrival(\%rest, $frozen, $p);
        }
        $ok{$p} = 1;
    }
    return \%ok;
} ## end sub landing_cells

# Every place the box on `from` can be taken to, the other boxes standing
# still.  $ok is landing_cells() for this box.  Returns a list of moves:
#
#   from, to     the box's cell before and after
#   man          the cell the player is left standing on
#   side         which side of `to` that is: 0 up, 1 right, 2 down, 3 left
#   pull         0 for a push search, 1 for a pull search
#   pushes       how many single pushes (or pulls) the box travelled
#   reversible   the box can be brought back to `from`, with the player back
#                in the region he started in
#   last_from    [every cell the box can make its LAST single push from and
#                still end in this same position] -- there may be several: the
#                box can come onto `to` from two sides and leave the player in
#                one region either way
#
# apply() takes such a move as it stands.
#
# was: mark_box_moves_in_graph (Festival.pm:1777), find_reversible_moves (1845)
# and get_box_moves_from_graph (1646), over the graph of allocate_graph (1450)
#
# It is a breadth-first walk in which every step is ONE ordinary push, made
# with push_move on a view that holds the other boxes, the frozen cells, and
# this box wherever it has got to.  The flood that finds the player's region
# after each push is the same set_reach every position gets; the original had
# a second one written into the generator.
#
# A box may come back to the cell it started on and that is still a move, if
# the player ends up on the far side of it, in a region he could not reach
# before: nothing moved, and the position is a different one.
#
# REVERSIBLE is read off the same walk.  Every push tried is remembered as an
# edge between two states, whether or not it led anywhere new, and a state is
# reversible when the starting state can be reached from it along those edges.
# The original walks the other way -- it UNDOES pushes outward from the start
# and keeps the states the forward walk had seen -- which is the same set.
#
# With $want_route every move also carries `route`: the single pushes it is
# made of, as [[cell, next cell], ...], along a shortest way.  Only whoever
# turns a finished solution back into player steps asks for it.
sub box_moves ($v, $from, $pull, $ok, $want_route = 0) {
    return () if !$v->{'box'}{$from} or $v->{'frozen'}{$from};
    my $step = $pull ? \&pull_move : \&push_move;
    my %rest = %{ $v->{'box'} };
    delete $rest{$from};

    # Where the walk starts: the box on `from`, the player in his region.  In
    # an ordinary view that is one state.  The level analysis also asks about
    # a player who is "everywhere at once" -- every free cell marked reachable,
    # to try a position from all sides in one go -- and then each region that
    # touches the box is a starting state of its own; coming back to any of
    # them is coming back to the start.
    my $first = $from . '|' . region_of($v);
    my %start = ($first => 1);
    my @flood;
    foreach my $side (grep {$v->{'reach'}{$_}} @{ $Cg{$from} }) {
        next if grep {$_->{$side}} @flood;
        my $there = set_reach({ 'box' => $v->{'box'}, 'frozen' => $v->{'frozen'}, 'sok' => $side });
        push @flood, $there->{'reach'};
        $start{ $from . '|' . region_of($there) } = 1;
    }

    # THE ORDER the sides of the box are tried in is part of the answer.  A
    # state can be arrived at from several sides, and the macro is named after
    # the side that got there FIRST -- so "first" has to mean what it meant in
    # the original: states in the order they were found, and at each state the
    # side the player arrived on before the others (up, right, down, left).
    # With the player on side j a push sends the box the other way, a pull
    # brings it towards him; either way he is on side j of the new cell too.
    my %seen = ($first => 1);
    my @q    = ([$from, $v, $first, 0, undef]);
    my (@moves, @state, %undone_by, %last_from, %came_by);
    my $bh = 0;
    while ($bh < @q) {
        my ($c, $view, $key, $n, $came) = @{ $q[$bh++] };
        foreach my $j (defined $came ? ($came, grep {$_ != $came} 0 .. 3) : 0 .. 3) {
            my $to = $N{$c}[$pull ? $j : $j ^ 2];
            next if !$ok->{$to};
            my $m        = $step->($view, $c, $to) or next;
            my $next     = set_reach({ 'box' => { %rest, $to => 1 }, 'frozen' => $v->{'frozen'}, 'sok' => $m->{'man'} });
            my $next_key = $to . '|' . region_of($next);
            $next_key                   = $first if $start{$next_key};
            $undone_by{$next_key}{$key} = 1;
            $last_from{$next_key}{$c}   = 1;
            next if $seen{$next_key}++;
            $came_by{$next_key} = [$key, $c, $to];
            push @moves,
                {
                    'from'       => $from,
                    'to'         => $to,
                    'man'        => $m->{'man'},
                    'side'       => $j,
                    'pull'       => $pull,
                    'pushes'     => $n + 1,
                    'reversible' => 0,
                };
            push @state, $next_key;
            push @q,     [$to, $next, $next_key, $n + 1, $j];
        } ## end foreach my $j (defined $came...)
    } ## end while ($bh < @q)

    # walk the edges backwards from the start
    my %back = ($first => 1);
    my @bq   = ($first);
    while (defined(my $key = shift @bq)) {
        foreach my $prev (keys %{ $undone_by{$key} // {} }) {
            push @bq, $prev if !$back{$prev}++;
        }
    }
    foreach my $i (0 .. $#moves) {
        $moves[$i]{'reversible'} = 1 if $back{ $state[$i] };
        $moves[$i]{'last_from'}  = [sort {$a <=> $b} keys %{ $last_from{ $state[$i] } }];
        next if !$want_route;
        my @route;
        for (my $key = $state[$i]; $came_by{$key}; $key = $came_by{$key}[0]) {
            unshift @route, [@{ $came_by{$key} }[1, 2]];
        }
        $moves[$i]{'route'} = \@route;
    }
    return @moves;
} ## end sub box_moves

# ---------------------------------------------------------------------------
# The corral
# ---------------------------------------------------------------------------
#
# The boxes cut the free floor into regions, and the player is in one of them.
# A CORRAL is a part of the floor he cannot get into -- one region, or several
# that belong together -- with the boxes standing round it.  If
#
#   * there is still something to do in there (an empty goal inside, or a box
#     on its edge that is not on a goal),
#   * no box on its edge can be pushed anywhere BUT into it, and
#   * every push into it that the edge boxes allow is one the player can make
#     right now, from where he is,
#
# then sooner or later one of those pushes has to be made, nothing done
# elsewhere can change which ones they are, and so it may as well be made NOW:
# the move generator is told to move edge boxes only.  (The literature calls
# this a PI-corral, for "player inside"... of the rest of the board.)  It is
# the largest single cut in the branching factor the engine has.
#
# Returns {box => 1, ...} -- the edge boxes that have such a push -- or undef
# when there is no corral to be had.
#
# was: detect_corral (Festival.pm:2932) and the fifteen subs above it, which
# kept the regions as a per-cell array of numbers, the corral as a board of
# marks, and rebuilt a third board ("corral boxes": the walls, the corral as
# player bits, and only the boxes that touch it) for every question they asked.
# Here a region is a list of cells, the corral is a set, and the edge boxes are
# a set.
#
# A push is tested on a board that holds ONLY the edge boxes, which is
# deliberate and the original's: whether an edge box could be pushed into the
# corral must not depend on a box further off that happens to stand in the
# way today.
#
# How the corral grows: start from a region that lies straight across a box
# from the player (or from two regions one box touches), and as long as some
# edge box could be pushed into the corral FROM another unreachable region, or
# past the corral into one, that region is part of the same problem and is
# taken in.  The order of taking in is the original's -- edge boxes by cell,
# directions 0..3 -- since the first corral that passes is the one used.
sub corral_boxes ($v) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    return undef if !%$reach;
    my ($region, $cells_of) = regions($v);
    my %region   = %$region;
    my @cells_of = @$cells_of;
    my $mine     = $region{ min(keys %$reach) };
    my @boxes    = sort {$a <=> $b} grep {!$frozen->{$_}} keys %$box;

    # a candidate is a region straight across a box from the player's
    my (%candidate, %touch);
    foreach my $p (@boxes) {
        foreach my $k (0 .. 3) {
            my ($near, $far) = @region{ @{ $N{$p} }[$k, $k ^ 2] };
            $candidate{$far} = 1 if defined $near and $near == $mine and defined $far and $far != $mine;
        }
        my @round = grep {defined} @region{ @{ $N{$p} } };
        foreach my $r1 (@round) {
            $touch{$r1}{$_} = 1 foreach @round;
        }
    }
    my $try = sub (@ids) {
        my %used   = map {$_ => 1} @ids;
        my %corral = map {$_ => 1} map {@{ $cells_of[$_] }} @ids;
        my (%edge, $edge_view);
        my $find_edge = sub () {
            %edge      = map {$_ => 1} grep {$box->{$_} and !$frozen->{$_}} map {@{ $N8{$_} }} keys %corral;
            $edge_view = { 'box' => \%edge, 'frozen' => $frozen };
        };
        my $taken = sub ($q) {$Wall{$q} or $frozen->{$q} or $edge{$q}};

        # could the box on p be pushed from `pusher` into the corral?  The
        # pusher's cell may hold another edge box; callers that mind say so.
        my $into = sub ($p, $k) {
            my ($pusher, $dest) = @{ $N{$p} }[$k, $k ^ 2];
            return 0 if $Wall{$pusher}   or $frozen->{$pusher} or $taken->($dest);
            return 0 if $corral{$pusher} or !$corral{$dest};
            return 0 if !defined(($Cm{$p} // {})->{$dest});
            return !dead_push($edge_view, $p, $k ^ 2);
        };

        # something left to do in there?
        $find_edge->();
        return undef if !grep({ $Goal{$_} } keys %corral) and !grep({!$Goal{$_}} keys %edge);

        # take in the regions that belong to the same problem
    GROW: while (1) {
            $find_edge->();
            foreach my $p (sort {$a <=> $b} keys %edge) {
                next if !grep {$corral{$_}} @{ $N{$p} };
                next if !grep {!$taken->($_) and !$corral{$_}} @{ $N{$p} };
                foreach my $k (0 .. 3) {
                    my ($pusher, $dest) = @{ $N{$p} }[$k, $k ^ 2];
                    my @more;
                    push @more, $region{$pusher} if $into->($p, $k) and !$edge{$pusher};
                    push @more, $region{$dest}
                        if !$taken->($pusher)
                        and !$taken->($dest)
                        and !$corral{$pusher}
                        and !$corral{$dest}
                        and defined(($Cm{$p} // {})->{$dest})
                        and !dead_push($edge_view, $p, $k ^ 2);
                    foreach my $id (grep {defined $_ and $_ != $mine and !$used{$_}} @more) {
                        $used{$id}  = 1;
                        $corral{$_} = 1 foreach @{ $cells_of[$id] };
                        next GROW;
                    }
                } ## end foreach my $k (0 .. 3)
            } ## end foreach my $p (sort {$a <=>...})
            last;
        } ## end GROW: while (1)
        my %option;
        foreach my $p (keys %edge) {
            foreach my $k (0 .. 3) {
                my ($pusher, $dest) = @{ $N{$p} }[$k, $k ^ 2];

                # a push that stays outside altogether: the box can get away
                return undef
                    if !$taken->($pusher)
                    and !$taken->($dest)
                    and !$corral{$pusher}
                    and !$corral{$dest}
                    and defined(($Cm{$p} // {})->{$dest})
                    and !dead_push($edge_view, $p, $k ^ 2);

                # a push into it that he cannot make from here
                next         if !$into->($p, $k) or $edge{$pusher};
                return undef if !$reach->{$pusher};
                $option{$p} = 1;
            } ## end foreach my $k (0 .. 3)
        } ## end foreach my $p (keys %edge)
        return \%option;
    }; ## end sub
    foreach my $id (grep {$candidate{$_}} 0 .. $#cells_of) {
        my $option = $try->($id) or next;
        return $option;
    }
    foreach my $i (grep {$_ != $mine} 0 .. $#cells_of) {
        foreach my $j (grep {$_ != $mine} $i + 1 .. $#cells_of) {
            next if !$candidate{$i} and !$candidate{$j};
            next if !$touch{$i}{$j};
            my $option = $try->($i, $j) or next;
            return $option;
        }
    }
    return undef;
} ## end sub corral_boxes

# ---------------------------------------------------------------------------
# Which moves are worth keeping
# ---------------------------------------------------------------------------
# Is the position a move leads to one the search should never enter?  Returns
# the name of the test that said so, or '' when the move stands.  $after is the
# view after the move (the frozen cells of the view it was made from carried
# along), $m the move.
#
# Options:
#   blok        ask %Game's blok table about the last single push INSTEAD of
#               the forbidden pairs, the frozen cluster, the 3x3 test and the
#               pattern library (the project's measured substitution; the
#               engine's $BLOK_REPLACES)
#   inefficient 0 lets a box be left standing where that is merely wasteful
#   keep        cells where a box may be left standing however wasteful it
#               looks -- a search aiming for a particular arrangement says so
#               (was: the imagined_hf_board test in is_inefficient_position,
#               Festival.pm:2567, HF pushing and REV pulling: any cell whose
#               byte on that board is not zero, which is the boxes AND the
#               player's region of the imagined position)
#   bases       the bases of the position the pull is made FROM (possible_moves
#               puts them there itself when the view has any)
#   far_pulls   the distance test's search (see boxes_that_must_be_there): its
#               own, laxer idea of whether a pull leaves anything to go on with
#
# was: check_deadlock_in_moves (Festival.pm:3999), with
# verify_simple_base_matching (3539)
sub why_dead ($after, $m, $opt) {
    my $to = $m->{'to'};

    # `bases` (the pull search that takes boxes off the board): a box brought
    # onto a base is asked nothing at all -- it is home
    my $bases = $opt->{'bases'};
    return ''           if $bases and $bases->{$to};
    return 'impossible' if $Impossible{$to};
    if ($m->{'pull'}) {
        return 'pair' if forbidden_pair($after, \%Pull_mpdb);
        return 'inefficient'
            if ($opt->{'inefficient'} // 1)
            and !($opt->{'keep'} and $opt->{'keep'}{$to})
            and is_inefficient($after, $to, 1);
        return 'no continuation' if !($opt->{'far_pulls'} ? can_go_on_pulling_far($after) : can_go_on_pulling($after));
        return 'pattern'         if pattern_dead($after, $to, 1);

        # ... and anywhere else, every base must still have SOME box that
        # could have been pushed here from it
        if ($bases) {
            my @boxes = keys %{ $after->{'box'} };
            foreach my $base (keys %$bases) {
                return 'base without a box' if !grep {defined $D{$base}{$_}} @boxes;
            }
        }
        return '';
    } ## end if ($m->{'pull'})

    # `keep`: cells where a box may be left standing however wasteful it looks
    # -- a search that is aiming for a particular arrangement says so
    my $wasteful =
        (($opt->{'inefficient'} // 1) and !($opt->{'keep'} and $opt->{'keep'}{$to}) and is_inefficient($after, $to, 0));
    if ($opt->{'blok'}) {
        return 'blok'        if blok_forbids($after, $m);
        return 'inefficient' if $wasteful;
        return '';
    }
    return 'pair'        if forbidden_pair($after, \%Mpdb);
    return 'inefficient' if $wasteful;
    return 'frozen'      if is_frozen_cluster($after, $to);
    return 'shut in'     if is_shut_in_3x3($after, $to);
    return 'pattern'     if pattern_dead($after, $to, 0);
    return '';
} ## end sub why_dead

# Do two boxes stand on a pair of cells the analysis found can never both be
# occupied?  A frozen box does not count -- it is a wall.
#
# was: is_mpdb_deadlock and is_pull_mpdb_deadlock (Festival.pm:3333-3354),
# which walked the whole list of pairs for every position
sub forbidden_pair ($v, $pair) {
    my ($box, $frozen) = @$v{ 'box', 'frozen' };
    foreach my $p (keys %$box) {
        next     if $frozen->{$p} or !$pair->{$p};
        return 1 if grep {$box->{$_} and !$frozen->{$_}} keys %{ $pair->{$p} };
    }
    return 0;
}

# %Game's own table, asked about the LAST single push of the move: the box
# came onto `to` from the cell the player is now standing on.  A list of the
# table is a set of cells that must not all hold boxes once it has.
#
# was: blok_forbids (Festival.pm:2676).  Frozen boxes DO count here -- the
# original tests the box set of the board from before the freezing, and the
# box set of a view is that set.
#
# ONE DELIBERATE DIFFERENCE, the first in this file.  A move can end in the
# same position by two different last pushes (the box comes onto `to` from two
# sides, the player is left in one region either way), and the table may
# condemn one of them and not the other.  The original asks about ONE -- the
# one its walk happened to reach first, to + Delta[sokoban_position] -- so
# whether it keeps the move is an accident of the order of that walk (game
# 24479: box 121 -> 135, from 134 dead, from 122 not).  But the table's verdict
# is about the POSITION: these boxes, the player in this region.  It is the
# same position whichever push came last, so if any of them is condemned the
# position is dead, and that is what is asked here.  The model can therefore
# throw away a move the original keeps, never the reverse.
#
# The table is %Game's own and is read as it stands: each entry is a bit string
# over the cells, and "every cell of it holds a box" is the project's test,
# ($boxes &. $entry) eq $entry -- the dotted operator, because under v5.42 a
# string AND needs it.  An entry is trimmed at its highest cell, and the AND
# comes out as long as the shorter operand, which is what makes the comparison
# right whichever of the two is shorter.
sub blok_forbids ($after, $m) {
    my $boxes = '';
    vec($boxes, $_, 1) = 1 foreach keys %{ $after->{'box'} };
    foreach my $from (@{ $m->{'last_from'} }) {
        my $entries = ($Blok{$from} // {})->{ $m->{'to'} } or next;
        foreach my $entry (@$entries) {
            return 1 if ($boxes &. $entry) eq $entry;
        }
    }
    return 0;
}

# Is the box on p part of a cluster that can never be pushed again, some of it
# not on goals?  Take away every box that has a push with both its cells free,
# over and over; what is left is stuck, and if any of it stands off a goal the
# position is dead.
#
# was: is_freeze_deadlock (Festival.pm:2445).  It is freeze_immovable's walk
# without the look at what the push leads to -- and it asks about the whole
# board, but only when the box that has just moved cannot be pushed itself.
sub is_frozen_cluster ($v, $p) {
    my $frozen = $v->{'frozen'};
    my %left   = map {$_ => 1} grep {!$frozen->{$_}} keys %{ $v->{'box'} };
    my $free   = sub ($q) {
        my $cm = $Cm{$q} or return 0;
        foreach my $to (keys %$cm) {
            next     if $frozen->{$to} or $left{$to};
            return 1 if !$frozen->{ $cm->{$to} } and !$left{ $cm->{$to} };
        }
        return 0;
    };
    return 0 if $free->($p);
    my $removed = 1;
    while ($removed) {
        $removed = 0;
        foreach my $q (keys %left) {
            next if !$free->($q);
            delete $left{$q};
            $removed = 1;
        }
    }
    return (grep {!$Goal{$_}} keys %left) ? 1 : 0;
} ## end sub is_frozen_cluster

# Has the box on p helped to shut a free cell in for good?  Looked for among
# the nine cells round p: a free cell that is not a goal, with all four sides
# taken and a box that is not on a goal among them, whose corners are taken in
# one of the ways that mean none of those four can ever be moved off it.
#
# was: is_3x3_deadlock (Festival.pm:2467)
sub is_shut_in_3x3 ($v, $p) {
    return 0 if !touches_unreachable($v, $p);
    my ($box, $frozen) = @$v{ 'box', 'frozen' };
    my $taken = sub ($q) {$Wall{$q} or $frozen->{$q} or $box->{$q}};
    my $wall  = sub ($q) {$Wall{$q} or $frozen->{$q}};
    foreach my $q ($p, @{ $N8{$p} }) {
        next if !$Floor{$q} or $taken->($q) or $Goal{$q};
        next if grep  {!$taken->($_)} @{ $N{$q} };
        next if !grep {$box->{$_} and !$frozen->{$_} and !$Goal{$_}} @{ $N{$q} };
        my $ring = $N8{$q};
        return 1 if $taken->($ring->[7]) and $taken->($ring->[3]);
        return 1 if $taken->($ring->[1]) and $taken->($ring->[5]);
        foreach my $i (0, 2, 4, 6) {
            next if !$wall->($ring->[$i]);
            my ($c1, $c2) = @$ring[($i + 3) & 7, ($i + 5) & 7];
            next     if !$taken->($c1) or !$taken->($c2);
            return 1 if $wall->($c1)   or $wall->($c2);
        }
    }
    return 0;
} ## end sub is_shut_in_3x3

# Is leaving a box on p a waste of a move?  Not a deadlock: a position the
# search is better off never entering, because the same box could have been
# taken one cell further at no cost.  A goal is never wasteful when pushing,
# and a cell a box starts on never is when pulling.
#
#   * p lies in a tunnel (the record's %Tunnel_push / %Tunnel_pull);
#   * pushing: p is in the mouth of a passage -- walls at both corners on one
#     side of it -- and one of six arrangements of the cells beside it says the
#     box is only in the way there;
#   * pulling: p is one step into such a passage, with a wall two cells on.
#
# The six and the two are the original's, turned through the four directions
# by walking the ring of eight; they are reproduced as they stand.
#
# was: is_inefficient_position (Festival.pm:2559)
sub is_inefficient ($v, $p, $pull) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    my $ring = $N8{$p};
    my $wall = sub ($k) {my $q = $ring->[$k & 7]; $Wall{$q} or $frozen->{$q}};
    if ($pull) {
        return 0 if $Start{$p};
        return 1 if $Tunnel_pull{$p};
        foreach my $j (0, 2, 4, 6) {
            my $q = $ring->[$j];
            next if $Wall{$q} or $frozen->{$q} or $box->{$q};
            my $beyond = $N{$q}[$j >> 1];
            next     if !($Wall{$beyond} or $frozen->{$beyond});
            return 1 if $wall->($j + 1) and $wall->($j + 3) and $wall->($j + 4);
            return 1 if $wall->($j + 4) and $wall->($j + 5) and $wall->($j + 7);
        }
        return 0;
    }
    return 0 if $Goal{$p};
    return 1 if $Tunnel_push{$p};
    my $in_reach = sub ($k) {$reach->{ $ring->[$k & 7] }};
    my $is_box   = sub ($k) {my $q = $ring->[$k & 7]; $box->{$q} and !$frozen->{$q}};
    foreach my $j (0, 2, 4, 6) {
        next     if !$wall->($j + 3) or !$wall->($j + 5);
        return 1 if $wall->($j + 2)   and !$wall->($j + 6) and !$in_reach->($j + 6);
        return 1 if $wall->($j + 6)   and !$wall->($j + 2) and !$in_reach->($j + 2);
        return 1 if $wall->($j + 2)   and !$wall->($j + 6) and $in_reach->($j);
        return 1 if $wall->($j + 6)   and !$wall->($j + 2) and $in_reach->($j);
        return 1 if $is_box->($j + 2) and !$in_reach->($j + 6);
        return 1 if $is_box->($j + 6) and !$in_reach->($j + 2);
    }
    return 0;
} ## end sub is_inefficient

# In a pull search: is there anything left to do from here?  Either it is over
# -- every box back on a cell a box starts on, and the player able to reach
# the cell HE starts on -- or some box can still be pulled, by a pull the map
# has.
#
# was: has_pull_continuation (Festival.pm:3977), which asked the bare geometry
sub can_go_on_pulling ($v) {
    my ($box, $reach) = @$v{ 'box', 'reach' };
    return 1 if $reach->{$Sok0} and !grep {!$Start{$_}} keys %$box;
    return 1 if grep                      {can_be_moved($v, $_, 1)} keys %$box;
    return 0;
}

# ---------------------------------------------------------------------------
# All the moves of a position
# ---------------------------------------------------------------------------
#
# Pushing: freeze what can never move again, find where a box may still go,
# look for a corral, and then for every box that is allowed to move take
# everything the generator offers and keep what why_dead lets through.
# Pulling: the same without the freezing, the live cells and the corral --
# those are all statements about getting boxes HOME.
#
# Returns (\@moves, $has_corral).  The view handed in is not changed.
#
# Options: those of why_dead, and `corral => 0` to go without one.
#
# A pull search whose view has BASES gets two things more (see "Bases"): the
# landing cells are cut down to those a box could have been pushed to from a
# base, and the macros that bring a box home to a base are marked -- and if
# there are any, they are all that is offered.
#
# was: find_possible_moves (Festival.pm:5746), for the plain forward and
# backward searches and the one with bases.  What it does for the auxiliary
# searches -- the deadlock zone, the five kinds of "kill" move -- waits for
# those searches.
sub possible_moves ($v, $pull, $opt = {}) {

    # (a view comes with nothing frozen, except in the small searches for dead
    # positions: theirs are boxes that were walled in before the search began
    # and stay walls all through it)
    my $work =
        { 'box' => $v->{'box'}, 'frozen' => { %{ $v->{'frozen'} } }, 'sok' => $v->{'sok'}, 'reach' => { %{ $v->{'reach'} } } };
    my ($live, $only);
    if (!$pull) {
        freeze_fixed($work);
        $live = live_cells($work);
        $only = corral_boxes($work) if $opt->{'corral'} // 1;
    }

    # with bases, a box may only be pulled to where a box could have been
    # pushed from one of them
    my $bases     = $pull  ? $v->{'base'}         : undef;
    my $from_base = $bases ? base_landing($bases) : undef;
    $opt = { %$opt, 'bases' => $bases } if $bases;
    my @moves;
    foreach my $from (keys %{ $work->{'box'} }) {
        next if $only and !$only->{$from};
        next if !can_be_moved($work, $from, $pull);
        my $ok = landing_cells($work, $from, $pull, $live);
        if ($from_base) {delete @$ok{ grep {!$from_base->{$_}} keys %$ok }}
        foreach my $m (box_moves($work, $from, $pull, $ok, $opt->{'route'})) {
            my %box = %{ $work->{'box'} };
            delete $box{$from};
            $box{ $m->{'to'} } = 1;
            my $after = set_reach({ 'box' => \%box, 'frozen' => $work->{'frozen'}, 'sok' => $m->{'man'} });
            push @moves, $m if !why_dead($after, $m, $opt);
        }
    }
    @moves = mark_base_moves($v, \@moves) if $bases;
    return (\@moves, $only ? 1 : 0);
} ## end sub possible_moves

# The order the original hands out macros in: by box, by where it goes, and by
# the side the player is left on (up, right, down, left).  Wherever "the first
# one that ..." decides something, this is the order that is meant.
sub in_original_order (@moves) {
    my $side = sub ($m) {
        return $m->{'side'} if defined $m->{'side'};
        my ($d) = grep {$N{ $m->{'to'} }[$_] == $m->{'man'}} 0 .. 3;
        return $d // 4;
    };
    return map {$_->[1]}
        sort {$a->[1]{'from'} <=> $b->[1]{'from'} or $a->[1]{'to'} <=> $b->[1]{'to'} or $a->[0] <=> $b->[0]}
        map {[$side->($_), $_]} @moves;
}

# ---------------------------------------------------------------------------
# What only a search can tell about a level
# ---------------------------------------------------------------------------
#
# Part of the level analysis cannot be done by looking at the level: it has to
# TRY.  "Can two boxes standing on these two cells ever both be brought home?"
# is answered by setting the two boxes up and searching with the engine's own
# move generator.  FestDev.pm does that, once per level, with copies of the
# subs of this file, and what it found comes in the record: %Mpdb,
# %Pull_mpdb, @Envelope and the chain verdict $Snail
# (Games::Sokoban::FestDev::search_analysis).
#
# What stays here is the small search it is done with, because the dead
# position tests below search with it too, and can_be_packed, which one of
# them asks.
# Can the boxes of this position all be put on goals?  1 = yes, 0 = no, and
# that is a proof (every position that can be reached was looked at), -1 = gave
# up: $max positions were opened.
#
# It is a small best-first search with no plan and no distances.  Of all the
# moves not yet followed, anywhere in what has been opened so far, it follows
# the one that leaves MOST BOXES ON GOALS, and among equals the one that
# leaves the free floor in the fewest pieces.  A position none of whose moves
# leads anywhere alive is dead, and that is handed back up to whatever led to
# it.  No corral: on a board of two or three boxes there is nothing to gain.
#
# The starting view may have the player "everywhere": every free cell in its
# reach.  That asks the question for all his regions at once.
#
# was: can_put_all_on_targets (Festival_Parser.pm:5210) over
# set_first_position (5036), expand_position (5094),
# get_move_with_most_packing (5172) and mark_deadlocks (4926).  The original
# keeps per position five parallel arrays indexed by move number, a hash of
# the board per move, and a 64x64-bit filter over those hashes to find "the
# moves that lead to the position just opened"; here a move is a small hash
# that carries its own outcome, and positions are found by their key.
sub can_be_packed ($start, $max) {
    my $nbox   = keys %{ $start->{'box'} };
    my $result = small_search(
        {
            'start' => $start,
            'max'   => $max,
            'moves' => sub ($view) {(possible_moves($view, 0, { 'corral' => 0 }))[0]},

            # whatever the starting view has frozen is a wall for the whole search
            'play' => sub ($view, $m) {
                my %box = %{ $view->{'box'} };
                delete $box{ $m->{'from'} };
                $box{ $m->{'to'} } = 1;
                return set_reach({ 'box' => \%box, 'frozen' => $view->{'frozen'}, 'sok' => $m->{'man'} });
            },
            'solved' => sub ($view) {!grep {!$Goal{$_}} keys %{ $view->{'box'} }},
            'better' => sub ($son, $best) {
                $son->{'packed'} > $best->{'packed'}
                    or ($son->{'packed'} == $best->{'packed'} and $son->{'regions'} < $best->{'regions'});
            },

            # before each pick: a move of the newest position that packs them all
            # is as good as having made it
            'look' => sub ($open) {
                my $last = $open->[-1];
                return 'solved' if grep {$_->{'packed'} == $nbox} @{ $last->{'sons'} };
                return '';
            },
        }
    );
    return { 'solved' => 1, 'dead' => 0, 'unknown' => -1 }->{$result};
} ## end sub can_be_packed

# The search both analyses share.  A spec says where to start, which moves a
# position has, when a position is solved, which of two untried moves is the
# better one, and -- `look`, before every pick -- whether what has been opened
# so far already settles the matter.  Returns 'solved', 'dead' (a proof: all
# that can be reached was opened and none of it was solved) or 'unknown' (room
# for `max` positions was not enough).
#
# Every untried move carries what it leads to: the view after it, that view's
# key, how many boxes stand on goals there (`packed`) and how many on starting
# cells (`unpacked`), how many boxes there are (`boxes`), how many pieces the
# free floor is in (`regions`) and how big its deadlock zone is (`zone`).
#
# A spec may bring its own way of making a move (`play`) and of naming a
# position (`key`): the searches over a deadlock zone do, their positions
# having a zone that moves with the boxes.  And `look` may strike out untried
# moves itself (set their `dead`); what follows from that is settled before the
# next pick.
sub small_search ($spec) {
    my (@open, %at);
    my $play          = $spec->{'play'} // \&apply;
    my $key_of        = $spec->{'key'}  // \&poskey;
    my $open_position = sub ($view, $key, $father) {
        my @sons;
        foreach my $m (in_original_order(@{ $spec->{'moves'}->($view) })) {
            my $after = $play->($view, $m);
            push @sons,
                {
                    'after'    => $after,
                    'key'      => $key_of->($after),
                    'packed'   => scalar(grep {$Goal{$_}} keys %{ $after->{'box'} }),
                    'unpacked' => scalar(grep {$Start{$_}} keys %{ $after->{'box'} }),
                    'boxes'    => scalar(keys %{ $after->{'box'} }),
                    'regions'  => scalar @{ (regions($after))[1] },
                    'zone'     => scalar(keys %{ $after->{'zone'} // {} }),
                    'dead'     => 0,
                };
        }
        my $pos = { 'view' => $view, 'key' => $key, 'sons' => \@sons, 'dead' => 0, 'father' => $father };
        push @open, $pos;
        $at{$key} = $pos;
        return $pos;
    }; ## end sub

    # `solved` ends the search; `finished` is what keeps a position with no
    # way on from being called dead.  They are one question unless the spec
    # says otherwise.
    my $solved   = $spec->{'solved'};
    my $finished = $spec->{'finished'} // $solved;

    # a position is dead when it is not solved and every move out of it is dead
    # or leads to an opened position that is; settle that for everything opened
    my $settle = sub () {
        my $changed = 1;
        while ($changed) {
            $changed = 0;
            foreach my $pos (grep {!$_->{'dead'}} @open) {
                foreach my $son (@{ $pos->{'sons'} }) {
                    next if $son->{'dead'} or !$at{ $son->{'key'} } or !$at{ $son->{'key'} }{'dead'};
                    $son->{'dead'} = 1;
                    $changed = 1;
                }
                next if grep {!$_->{'dead'}} @{ $pos->{'sons'} };
                next if $finished->($pos->{'view'});
                $pos->{'dead'} = 1;
                $changed = 1;
            }
        }
    }; ## end $settle = sub

    # (the start goes by a name no move can lead to unless the spec says it is
    # a position like any other: the analyses start with the player
    # "everywhere", which is none)
    if ($spec->{'starts'}) {    # several, all of them positions like any other
        foreach my $start (@{ $spec->{'starts'} }) {
            my $key = $key_of->($start);
            $open_position->($start, $key, undef) if !$at{$key};
        }
    }
    else {
        $open_position->($spec->{'start'}, $spec->{'start_is_a_position'} ? $key_of->($spec->{'start'}) : 'start', undef);
    }
    $settle->();
    while (1) {
        my $verdict = $spec->{'look'}->(\@open);
        return $verdict if $verdict;
        $settle->();
        my ($best, $from);
        foreach my $pos (grep {!$_->{'dead'}} @open) {
            foreach my $son (grep {!$_->{'dead'} and !$at{ $_->{'key'} }} @{ $pos->{'sons'} }) {
                ($best, $from) = ($son, $pos) if !$best or $spec->{'better'}->($son, $best);
            }
        }
        return 'dead' if !$best;
        my $pos = $open_position->($best->{'after'}, $best->{'key'}, $from);
        $settle->();
        return 'solved'  if $solved->($pos->{'view'});
        return 'unknown' if @open == $spec->{'max'};
    } ## end while (1)
} ## end sub small_search

# ---------------------------------------------------------------------------
# Dead positions
# ---------------------------------------------------------------------------
#
# The filters of why_dead are asked of every macro a position has, so they
# have to be cheap, and they look at the box that moved.  The tests here look
# at the WHOLE position, cost far more, and are asked only of the one macro the
# tree has just picked to follow -- so a position pays for them when it is
# about to be opened, not when it is merely seen.
#
# was: board_is_deadlocked (Festival.pm:7538), of which these are the members
# that do no searching of their own
# Can every box be given a goal of its own that it could still be pushed to?
# (Pulling: a starting cell -- or a base -- it could have been pushed FROM.)
#
# Pushing, the question is asked after the freezing: a frozen box is a wall, and
# so is the goal under it; a box frozen OFF a goal leaves a box too few or a
# goal too many, and that is the end at once.  "Could be pushed to" is on the
# board without the other boxes, and leaves out the pushes that begin with the
# player in a dead-end pocket he is not in.
#
# was: check_matching_deadlock (Festival.pm:3464)
sub unmatched ($v, $pull) {
    return !boxes_match_bases($v->{'box'}, $v->{'base'} // \%Start) if $pull;
    my $work = { 'box' => $v->{'box'}, 'frozen' => {}, 'sok' => $v->{'sok'}, 'reach' => { %{ $v->{'reach'} } } };
    freeze_fixed($work);
    my $frozen = $work->{'frozen'};
    my @boxes  = grep {!$frozen->{$_}} keys %{ $v->{'box'} };
    my @goals  = grep {!$frozen->{$_}} keys %Goal;
    return 1 if @boxes != @goals;
    return 0 if !@boxes;
    my %side;
    my @cost = map {
        my $p  = $_;
        my $to = box_spread($work, [$p], 0, 1, \%side);
        [map {($_ == $p or defined $to->{$_}) ? 0 : 1} @goals]
    } @boxes;
    return Games::Sokoban::Solver::Munkres::assign(\@cost) ? 1 : 0;
} ## end sub unmatched

# Take away every box the player could pull one step right now, let him into
# the room that makes, and go on until nothing more comes away.  Returns the
# boxes left standing.  A pull is one the map has (cp): the cell the box comes
# onto in his reach, the cell he steps back to free.
#
# was: back_eliminate_loop (Festival.pm:3400) over simple_pull_box_eliminator,
# which asked the bare geometry
sub pulled_off_freely ($box, $frozen, $reach) {
    my %box   = %$box;
    my %reach = %$reach;
    my $again = 1;
    while ($again) {
        $again = 0;
        foreach my $p (keys %box) {
            my $cp = $Cp{$p} or next;
            foreach my $to (keys %$cp) {
                next if !$reach{$to};
                my $back = $cp->{$to};
                next if $frozen->{$back} or $box{$back};
                delete $box{$p};
                $reach{$p} = 1;
                $again = 1;
                last;
            }
        }
        next if !$again;
        my @q  = keys %reach;
        my $bh = 0;
        while ($bh < @q) {
            foreach my $nb (@{ $Cg{ $q[$bh++] } }) {
                next if $reach{$nb} or $box{$nb} or $frozen->{$nb};
                $reach{$nb} = 1;
                push @q, $nb;
            }
        }
    } ## end while ($again)
    return \%box;
} ## end sub pulled_off_freely

# Pulling: if even pulling with no regard for anything leaves a box that is
# not on a starting cell, that box will never be on one.
#
# was: free_pull_deadlock (Festival.pm:3433)
sub cannot_be_pulled_home ($v) {
    my $left = pulled_off_freely($v->{'box'}, {}, $v->{'reach'});
    return scalar grep {!$Start{$_}} keys %$left;
}

# Pushing, the same thought the other way round.  Imagine the level solved --
# a box on every goal that is not frozen over -- and pull freely from there.
# Whatever cannot be pulled off had better be standing there ALREADY.  The
# player may start in any of the regions the solved level has; one that works
# is enough.
#
# was: try_pulling_all_zones (Festival.pm:3420) with eliminate_from_zone (3409)
sub goals_cannot_be_emptied ($v) {
    my $work = { 'box' => $v->{'box'}, 'frozen' => {}, 'sok' => $v->{'sok'}, 'reach' => { %{ $v->{'reach'} } } };
    freeze_fixed($work);
    my $frozen = $work->{'frozen'};
    my %home   = map {$_ => 1} grep {!$frozen->{$_}} keys %Goal;
    foreach my $zone (@{ (regions({ 'box' => \%home, 'frozen' => $frozen }))[1] }) {
        my $left = pulled_off_freely(\%home, $frozen, { map {$_ => 1} @$zone });
        return 0 if !grep {!$v->{'box'}{$_} or $frozen->{$_}} keys %$left;
    }
    return 1;
}

# A diagonal run of enclosed empty cells (diagonal_voids) is a staircase of
# boxes and walls.  Walk down it: a box that is not on a goal, standing above
# or beside a step, spoils the run from there on -- unless a later step is a
# goal, which a box may yet be meant for.  A run spoilt at its end is dead; so
# is a clean run that ends in a box off its goal with no goal among its steps.
#
# was: is_diag_deadlock (Festival.pm:1004) over diag_deadlock (983), which is
# transcribed step for step -- it is a small state machine and reads like one
sub dead_on_a_diagonal ($v) {
    my $box   = $v->{'box'};
    my $plain = sub ($p) {$box->{$p} and !$Goal{$p}};
RUN: foreach my $run (@{ diagonal_voids({ %$v, 'frozen' => {} }) }) {
        my ($cells, $diag) = @$run;

        # the run goes down and to the right (3) or down and to the left (5);
        # "beside" a step is the side the run came from.  The last step is the
        # cell the run ends against, which may be a wall -- so by arithmetic
        my $beside = $diag == 3 ? -1 : 1;
        my @steps  = (@$cells, $N8{ $cells->[-1] }[$diag]);
        my $good   = $plain->($steps[0] - $Width + $beside) ? 0 : 1;
        foreach my $i (0 .. $#steps) {
            my $p = $steps[$i];
            if (!$good or $plain->($p - $Width) or $plain->($p + $beside)) {
                return 1 if $i == $#steps;
                $good = $Goal{$p} ? 1 : 0;
                next;
            }
            last     if $i == $#steps;
            next RUN if $Goal{$p};
        }
        return 1 if $plain->($steps[-1]);
    } ## end RUN: foreach my $run (@{ diagonal_voids...})
    return 0;
} ## end sub dead_on_a_diagonal

# All of them, in the original's order -- these four and the ones that search
# (the sections that follow).  Returns the reason, '' for a position nothing
# could be said against.  $opt->{'no_matching'} leaves the matching test out:
# the dragonfly search does (was: check_matching_deadlock returning 0 in
# DRAGONFLY, Festival.pm:3468).
sub position_is_dead ($v, $pull, $opt = {}) {
    return 'unmatched' if !$opt->{'no_matching'} and unmatched($v, $pull);
    my $in_pieces = @{ (regions($v))[1] } != 1;
    if ($pull) {
        return 'cannot be pulled home' if cannot_be_pulled_home($v);
        return 'stuck pattern'         if in_stuck_pattern($v, 1);
        return 'shut in'               if $in_pieces and shut_in_when_pulling($v, $opt);
        return 'wobblers'              if wobblers_dead($v, $opt);
        return '';
    }
    return 'goals cannot be emptied' if goals_cannot_be_emptied($v);
    return 'stuck pattern'           if in_stuck_pattern($v, 0);
    return 'corral'                  if $in_pieces and corral_is_dead($v, $opt);
    return 'diagonal'                if dead_on_a_diagonal($v);
    return 'too few boxes there'     if too_few_boxes_there($v);
    return '';
} ## end sub position_is_dead

# The question as the tree asks it: of the macro it has just picked.  A macro
# that takes a box off the board is not asked.
#
# was: move_is_deadlocked (Festival.pm:7560)
sub picked_is_dead ($view, $m, $pull, $opt = {}) {
    return 0 if $m->{'isbase'} or $m->{'kill'};
    my $after = apply($view, $m);
    return 1 if position_is_dead($after, $pull, $opt);
    return room_is_dead($after, $m, $pull, $opt);
}

# ---------------------------------------------------------------------------
# Dead positions: the search over a deadlock zone
# ---------------------------------------------------------------------------
#
# Most dead positions are dead LOCALLY: a few boxes round a part of the floor
# the player cannot get into have locked each other up, and the rest of the
# board has nothing to do with it.  So the rest of the board is thrown away.
#
# THE ZONE is the part that is kept: the closed-off floor, the cells round it,
# and a box standing straight behind a box on its edge if it cannot step aside.
# Boxes outside the zone are taken off, which lets the player walk about
# freely out there.  Then a small search is run on what is left, with two rules
# of its own:
#
#   * a box that can be brought OUT of the zone is simply taken off the board
#     -- it has escaped, it is no longer part of the question -- and when some
#     box can escape, that is the only macro the position has;
#   * after every macro the zone is cut down to what is still closed off.
#
# The search ends ALIVE as soon as it sees a way out -- nothing left to do in
# the zone, the zone gone, the floor in one piece -- DEAD when every line of
# play has run into the sand, and UNKNOWN when it has opened as many positions
# as it was allowed (50).  Only DEAD kills the macro the tree asked about.
#
# Pulling, the zone is the other way round: it is where the player IS -- his
# region, the boxes round it, and enclosed single cells next to those -- and
# the question is whether he can pull his way out of it.
#
# The view of this search carries `zone`, and its `frozen` are the boxes that
# were walled in before the search began: they are walls all through it, and
# are NOT in `box`.
#
# What these searches find out is remembered for the whole solve (%Dead_cache),
# dead and alive positions alike.  An UNKNOWN is remembered too, with a count of
# how often it has been asked about since: at the 128th asking, the 256th, ...
# the search is run again, allowed that many positions.
#
# was: corral_deadlock (Festival.pm:7477) and everything under it
sub zone_key ($v) {
    return join '|', poskey($v), join(',', sort {$a <=> $b} keys %{ $v->{'zone'} // {} }),
        join(',', sort {$a <=> $b} keys %{ $v->{'frozen'} });
}

# The player's region grown into whatever room has been made for it.
#
# was: expand_sokoban_cloud (Festival.pm:365) called without a seed
sub grown_reach ($reach, $box, $frozen) {
    my %reach = %$reach;
    my @q     = keys %reach;
    my $bh    = 0;
    while ($bh < @q) {
        foreach my $nb (@{ $Cg{ $q[$bh++] } }) {
            next if $reach{$nb} or $box->{$nb} or $frozen->{$nb};
            $reach{$nb} = 1;
            push @q, $nb;
        }
    }
    return \%reach;
}

# The zone round a group of closed-off cells, pushing; $within, if given, is
# the zone so far, which the new one may not grow out of.
#
# was: update_deadlock_zone_from_group_push_mode (Festival.pm:1137)
sub push_zone ($v, $group, $within) {
    my ($box, $frozen) = @$v{ 'box', 'frozen' };
    my %zone;
    foreach my $p (@$group) {
        $zone{$p} = 1;
        $zone{$_} = 1 foreach grep {!$Wall{$_} and !$frozen->{$_}} @{ $N8{$p} };
        foreach my $d (0 .. 3) {
            my $near = $N{$p}[$d];
            next if !$box->{$near};
            my $far = $N{$near}[$d];
            $zone{$far} = 1 if $box->{$far} and !can_be_pushed_sideways($v, $far, $d);
        }
    }
    if ($within) {delete @zone{ grep {!$within->{$_}} keys %zone }}
    return \%zone;
} ## end sub push_zone

# ... and pulling: the player's region, the boxes round it, and every enclosed
# single cell that touches the zone, with the boxes round that.
#
# was: init_deadlock_zone_from_group (Festival.pm:1185), its pull half, with
# add_islands (1166)
sub pull_zone ($v) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    my %zone = %$reach;
    foreach my $p (keys %$reach) {
        $zone{$_} = 1 foreach grep {$box->{$_}} @{ $N8{$p} };
    }
    my %first = %zone;
    foreach my $p (keys %Floor) {
        next if $box->{$p} or $frozen->{$p} or $first{$p};
        next if !grep {$first{$_}} @{ $N{$p} };
        next if grep  {!($Wall{$_} or $frozen->{$_} or $box->{$_})} @{ $N{$p} };
        $zone{$p} = 1;
        $zone{$_} = 1 foreach grep {$box->{$_}} @{ $N8{$p} };
    }
    return \%zone;
} ## end sub pull_zone

# Take off the boxes outside the zone, and let the player into the room.
#
# was: clear_boxes_out_of_deadlock_zone (Festival.pm:1249)
sub keep_zone_boxes ($v) {
    my %box = map {$_ => 1} grep {$v->{'zone'}{$_}} keys %{ $v->{'box'} };
    return { %$v, 'box' => \%box, 'reach' => grown_reach($v->{'reach'}, \%box, $v->{'frozen'}) };
}

# Pushing: is anything left to do in the zone -- out of the player's reach, a
# box off its goal or a goal without its box?
#
# was: work_left_in_deadlock_zone (Festival.pm:1091)
sub work_left_in_zone ($v) {
    my ($box, $reach) = @$v{ 'box', 'reach' };
    return scalar grep {!$reach->{$_} and ($box->{$_} xor $Goal{$_})} keys %{ $v->{'zone'} };
}

# A macro of the zone search made: the box moved (or taken off), the zone
# brought up to date, the boxes that have fallen out of it taken off.
#
# was: apply_move (Festival.pm:3303) in DEADLOCK_SEARCH, with
# update_deadlock_zone (1266)
sub zone_play ($v, $m, $pull) {
    my ($frozen, $old) = @$v{ 'frozen', 'zone' };
    my %box = %{ $v->{'box'} };
    delete $box{ $m->{'from'} };
    my $after;
    if ($m->{'kill'}) {
        $after =
            { 'box' => \%box, 'frozen' => $frozen, 'sok' => $v->{'sok'}, 'reach' => grown_reach($v->{'reach'}, \%box, $frozen) };
    }
    else {
        $box{ $m->{'to'} } = 1;
        $after = set_reach({ 'box' => \%box, 'frozen' => $frozen, 'sok' => $m->{'man'} });
    }
    my $reach = $after->{'reach'};
    $after->{'zone'} =
        $pull
        ? pull_zone($after)
        : push_zone($after, [grep {!$box{$_} and !$frozen->{$_} and !$reach->{$_}} keys %$old], $old);
    return keep_zone_boxes($after);
} ## end sub zone_play

# The macros of a position of the zone search: the ordinary ones, no corral --
# unless some box can leave the zone, and then only that: the first such box
# (by cell) is taken off.
#
# was: find_possible_moves (Festival.pm:5746) in DEADLOCK_SEARCH, with
# check_for_deadlock_zone_moves (5720)
sub zone_moves ($v, $pull, $opt) {
    return moves_or_removal($v, $pull, $opt, sub ($m, $all, $in) {!$in->{'zone'}{ $m->{'to'} }});
}

# The search itself: 'dead', 'alive' or 'unknown'.
#
# Of all the macros not yet followed it follows the one that leaves the floor
# in the fewest pieces, then the fewest boxes, then the smallest zone.  UNKNOWN
# comes two ways: $max positions opened, or more than $max different positions
# in sight (opened or not).
#
# (The original counts the positions in sight through a table of 1024 hash
# buckets, so two that share a bucket count as one and it may go on a little
# longer than its own limit says.  Here they are counted.  The gate allows for
# exactly that: the model may say UNKNOWN where the original reached a verdict,
# never the other way round, and never a different verdict.)
#
# was: corral_deadlock_search_actual (Festival.pm:7376) with
# son_can_break_free (5899), choose_deadlock_son (5881),
# mark_deadlocked_sons_using_cache (5920), insert_positions_to_deadlock_cache
# (5834)
sub zone_search ($start, $pull, $max, $opt) {
    return 'alive' if !$pull and !work_left_in_zone($start);
    my $known = sub ($key) {($Dead_cache{"$key/$pull"} // [''])->[0]};
    my $opened;
    my $result = small_search(
        {
            'start'               => $start,
            'start_is_a_position' => 1,
            'max'                 => $max,
            'play'                => sub ($v, $m) {zone_play($v, $m, $pull)},
            'key'                 => \&zone_key,
            'moves'               => sub ($v) {zone_moves($v, $pull, $opt)},
            'solved'              => sub ($v) {0},
            'finished'            => sub ($v) {!$pull and !work_left_in_zone($v)},
            'better'              => sub ($son, $best) {
                return $son->{'regions'} < $best->{'regions'} if $son->{'regions'} != $best->{'regions'};
                return $son->{'boxes'} < $best->{'boxes'}     if $son->{'boxes'} != $best->{'boxes'};
                return $son->{'zone'} < $best->{'zone'};
            },
            'look' => sub ($open) {
                $opened = $open;
                my %in_sight = map {$_->{'key'} => 1} map {@{ $_->{'sons'} }} @$open;
                return 'unknown' if keys %in_sight > $max;

                # a way out of the newest position?
                my $last = $open->[-1];
                return 'alive' if !$pull and !work_left_in_zone($last->{'view'});
                foreach my $son (grep {!$_->{'dead'}} @{ $last->{'sons'} }) {

                    # (the floor in one piece: pushing it says nothing new -- a
                    # player who can get everywhere leaves no closed-off cell and so
                    # no zone -- but pulling it is the plain case of not being shut in)
                    return 'alive' if !$son->{'zone'} or $son->{'regions'} == 1 or $known->($son->{'key'}) eq 'alive';
                    next           if !$pull;
                    my $after = $son->{'after'};
                    return 'alive' if grep {!$last->{'view'}{'zone'}{$_}} keys %{ $after->{'zone'} };    # the zone has grown
                    return 'alive' if grep {!$after->{'zone'}{$_}} keys %{ $after->{'reach'} };          # he is out of it
                }

                # what is known to be dead need not be tried
                my %is_open = map {$_->{'key'} => 1} @$open;
                foreach my $key (grep {!$is_open{$_} and $known->($_) eq 'dead'} map {$_->{'key'}} @{ $last->{'sons'} }) {
                    $_->{'dead'} = 1 foreach grep {$_->{'key'} eq $key} map {@{ $_->{'sons'} }} grep {!$_->{'dead'}} @$open;
                }
                return '';
            },
        }
    );
    $result = 'alive' if $result eq 'solved';
    foreach my $pos (grep {$_->{'dead'} or $result eq 'dead'} @$opened) {
        remember_verdict("$pos->{'key'}/$pull", 'dead');
    }
    if ($result eq 'alive') {
        for (my $pos = $opened->[-1]; $pos; $pos = $pos->{'father'}) {remember_verdict("$pos->{'key'}/$pull", 'alive')}
    }
    return $result;
} ## end sub zone_search

# was: insert_to_deadlock_cache (Festival.pm:492)
sub remember_verdict ($key, $verdict) {
    my $e = $Dead_cache{$key};
    if (!$e) {$Dead_cache{$key} = [$verdict, 0]; return}
    Carp::confess("the searches disagree about $key: $e->[0], now $verdict")
        if $e->[0] ne 'unknown'
        and $verdict ne 'unknown'
        and $e->[0] ne $verdict;
    $e->[0] = $verdict if $e->[0] eq 'unknown';
    return;
}

# The search, through what is remembered.
#
# was: advanced_deadlock_search (Festival.pm:7439) with should_reevaluate (5933)
sub zone_verdict ($start, $pull, $opt) {
    my $key = zone_key($start) . "/$pull";
    my $e   = $Dead_cache{$key};
    if ($e) {
        my $asked = ++$e->[1];
        if ($e->[0] eq 'unknown' and $asked >= 100 and !($asked & ($asked - 1))) {
            my $again = zone_search($start, $pull, $asked, $opt);
            remember_verdict($key, $again) if $again ne 'unknown';
            return $again;
        }
        return $e->[0];
    }
    my $verdict = zone_search($start, $pull, 50, $opt);
    remember_verdict($key, $verdict);
    return $verdict;
} ## end sub zone_verdict

# A last resort for a zone with five boxes or fewer that keeps coming back: at
# the HUNDREDTH time of asking -- not before, and not again -- try outright
# whether its boxes can all be brought home.
#
# was: mini_corral (Festival.pm:7412)
sub few_boxes_verdict ($v) {
    return 'alive' if keys %{ $v->{'box'} } > 5;
    my $key = zone_key($v) . '/few';
    my $e   = $Dead_cache{$key};
    if (!$e) {$Dead_cache{$key} = ['unknown', 0]; return 'unknown'}
    return $e->[0]   if $e->[0] ne 'unknown';
    return 'unknown' if ++$e->[1] != 100;
    my $packed = (grep {!$Goal{$_}} keys %{ $v->{'box'} }) ? can_be_packed($v, 1000) : 1;
    return $e->[0] = $packed == 0 ? 'dead' : 'alive';
}

# The position with what can never move again turned into walls for good:
# those boxes leave `box` and stay in `frozen`.
sub walled_in ($v) {
    my $work = { 'box' => $v->{'box'}, 'frozen' => {}, 'sok' => $v->{'sok'}, 'reach' => { %{ $v->{'reach'} } } };
    freeze_fixed($work);
    my $frozen = $work->{'frozen'};
    return {
        'box'    => { map {$_ => 1} grep {!$frozen->{$_}} keys %{ $v->{'box'} } },
        'frozen' => $frozen,
        'sok'    => $v->{'sok'},
        'reach'  => $work->{'reach'},
    };
}

# The starting position of a zone search round these closed-off cells: the
# zone, the boxes outside it taken off -- and the walled-in boxes with no zone
# beside them as well: they are nobody's business, and the floor under them is
# floor again.
sub zone_round ($walled, $cells) {
    my $zoned = keep_zone_boxes({ %$walled, 'zone' => push_zone($walled, $cells, undef) });
    my %still = map {$_ => 1} grep {
        my $p = $_;
        grep {$zoned->{'zone'}{$_}} @{ $N8{$p} }
    } keys %{ $walled->{'frozen'} };
    return { %$zoned, 'frozen' => \%still, 'reach' => grown_reach($zoned->{'reach'}, $zoned->{'box'}, \%still) };
}

# Pushing.  Freeze what can never move again; then every closed-off region by
# itself, and every two of them that one box stands between, is made a zone and
# searched.  One dead zone is enough.
#
# was: corral_deadlock (Festival.pm:7477), its push half, with
# keep_two_components (5859) and clear_frozen_boxes_away_from_deadlock_zone
# (1228)
sub corral_is_dead ($v, $opt = {}) {
    return 0 if !grep {!$Goal{$_}} keys %{ $v->{'box'} };
    my $walled = walled_in($v);
    my ($region, $cells_of) = regions($walled);
    return 0 if !%{ $walled->{'reach'} };
    my $mine = $region->{ min(keys %{ $walled->{'reach'} }) };
    my (%checked, %gave_up);
    my $dead = sub (@regions) {
        my $zoned   = zone_round($walled, [map {@{ $cells_of->[$_] }} @regions]);
        my $verdict = zone_verdict($zoned, 0, $opt);
        return (1,                                           $verdict) if $verdict eq 'dead';
        return (few_boxes_verdict($zoned) eq 'dead' ? 1 : 0, $verdict);
    };
    foreach my $r (grep {$_ != $mine} 0 .. $#$cells_of) {
        $checked{"$r,$r"} = 1;
        my ($is, $verdict) = $dead->($r);
        return 1         if $is;
        $gave_up{$r} = 1 if $verdict eq 'unknown';
    }
    foreach my $p (sort {$a <=> $b} keys %{ $walled->{'box'} }) {
        my @round = grep {defined} map {$region->{$_}} @{ $N{$p} };
        foreach my $k1 (0 .. $#round) {
            foreach my $k2 ($k1 .. $#round) {
                my ($r1, $r2) = @round[$k1, $k2];
                next if $r1 == $mine or $r2 == $mine or $checked{"$r1,$r2"} or $gave_up{$r1} or $gave_up{$r2};
                $checked{"$r1,$r2"} = $checked{"$r2,$r1"} = 1;
                return 1 if ($dead->($r1, $r2))[0];
            }
        }
    }
    return 0;
} ## end sub corral_is_dead

# Pulling.  The zone is the player's own region; if the search finds him shut
# in there for good, the position is dead -- provided there is still something
# to do OUTSIDE the zone, a box that is not on a starting cell or a starting
# cell without its box.
#
# was: advanced_deadlock_pull_mode (Festival.pm:7457) with
# work_left_outside_deadlock_zone (1102)
sub shut_in_when_pulling ($v, $opt = {}) {
    my $box = $v->{'box'};
    return 0 if $v->{'reach'}{$Sok0} and !grep {!$Start{$_}} keys %$box;
    return 0 if @{ (regions($v))[1] } == 1;
    my $zoned = { 'box' => $box, 'frozen' => {}, 'sok' => $v->{'sok'}, 'reach' => $v->{'reach'} };
    my $zone  = $zoned->{'zone'} = pull_zone($zoned);
    my $kept  = keep_zone_boxes($zoned);
    return 0 if keys %{ $kept->{'box'} } == keys %Start;
    return 0 if zone_verdict($kept, 1, $opt) ne 'dead';
    return scalar grep {!$zone->{$_} and ($box->{$_} xor $Start{$_})} keys %Floor;
}

# ---------------------------------------------------------------------------
# Dead positions: searches in which a box is let go
# ---------------------------------------------------------------------------
#
# The zone search is one of a family.  They all ask "can these few boxes ever
# be got out of the way?", and they all answer it the same way: play on, and
# the moment a box has plainly GOT AWAY -- by that search's own idea of getting
# away -- take it off the board; when that can be done it is the only macro the
# position has.  If the boxes that remain all end up at home, the position is
# alive.  What differs is only what "got away" means:
#
#   zone       the box can be brought out of the zone              (above)
#   wobblers   its macro can be undone, or carries it two rows AND two columns
#   rooms      it can be brought into another room
#
# `moves_or_removal` is that rule, `removal_search` the search for the plain
# members of the family (the zone search has more to it and is written out).
# The macros of a position, no corral -- or, if $gets_away says so of any of
# them, that one macro alone, as a taking off: the first, by box and cell.
#
# was: detect_kill_moves (Festival.pm:5731) and the `last` after it in
# find_possible_moves (5790)
sub moves_or_removal ($v, $pull, $opt, $gets_away) {
    my @moves = in_original_order(@{ (possible_moves($v, $pull, { %$opt, 'corral' => 0 }))[0] });
    my ($out) = grep {$gets_away->($_, \@moves, $v)} @moves;
    return $out ? [{ %$out, 'kill' => 1 }] : \@moves;
}

# 'dead', 'alive' or 'unknown' ($max positions opened, or more than that in
# sight).  Alive = every box left is at home: on a goal, or pulling on a
# starting cell.  Of the macros not yet followed the one that leaves fewest
# boxes is taken, then the floor in fewest pieces, then most boxes at home.
#
# was: wobblers_search_actual (Festival.pm:7196) and
# rooms_deadlock_search_actual (7009), which are one loop written twice, with
# get_best_wobblers_move (4551) and get_best_rooms_deadlock_move (4190), which
# are one comparison written twice
#
# $sight is the cap on the positions in sight, $max unless said otherwise.
# (The original counts them through 1024 hash buckets, so two that share a
# bucket count once and its limits are softer than they say: its "500" lets
# some 680 positions through and its "1000" some 3800.  The callers that had
# those limits say the real numbers.)
sub removal_search ($start, $pull, $max, $opt, $gets_away, $sight = $max) {
    my $home     = $pull ? \%Start    : \%Goal;
    my $at_home  = $pull ? 'unpacked' : 'packed';
    my $all_home = sub ($v) {!grep {!$home->{$_}} keys %{ $v->{'box'} }};
    return 'alive' if $all_home->($start);
    my $result = small_search(
        {
            'start'               => $start,
            'start_is_a_position' => 1,
            'max'                 => $max,
            'moves'               => sub ($v) {moves_or_removal($v, $pull, $opt, $gets_away)},
            'solved'              => $all_home,
            'finished'            => sub ($v) {$all_home->($v) and (!$pull or $v->{'reach'}{$Sok0})},
            'better'              => sub ($son, $best) {
                return $son->{'boxes'} < $best->{'boxes'}     if $son->{'boxes'} != $best->{'boxes'};
                return $son->{'regions'} < $best->{'regions'} if $son->{'regions'} != $best->{'regions'};
                return $son->{$at_home} > $best->{$at_home};
            },
            'look' => sub ($open) {
                my %in_sight = map {$_->{'key'} => 1} map {@{ $_->{'sons'} }} @$open;
                return keys %in_sight > $sight ? 'unknown' : '';
            },
        }
    );
    return $result eq 'solved' ? 'alive' : $result;
} ## end sub removal_search

# Such a search, asked once per position and solve: whatever it said is said
# again, UNKNOWN included.
sub removal_verdict ($name, $start, $pull, $max, $opt, $gets_away, $sight = $max) {
    my $key = poskey($start) . "/$name/$pull";
    return ($Dead_cache{$key} //= [removal_search($start, $pull, $max, $opt, $gets_away, $sight), 0])->[0];
}

# ---- wobblers (pulling only)
#
# A WOBBLER is a box whose pull can be taken back at once: pulled one cell, the
# player can walk round to where it stood.  Such a box hinders nobody for long,
# so it is left out -- and so is a box the player cannot touch at all, and one
# he can pull that has a free side he cannot get to.  If what then remains
# cannot be got home even with wobbling and far-travelling boxes taken off as
# they turn up, the position is dead.
#
# The first sweep (the boxes out of touch) goes through the boxes once, in
# order, and each removal is seen by the boxes after it; the second goes round
# until nothing more wobbles.  Both are the original's, order and all.
#
# was: is_wobblers_deadlock (Festival.pm:7244) with
# remove_boxes_with_no_player_access (4466), remove_wobblers (4517),
# pull_is_reversible (4502), push_is_reversible (4488),
# reduce_moves_in_wobblers_search (4441)
sub without_boxes_out_of_touch ($v) {
    my %box   = %{ $v->{'box'} };
    my $reach = $v->{'reach'};
    foreach my $p (sort {$a <=> $b} keys %box) {
        my @round = @{ $N{$p} };
        if (!grep {$reach->{$_}} @round) {
            delete $box{$p};
            next;
        }
        next if !grep {!$Wall{$_} and !$box{$_} and !$reach->{$_}} @round;
        my $cp = $Cp{$p} // {};
        delete $box{$p} if grep {$reach->{$_} and $reach->{ $cp->{$_} }} keys %$cp;
    }
    return { 'box' => \%box, 'frozen' => {}, 'sok' => $v->{'sok'}, 'reach' => grown_reach($reach, \%box, {}) };
} ## end sub without_boxes_out_of_touch

# Can the single push (or pull) of the box on p in direction d be undone?
sub step_can_be_undone ($box, $reach, $p, $d, $pull) {

    # the step and the step that takes it back both have to be steps the map
    # has.  Pushing he stands behind the box and needs two free cells ahead of
    # it; pulling he stands ahead of it, needs the cell beyond himself to step
    # back onto -- and the cell behind the box free, to pull it back from
    my ($to, $behind) = ($N{$p}[$d], $N{$p}[$d ^ 2]);
    my $map = $pull ? \%Cp : \%Cm;
    return 0 if !defined(($map->{$p} // {})->{$to}) or !defined(($map->{$to} // {})->{$p});
    return 0 if !$reach->{ $pull ? $to : $behind };
    return 0 if $box->{$to};
    return 0 if $pull and $box->{$behind};
    my $beyond = $N{$to}[$d];
    return 0 if $box->{$beyond};
    my %moved = %$box;
    delete $moved{$p};
    $moved{$to} = 1;
    my $after = set_reach({ 'box' => \%moved, 'frozen' => {}, 'sok' => $pull ? $beyond : $p });
    return $after->{'reach'}{ $pull ? $p : $beyond } ? 1 : 0;
} ## end sub step_can_be_undone

sub without_wobblers ($v, $pull) {
    my %box   = %{ $v->{'box'} };
    my $reach = { %{ $v->{'reach'} } };
    my $again = 1;
    while ($again) {
        $again = 0;
        foreach my $p (sort {$a <=> $b} keys %box) {
            next if !grep {step_can_be_undone(\%box, $reach, $p, $_, $pull)} 0 .. 3;
            delete $box{$p};
            $reach->{$p} = 1;
            $again = 1;
        }
        $reach = grown_reach($reach, \%box, {}) if $again;
    }
    return { 'box' => \%box, 'frozen' => {}, 'sok' => $v->{'sok'}, 'reach' => $reach };
} ## end sub without_wobblers

# what "got away" means in the wobblers search
sub wobbles_or_travels ($m, $all, $in) {
    return 1 if $m->{'reversible'};
    my ($from, $to) = @$m{ 'from', 'to' };
    return (abs(int($from / $Width) - int($to / $Width)) >= 2 and abs($from % $Width - $to % $Width) >= 2) ? 1 : 0;
}

sub wobblers_dead ($v, $opt = {}) {
    my $bare = without_wobblers(without_boxes_out_of_touch($v), 1);
    my $left = keys %{ $bare->{'box'} };
    return 0 if !$left or $left == keys %Start;
    return removal_verdict('wobblers', $bare, 1, 50, $opt, \&wobbles_or_travels) eq 'dead' ? 1 : 0;
}

# A backward search starts once for every region the solved level leaves the
# player; a region from which the boxes cannot be got off the goals and home,
# even this generously, is not started from at all.
#
# was: start_zone_is_deadlocked (Festival.pm:7229)
sub start_is_dead ($root, $opt = {}) {
    my $bare = { 'box' => $root->{'box'}, 'frozen' => {}, 'sok' => $root->{'sok'}, 'reach' => $root->{'reach'} };
    return removal_search($bare, 1, 1000, $opt, \&wobbles_or_travels, 3800) eq 'dead' ? 1 : 0;
}

# ---- rooms (either direction)
#
# The box has just been brought into a small room -- the room with the mouths
# of its corridors, under 25 cells -- that now holds two to five boxes (five
# only if it has 17 cells or fewer, four only if 20).  Keep the boxes of that
# room and nothing else: if they cannot all be got home, a box that can be
# brought into ANOTHER room being let go, the position is dead.
#
# was: is_rooms_deadlock (Festival.pm:7055) with keep_boxes_in_room (4208) and
# reduce_moves_in_rooms_deadlock_search (4159)
sub room_is_dead ($after, $m, $pull, $opt = {}) {
    return 0 if $m->{'isbase'} or $m->{'kill'} or @Room_area <= 1;
    my $box = $after->{'box'};
    foreach my $t (grep {$Room_area[$_]{ $m->{'to'} }} 0 .. $#Room_area) {
        my $area = $Room_area[$t];
        my $size = keys %$area;
        next if $size >= 25;
        my %kept = map {$_ => 1} grep {$area->{$_}} keys %$box;
        my $n    = keys %kept;
        next if $n <= 1 or $n > 5 or ($n == 5 and $size > 17) or ($n == 4 and $size > 20);
        my $alone =
            { 'box' => \%kept, 'frozen' => {}, 'sok' => $after->{'sok'}, 'reach' => grown_reach($after->{'reach'}, \%kept, {}) };
        my $verdict = removal_verdict('rooms', $alone, $pull, 200, $opt,
            sub ($move, $all, $in) {defined $Room{ $move->{'to'} } and $Room{ $move->{'to'} } != $t});
        return 1 if $verdict eq 'dead';
    }
    return 0;
} ## end sub room_is_dead

# ---- the boxes that must already be there (pushing only)
#
# The question is put to the WALLS, not to the position: the level's own walls,
# plus the boxes frozen where they stand, plus every goal hole.  Given those
# walls, imagine the level solved -- a box on every goal that is not walled
# over -- and pull back from there, from every region the player could be in,
# letting a box go as soon as it has been pulled FIVE STEPS' WALK away and the
# player can get back to where it stood.  If that search runs dry without
# emptying the board (and within 600 positions), it has seen every
# arrangement the last few boxes can be in, and two things can be read off:
#
#   * a box that stands on its goal in EVERY one of them can never be brought
#     there late -- it must be there already;
#   * round every cell, the FEWEST boxes seen there in any of them (on the
#     cell and its four neighbours; on it and all eight) -- the position must
#     have at least as many.
#
# A position that fails either is dead.  The answer is kept per set of walls
# (up to 500 of them).  If the search hits 600 positions it is run once more
# with three steps' walk instead of five, and whatever that gives is kept.
#
# was: is_k_dist_deadlock (Festival.pm:6968), check_deadlock_using_k_dist_cache
# (6934), get_k_dist_forced_boxes (6874), check_for_k_dist_moves (4103),
# count_adjacent_boxes (4087), has_pull_continuation's K_DIST branch (3982)
# A move made on a board whose frozen cells stay walls; a taking off included.
sub apply_within_walls ($v, $m) {
    my %box = %{ $v->{'box'} };
    delete $box{ $m->{'from'} };
    if ($m->{'kill'}) {
        return {
            'box'    => \%box,
            'frozen' => $v->{'frozen'},
            'sok'    => $v->{'sok'},
            'reach'  => grown_reach($v->{'reach'}, \%box, $v->{'frozen'})
        };
    }
    $box{ $m->{'to'} } = 1;
    return set_reach({ 'box' => \%box, 'frozen' => $v->{'frozen'}, 'sok' => $m->{'man'} });
}

# In that search a pull leaves something to go on with if the player has any
# room at all -- more than the one cell he stands on -- or stands against one
# of the walls that are not the level's own.
sub can_go_on_pulling_far ($v) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    return 1 if $reach->{$Sok0} and !grep {!$Start{$_}} keys %$box;
    return 1 if keys %$reach > 1;
    return scalar grep {$frozen->{$_}} map {@{ $N{$_} }} keys %$reach;
}

# {cell => how many boxes stand on it or next to it}, by four and by eight
sub boxes_about ($box) {
    my (%by4, %by8);
    foreach my $p (keys %$box) {
        $by4{$p}++;
        $by8{$p}++;
        foreach my $k (0 .. 7) {
            my $q = $N8{$p}[$k];
            $by8{$q}++;
            $by4{$q}++ if !($k & 1);
        }
    }
    return (\%by4, \%by8);
}

# What the pull-back search says about these walls: {must => {cell}, by4 =>
# {cell => least}, by8 => {cell => least}}, all empty when it says nothing.
# Second value: whether it was cut short at 600 positions.
sub boxes_that_must_be_there ($walls, $steps) {
    my %home  = map {$_ => 1} grep {!$walls->{$_}} keys %Goal;
    my @roots = map {set_reach({ 'box' => {%home}, 'frozen' => $walls, 'sok' => $_->[0] })}
        @{ (regions({ 'box' => \%home, 'frozen' => $walls }))[1] };
    my $nothing = { 'must' => {}, 'by4' => {}, 'by8' => {} };
    return ($nothing, 0) if !@roots;
    my $opened;
    my $opt    = { 'inefficient' => 0, 'far_pulls' => 1 };
    my $result = small_search(
        {
            'starts' => \@roots,
            'max'    => 600,
            'play'   => \&apply_within_walls,
            'key'    => \&zone_key,
            'moves'  => sub ($v) {
                moves_or_removal(
                    $v, 1, $opt,
                    sub ($m, $all, $in) {
                        ($Walk{ $m->{'to'} }{ $m->{'from'} } // 1000000) >= $steps
                            and apply_within_walls($in, $m)->{'reach'}{ $m->{'from'} };
                    }
                );
            },
            'solved'   => sub ($v) {!%{ $v->{'box'} }},
            'finished' => sub ($v) {$v->{'reach'}{$Sok0} and !grep {!$Start{$_}} keys %{ $v->{'box'} }},
            'better'   => sub ($son, $best) {
                return $son->{'boxes'} < $best->{'boxes'} if $son->{'boxes'} != $best->{'boxes'};
                return $son->{'regions'} < $best->{'regions'};
            },
            'look' => sub ($open) {$opened = $open; ''},
        }
    );
    return ($nothing, @$opened >= 600 ? 1 : 0) if $result ne 'dead';
    my (%must, %by4, %by8);
    foreach my $i (0 .. $#$opened) {
        my $box = $opened->[$i]{'view'}{'box'};
        my ($four, $eight) = boxes_about($box);
        if (!$i) {%must = %$box; %by4 = %$four; %by8 = %$eight; next}
        delete @must{ grep {!$box->{$_}} keys %must };
        foreach my $pair ([\%by4, $four], [\%by8, $eight]) {
            my ($least, $here) = @$pair;
            foreach my $p (keys %$least) {
                my $n = $here->{$p} // 0;
                if    (!$n)               {delete $least->{$p}}
                elsif ($n < $least->{$p}) {$least->{$p} = $n}
            }
        }
    }
    return ({ 'must' => \%must, 'by4' => \%by4, 'by8' => \%by8 }, 0);
} ## end sub boxes_that_must_be_there

sub too_few_boxes_there ($v) {
    return 0 if !grep {!$Goal{$_}} keys %{ $v->{'box'} };
    my $walled = walled_in($v);
    my %walls  = (%{ $walled->{'frozen'} }, map {$_ => 1} keys %Goal_hole);
    my $key    = join ',', sort {$a <=> $b} keys %walls;
    if (!$Far_pulls{$key}) {

        # (the 500 are the original's; it ran the search for a 501st set of
        # walls all the same and threw the answer away)
        return 0 if keys %Far_pulls >= 500;
        my ($said, $cut_short) = boxes_that_must_be_there(\%walls, 5);
        ($said) = boxes_that_must_be_there(\%walls, 3) if $cut_short;
        $Far_pulls{$key} = $said;
    }
    my $said = $Far_pulls{$key};
    return 1 if grep {!$v->{'box'}{$_}} keys %{ $said->{'must'} };
    my %free = map {$_ => 1} grep {!$walls{$_}} keys %{ $v->{'box'} };
    my ($by4, $by8) = boxes_about(\%free);
    return 1 if grep {($by4->{$_} // 0) < $said->{'by4'}{$_}} keys %{ $said->{'by4'} };
    return 1 if grep {($by8->{$_} // 0) < $said->{'by8'}{$_}} keys %{ $said->{'by8'} };
    return 0;
} ## end sub too_few_boxes_there

# ---- what a search learns as it goes: stuck patterns
#
# When a position of the big tree has had 64 positions opened under it (128
# pulling) and the search is still in there, something about it may be dead
# that none of the tests above can see.  So it is looked at once more, slowly:
# take off the wobblers (pushing) and every box that can be moved both ALONG A
# ROW AND ALONG A COLUMN with the player able to get back to where it stood --
# a box that free is nobody's prisoner -- and if two to twelve boxes are left,
# search them the same generous way (500 positions).  If they are dead, boil
# them down: drop every box without which they are dead still.  What remains,
# with the player's region, is a STUCK PATTERN, kept for the rest of the solve:
# any position that has those boxes, the player in that region, is dead.
#
# was: learn_from_subtrees (Festival.pm:7364), slow_xy_deadlock (7344),
# clear_xy_boxes (5809), reduce_moves_in_xy_search (4594) with mark_hv_indices
# (4569), xy_deadlock_search (7297), distill_pattern (7308), add_stuck_pattern
# (5693), is_in_stuck_patterns (5676)
# what "got away" means here: some macro of the box changes its row and some
# macro its column, counting only macros after which the player can walk to
# the cell the box came from.  It looks at all the macros of the position at
# once, so it is worked out once per list and remembered while that list is
# being asked about.
sub moves_both_ways () {
    my ($for, %free) = ('');
    return sub ($m, $all, $v) {
        my $key = poskey($v);    # (not the list's address: a freed list's address comes round again)
        if ($for ne $key) {
            ($for, %free) = ($key);
            my (%rows, %columns);
            foreach my $move (@$all) {
                my ($from, $to) = @$move{ 'from', 'to' };
                next if !apply($v, $move)->{'reach'}{$from};
                $rows{$from}    = 1 if int($to / $Width) != int($from / $Width);
                $columns{$from} = 1 if $to % $Width != $from % $Width;
            }
            $free{$_} = 1 foreach grep {$columns{$_}} keys %rows;
        }
        return $free{ $m->{'from'} };
    }; ## end sub
} ## end sub moves_both_ways

sub xy_verdict ($v, $pull, $opt = {}) {
    return removal_verdict('xy', $v, $pull, 500, $opt, moves_both_ways(), 680);
}

# Take off, one after another, every box that is free both ways.
sub without_free_boxes ($v, $pull, $opt = {}) {
    while (1) {
        my $moves = moves_or_removal($v, $pull, $opt, moves_both_ways());
        return $v if !@$moves or !$moves->[0]{'kill'};
        $v = apply($v, $moves->[0]);
    }
}

# Look at a position slowly; if it turns out dead, remember why.
sub learn_stuck_pattern ($view, $pull, $opt = {}) {
    my $v = { 'box' => $view->{'box'}, 'frozen' => {}, 'sok' => $view->{'sok'}, 'reach' => $view->{'reach'} };
    return if in_stuck_pattern($v, $pull);
    $v = without_wobblers($v, 0) if !$pull;
    $v = without_free_boxes($v, $pull, $opt);
    my $n = keys %{ $v->{'box'} };
    return if !$n or $n > 12 or $n == keys %Start;
    return if xy_verdict($v, $pull, $opt) ne 'dead';

    # boil it down: by cell, and from the top again after every box dropped
    my $home = $pull ? \%Start : \%Goal;
DROP: while (1) {
        foreach my $p (sort {$a <=> $b} keys %{ $v->{'box'} }) {
            my %less = %{ $v->{'box'} };
            delete $less{$p};
            next if !grep {!$home->{$_}} keys %less;
            my $without =
                { 'box' => \%less, 'frozen' => {}, 'sok' => $v->{'sok'}, 'reach' => grown_reach($v->{'reach'}, \%less, {}) };
            next if xy_verdict($without, $pull, $opt) ne 'dead';
            $v = $without;
            next DROP;
        }
        last;
    }
    push @Stuck, { 'box' => { %{ $v->{'box'} } }, 'reach' => { %{ $v->{'reach'} } }, 'pull' => $pull }
        if !in_stuck_pattern($v, $pull);
    return;
} ## end sub learn_stuck_pattern

sub in_stuck_pattern ($v, $pull) {
    my $box = $v->{'box'};
    my $man = min(keys %{ $v->{'reach'} }) // return 0;
    foreach my $stuck (grep {$_->{'pull'} == $pull} @Stuck) {
        next     if grep {!$box->{$_}} keys %{ $stuck->{'box'} };
        return 1 if $stuck->{'reach'}{$man};
    }
    return 0;
}

# ---------------------------------------------------------------------------
# The big tree
# ---------------------------------------------------------------------------
#
# Everything above works on one position.  This is the search that strings
# positions together, and it is ONE search for all of Festival: the forward
# search and the backward (packing) search, in every mode, are this loop with
# different answers to five questions.  What a mode is, is its answers.
#
#   moves    which macros a position has           (possible_moves, and how)
#   score    the numbers a position is judged by   (a hash of them)
#   better   which of two scores is the better one
#   cell     which CELL a score files a position under
#   advise   which of a position's macros come recommended
#
# THE TREE.  A node is a position that has been SEEN -- it has a key and a
# score and nothing else.  An expansion is a node that has been OPENED: it
# keeps the view, its macros (`sons`, each pointing at the node it leads to),
# its father, and its weight.
#
# THE WEIGHT of an expansion is the number of macros on the way to it that
# nobody recommended: a recommended macro costs 0, any other costs 1.  So "the
# lightest" means "reached mostly by doing what the advisors said".
#
# THE CELLS.  An expansion is filed under the cell of the best score met on
# the way to it (`best_past`), not under its own -- so a line of play that has
# once got somewhere stays filed where it got to, even while it wanders.  In
# each cell the expansions wait in a queue, lightest first, equal weights by
# the score their best untried macro leads to.  What is picked from a cell is
# that macro: the best untried one of the expansion at the head of the queue.
#
# THE TURNS.  Cells take turns.  On odd turns it is the next cell round the
# ring (and a cell that has just been created jumps the ring: it is next); on
# even turns it is the cell of the best line of play found so far.  That is
# the whole policy: every kind of position that has turned up keeps getting
# its share of the effort, and the most promising one gets half of all of it.
#
# was: FESS (Festival.pm:7780) and packing_search (7900s), which are this loop
# written out twice; set_root (7118), expand_node (7156),
# fill_expansion_structures (7078), set_weight_to_node_moves (4339),
# set_best_move (6211), best_move_in_tree (6260), add_label_to_last_node
# (6281), the request ring (582-720), update_best_so_far (6369),
# best_node_in_tree (6389), set_deadlock_status (4289),
# store_solution_in_helper (4398).  The original keeps the tree in eight flat
# arrays with packed moves and packed scores -- a measured saving of memory
# (2 237 -> 683 MB) that is NOT reproduced here; this version is for reading.
#
# WHAT A MODE HANGS ON THE LOOP besides its five answers: `dead`, asked of a
# macro at the moment it is picked (the expensive tests of a whole position,
# see "Dead positions": a yes kills the position it leads to); `refuse`, asked
# next (strikes out the macro only).  And `greedy`, ANOTHER WAY
# OF PICKING altogether, the GIRL mode's: {value => sub (score) -> number,
# epsilon => N}.  With it there are no cells and no turns until the slide
# begins: every position carries a VALUE -- its own score's value, or the best
# value under it once it has been opened -- and the pick walks down from a
# root, taking the best-valued macro at each step and, on every epsilon-th
# visit to a position, the macros in turn; the tree is kept a tree (a macro to
# a position known already is struck out), and the best line of play is
# judged by its own score.  Once the slide has begun the cells and the weights
# take over as in every other mode.  The loop itself learns two things from the shape of its tree: rings
# of positions that lead only to one another (the cycle check, below), and
# STUCK PATTERNS -- a position that has had 64 positions opened under it (128
# pulling) is looked at slowly, once (learn_stuck_pattern).
#
# Returns {result => 'solved' | 'timeout' | 'exhausted', line =>
# [expansions from the root to the solved one], best, met, tree => [every
# expansion], opened, seen, time}.
#
# THE PERIMETER is how a forward and a backward search meet.  It is a table
# both write into -- position => how many macros from its root, and which side
# wrote it -- for every position they open and every position its macros lead
# to.  The backward search starts from the SOLVED position, so an entry of its
# says "from here the level can be finished in that many macros".  The moment
# the forward search opens a position one of whose macros leads into the
# backward side's entries, the hunt is over and the SLIDE begins: that
# expansion is given a weight far below anything else (-2000 plus the depth),
# so it is picked at once, and from then on only such picks are made -- each
# one a step to an entry of smaller depth, down to depth 0, the solved
# position.  No path is stitched together: the forward search simply walks the
# backward tree home, checking every macro on the way with its own generator.
#
# $spec->{'perimeter'} is the shared table, $spec->{'pull'} says which side
# this search is.  `moves` is called with the state of the search as a second
# argument ({found => 1} once the slide has begun), because on the slide the
# forward generator has to offer everything the backward search may have done:
# no corral, and no "wasteful" positions thrown away.  The state says
# {loose => 1} from the start when a root is already in the other side's
# entries -- the other search got this far -- and the generator is to be as
# loose then, for the same reason.
sub feature_search ($spec) {
    my $started = Time::HiRes::time();
    my $better  = $spec->{'better'};
    my $mine    = $spec->{'pull'} ? 1 : 0;
    my $met     = $spec->{'perimeter'};
    my $state   = { 'found' => 0 };
    my (%node, @opened, %queue, @ring, %in_ring);
    my $turn_of = 0;    # whose turn it is, round the ring
    my $serial  = 0;    # positions seen so far

    # an entry of the pull side is never overwritten by the push side, and one
    # side keeps the smallest depth it has seen a position at
    my $note = sub ($key, $depth) {
        my $old = $met->{$key};
        return if $old and $old->[0] == 1     and $mine == 0;
        return if $old and $old->[0] == $mine and $old->[1] <= $depth;
        $met->{$key} = [$mine, $depth];
    };

    # THE SCORE of a node is kept PACKED: one string of doubles in a fixed
    # order of keys, the order of the first score this search computes (every
    # score of one search has the same keys).  score_of unpacks it; `better`
    # and `cell` are given unpacked copies.  (was: score_pack / score_hash,
    # Festival 0.16 -- 160 B against a hash of over a thousand)
    my @keys;
    my $packed = sub ($score) {
        @keys = sort keys %$score if !@keys;
        return pack 'd*', @$score{@keys};
    };

    # `meet`: the name a position goes by in the perimeter.  It is the key,
    # unless the search says otherwise -- the one with bases does: its keys
    # carry the bases, which the forward side knows nothing of, and once it has
    # taken a box off the board its positions are none the forward side could
    # ever be in (undef = do not write it down).
    my $node_of = sub ($view) {
        my $key = poskey($view);
        return $node{$key} //= {
            'key'    => $key,
            'serial' => $serial++,                                                   # the order the positions were first seen in
            'meet'   => $spec->{'meet_key'} ? $spec->{'meet_key'}->($view) : $key,
            'score'  => $packed->($spec->{'score'}->($view)),
            'keys'   => \@keys,
            'dead'   => 0,
            'opened' => undef,
        };
    };

    # THE MACROS of an expansion are four arrays side by side, one slot a
    # macro: the node it leads to (son_node), the macro packed into six bytes
    # (son_move -- what the tree needs of it: the box's cell, where it ends,
    # where the player ends, and whether it takes the box off), whether it
    # is struck out (son_dead) and its weight (son_weight).  Nothing else of
    # the macro is kept: the player's steps are worked out again from these
    # three cells when a solution is written down.  (was: the eight flat
    # arrays of the original's tree and its move_pack, Festival 0.14)
    my $live = sub ($e) {return set_reach({ %{ $e->{'view'} } })};    # the view with the player's region, flooded afresh

    # the best untried macro of an expansion: lightest first, then best score
    my $set_best = sub ($e) {
        $e->{'best'} = undef;
        return if $e->{'node'}{'dead'};
        my ($nodes, $dead, $weight) = @$e{ 'son_node', 'son_dead', 'son_weight' };
        foreach my $k (0 .. $#$nodes) {
            next if $dead->[$k] or $nodes->[$k]{'opened'};
            if ($nodes->[$k]{'dead'}) {$dead->[$k] = 1; next}
            my $best = $e->{'best'};
            $e->{'best'} = $k
                if !defined $best
                or $weight->[$k] < $weight->[$best]
                or ($weight->[$k] == $weight->[$best] and $better->(score_of($nodes->[$k]), score_of($nodes->[$best])));
        }
        return;
    }; ## end sub

    # a position is dead when it is not solved and all its macros are
    # (__SUB__, not a variable holding the sub: a closure that names itself
    # keeps itself alive, and with it the whole tree, after the search is over)
    my $settle = sub ($e) {
        return if $e->{'node'}{'dead'};
        return if $e->{'depth'} and $e->{'solved'};
        my ($nodes, $dead) = @$e{ 'son_node', 'son_dead' };
        foreach my $k (0 .. $#$nodes) {
            $dead->[$k] = 1 if $nodes->[$k]{'dead'};
        }
        return if grep {!$_} @$dead;
        $e->{'node'}{'dead'} = 1;
        __SUB__->($e->{'father'}) if $e->{'father'};
    };

    # the queue of one cell: a heap of expansions.  (By value an expansion
    # stays in its queue while its macros are used up under it, so an entry
    # may be left without a best macro: it sinks, and is looked at again when
    # it comes up.)
    my $ahead = sub ($e1, $e2) {
        my ($b1, $b2) = ($e1->{'best'}, $e2->{'best'});
        my ($w1, $w2) = (
            $e1->{'weight'} + (defined $b1 ? $e1->{'son_weight'}[$b1] : 1e9),
            $e2->{'weight'} + (defined $b2 ? $e2->{'son_weight'}[$b2] : 1e9)
        );
        return $w1 < $w2 if $w1 != $w2;
        if (defined $b1 and defined $b2) {
            my ($s1, $s2) = (score_of($e1->{'son_node'}[$b1]), score_of($e2->{'son_node'}[$b2]));
            return 1 if $better->($s1, $s2);
            return 0 if $better->($s2, $s1);
        }
        return $e1->{'index'} < $e2->{'index'};
    };
    my $enqueue = sub ($heap, $e) {
        my $i = push(@$heap, $e) - 1;
        while ($i > 0) {
            my $up = int(($i - 1) / 2);
            last if !$ahead->($heap->[$i], $heap->[$up]);
            @$heap[$i, $up] = @$heap[$up, $i];
            $i = $up;
        }
    };
    my $dequeue = sub ($heap) {
        return undef if !@$heap;
        my $top  = $heap->[0];
        my $last = pop @$heap;
        if (@$heap) {
            $heap->[0] = $last;
            my $i = 0;
            while (1) {
                my ($l, $r, $first) = (2 * $i + 1, 2 * $i + 2, $i);
                $first = $l if $l < @$heap and $ahead->($heap->[$l], $heap->[$first]);
                $first = $r if $r < @$heap and $ahead->($heap->[$r], $heap->[$first]);
                last if $first == $i;
                @$heap[$i, $first] = @$heap[$first, $i];
                $i = $first;
            }
        }
        return $top;
    }; ## end sub

    # open a node: its macros, their weights, its cell.  $view comes with the
    # player's region; what the expansion keeps of it is the boxes and the
    # player's cell (the region is flooded afresh when the position is picked
    # again, see $live).
    my $open = sub ($view, $father, $via) {
        my $before = scalar keys %node;    # positions known before this one was opened
        my $node   = $node_of->($view);
        my ($moves, $corral) = $spec->{'moves'}->($view, $state);

        # the macros in full, for as long as this position is being opened --
        # the advisors may look at the views they lead to; the tree keeps
        # only the four arrays
        my @sons = map {
            my $after = apply($view, $_);
            +{ 'move' => $_, 'after' => $after, 'node' => $node_of->($after), 'dead' => 0, 'weight' => 1 };
        } in_original_order(@$moves);

        # BY VALUE (see below) the tree stays a TREE: a macro to a position that
        # was known before this one was opened is struck out
        # (was: block_existing_sons_tree, Festival.pm:4327)
        if ($spec->{'greedy'}) {
            $_->{'dead'} = 1 foreach grep {$_->{'node'}{'serial'} < $before} @sons;
        }
        my $e = {
            'index'  => scalar @opened,
            'node'   => $node,
            'view'   => $view,            # in full while the advisors look; the boxes and the player's cell after
            'father' => $father,
            'via'    => $via,
            'depth'  => $father                    ? $father->{'depth'} + 1                 : 0,
            'weight' => $father                    ? $father->{'weight'} + $via->{'weight'} : 0,
            'corral' => $corral                    ? 1                                      : 0,
            'solved' => $spec->{'solved'}->($view) ? 1                                      : 0,
            'sons'   => \@sons,
        };

        # (a WEAK reference: the expansion points at its node too, and two
        # things that hold each other are never let go.  @opened is what keeps
        # the expansions alive, for as long as anybody holds the result.)
        $node->{'opened'} = $e;
        Scalar::Util::weaken($node->{'opened'});
        push @opened, $e;

        # the best score on the way here
        $e->{'best_past'} = $node;
        $e->{'best_past'} = $father->{'best_past'}
            if $father and !$better->(score_of($node), score_of($father->{'best_past'}));

        # recommended macros cost nothing; and where there are only one or two
        # macros to choose from, the first of them is as good as recommended
        # (the advisors may look at the views the macros lead to; nobody else
        # does, and a tree does not keep a view per macro)
        $sons[$_]{'weight'} = 0 foreach @{ $spec->{'advise'}->($e) };
        $sons[0]{'weight'} = 0 if @sons == 1 or @sons == 2;
        if (!$spec->{'weighted'}) {$_->{'weight'} = 0 foreach @sons}
        if ($state->{'found'})    {$_->{'weight'} = 1 foreach @sons}

        # ... and from here on the four arrays, and the view without its region
        delete $e->{'sons'};
        $e->{'view'} = {%$view};
        delete $e->{'view'}{'reach'};
        my $nodes  = $e->{'son_node'}   = [map {$_->{'node'}} @sons];
        my $dead   = $e->{'son_dead'}   = [map {$_->{'dead'}} @sons];
        my $weight = $e->{'son_weight'} = [map {$_->{'weight'}} @sons];
        $e->{'son_move'} = [map {move_pack($_->{'move'})} @sons];
        @sons = ();
        my $jump = 0;

        if ($met) {

            # does a macro of this position lead into the other side's tree?
            # On the slide, only deeper into it than this position already is.
            my $limit = $e->{'weight'} < 0 ? 2000 + $e->{'weight'} : 1e9;
            my $down;
            foreach
                my $k (grep {!$dead->[$_] and !$nodes->[$_]{'dead'} and !$nodes->[$_]{'opened'} and defined $nodes->[$_]{'meet'}}
                    0 .. $#$nodes)
            {
                my $entry = $met->{ $nodes->[$k]{'meet'} } or next;
                next                      if $entry->[0] == $mine or $entry->[1] >= $limit;
                $down = [$k, $entry->[1]] if !$down               or $entry->[1] < $down->[1];
            }
            if ($down) {
                $e->{'weight'}        = -2000 + $down->[1] + 1;
                $weight->[$down->[0]] = -1;
                $state->{'found'}     = 1;
                $jump                 = 1;
            }

            # and write this position down for the other side to find -- the
            # forward search only until it has found the way itself
            if (!$state->{'found'} or $mine) {
                $note->($node->{'meet'}, $e->{'depth'}) if defined $node->{'meet'};
                if (!$state->{'found'}) {
                    $note->($_->{'meet'}, $e->{'depth'} + 1) foreach grep {defined $_->{'meet'}} @$nodes;
                }
            }
        } ## end if ($met)

        # a macro of this position that leads to a position not opened yet
        # (what the cycle check follows, see below)
        ($e->{'leaf'}) = grep {!$nodes->[$_]{'dead'} and !$nodes->[$_]{'opened'}} 0 .. $#$nodes;

        # how many positions have been opened under each position on the way
        # here -- not counted for a position dead on arrival, that is, one
        # every macro of which leads to a dead position.  Counted BEFORE the
        # position is settled: a position the tree rule (by value) has left
        # without a macro is settled dead, its ancestors with it, and yet it
        # counts, and so do they, as in the original, where the striking comes
        # after the counting
        # (was: update_subtree_size, Festival.pm:4262, after set_deadlock_status
        # and before block_existing_sons_tree)
        $e->{'subtree'} = $father ? 0 : 1;
        if ($father and (($e->{'depth'} and $e->{'solved'}) or grep {!$_->{'dead'}} @$nodes)) {
            $e->{'subtree'}++;
            for (my $up = $father; $up and !$up->{'node'}{'dead'}; $up = $up->{'father'}) {$up->{'subtree'}++}
        }
        $settle->($e);
        $set_best->($e);

        # BY VALUE: every live macro's position gets the value of its score, the
        # position itself the best of those, and that is carried up towards the root,
        # each ancestor taking the best of its live macros
        # (was: set_values_to_moves_tree 6437, back_propagate_values_tree 4806)
        if (my $greedy = $spec->{'greedy'}) {
            $e->{'next_son'} = 0;
            my $value = $greedy->{'value'};
            $node->{'value'} = $value->(score_of($node));
            foreach my $k (grep {!$dead->[$_] and !$nodes->[$_]{'dead'}} 0 .. $#$nodes) {
                $nodes->[$k]{'value'} = $value->(score_of($nodes->[$k]));
            }
            for (my $up = $e; $up and !$up->{'node'}{'dead'}; $up = $up->{'father'}) {
                my ($un, $ud) = @$up{ 'son_node', 'son_dead' };
                my @live = map {$un->[$_]{'value'}} grep {!$ud->[$_] and !$un->[$_]{'dead'}} 0 .. $#$un;
                $up->{'node'}{'value'} = List::Util::max(@live) if @live;
            }
        }
        my $cell = $spec->{'cell'}->(score_of($e->{'best_past'}));
        if (!defined $in_ring{$cell}) {
            push @ring, $cell;
            $in_ring{$cell} = $#ring;
            $turn_of = $#ring;
        }
        $turn_of = $in_ring{$cell}           if $jump;
        $enqueue->($queue{$cell} //= [], $e) if defined $e->{'best'};
        return $e;
    }; ## end sub

    # the best untried macro waiting in one cell: (expansion, macro index)
    my $pick = sub ($cell) {
        my $heap = $queue{$cell} or return;
        while (defined(my $e = $dequeue->($heap))) {
            my $k = $e->{'best'};
            my $free =
                (defined $k and !$e->{'son_dead'}[$k] and !$e->{'son_node'}[$k]{'dead'} and !$e->{'son_node'}[$k]{'opened'})
                ? 1
                : 0;
            $set_best->($e);
            $enqueue->($heap, $e) if defined $e->{'best'} and !$free;
            next                  if !$free;
            return ($e, $k);
        }
        return;
    }; ## end sub

    # THE CYCLE CHECK.  Positions that lead only to one another, with no macro
    # among them that goes anywhere new, are never found dead by `settle`:
    # each has a living son -- another of the ring.  Every expansion keeps a
    # macro that points towards an unopened position (`leaf`); follow those
    # from the best line of play, and if the trail ends without having reached
    # one, the pointers are worked out again for the whole tree, from the
    # bottom up, and whatever is left without one is dead.
    my $no_way_out = sub ($e) {
        my %walked;
        while (defined $e->{'leaf'} and !$e->{'node'}{'dead'} and !$walked{$e}++) {
            my $son = $e->{'son_node'}[$e->{'leaf'}];
            last if $son->{'dead'};
            $e = $son->{'opened'} or return;
        }
        $_->{'leaf'} = undef foreach @opened;
        my $changed = 1;
        while ($changed) {
            $changed = 0;
            foreach my $x (reverse @opened) {
                next if defined $x->{'leaf'} or $x->{'node'}{'dead'};
                my ($nodes, $dead) = @$x{ 'son_node', 'son_dead' };
                foreach my $j (0 .. $#$nodes) {
                    next if $dead->[$j];
                    if ($nodes->[$j]{'dead'}) {$dead->[$j] = 1; next}
                    my $under = $nodes->[$j]{'opened'};
                    next if $under and !defined $under->{'leaf'};
                    $x->{'leaf'} = $j;
                    $changed = 1;
                    last;
                }
            }
        } ## end while ($changed)
        $_->{'node'}{'dead'} = 1 foreach grep {!defined $_->{'leaf'} and !$_->{'node'}{'dead'}} @opened;
        return;
    }; ## end sub

    # the best of the positions opened that are not dead
    # -- the original's way: any position rather than a root, any without a
    # corral rather than with one, then the best own score, the earlier at a
    # tie (was: best_node_in_tree, Festival.pm:6389)
    my $best_alive = sub () {
        my $best;
        foreach my $e (grep {!$_->{'node'}{'dead'}} @opened) {
            if (!$best) {$best = $e; next}
            next if !$e->{'depth'};
            if (!$best->{'depth'}) {$best = $e; next}
            next if $e->{'corral'};
            if ($best->{'corral'}) {$best = $e; next}
            $best = $e if $better->(score_of($e->{'node'}), score_of($best->{'node'}));
        }
        return $best;
    };

    # a position declared dead with everything under it
    my $bury = sub ($e) {
        return if $e->{'node'}{'dead'};
        $e->{'node'}{'dead'} = 1;
        my ($nodes, $dead) = @$e{ 'son_node', 'son_dead' };
        foreach my $k (0 .. $#$nodes) {
            $dead->[$k] = 1;
            my $under = $nodes->[$k]{'opened'};
            if   ($under) {__SUB__->($under)}
            else          {$nodes->[$k]{'dead'} = 1}
        }
        $settle->($e->{'father'}) if $e->{'father'};
    };

    # positions to be known before any root is opened (the original declares
    # every root's position a node first, and by value a macro into one of
    # them from another root's tree is then struck out: `known` are the roots
    # before the start check, see solve_girl)
    $node_of->($_) foreach @{ $spec->{'known'} // [] };

    # Is a root already in the OTHER side's perimeter?  Then the other search
    # got as far as here, and this one may be on the slide from its very first
    # macro -- so its generator is LOOSE from the start: no corral, no
    # "wasteful" test, everything the other search could have done.
    # (was: enable_inefficient_moves, set in FESS (Festival.pm:7796) when the
    # root's hash is in the perimeter)
    if ($met) {
        foreach my $root (@{ $spec->{'roots'} }) {
            my $key = $spec->{'meet_key'} ? $spec->{'meet_key'}->($root) : poskey($root);
            next                  if !defined $key or !$met->{$key};
            $state->{'loose'} = 1 if $met->{$key}[0] != $mine;
        }
    }

    # BY VALUE: the pick of the GIRL regime.  From the live root with the
    # fewest positions under it, down: at each position the value is worked
    # out again as the best of its live macros' values, and the macro taken is
    # the best-valued -- except on every epsilon-th visit, counted by the
    # positions opened under it, when the macros are taken in turn.  A macro
    # to a position already opened leads down into it; the first that does not
    # is the pick.  A position found dead on the way sends the walk back to a
    # root.
    # (was: choose_pos_son_to_expand_Epsilon_greedy_tree, Festival.pm:4778,
    # with go_to_root_greedy_tree 4696, recompute_values_tree 4726,
    # pick_son_Epsilon_greedy_tree 4766, choose_best_value_son_tree 4745 and
    # choose_cyclic_son_tree 4712)
    my $greedy_pick = sub () {
        my $epsilon = $spec->{'greedy'}{'epsilon'};
        my $root    = sub () {
            my $best;
            foreach my $r (grep {!$_->{'depth'} and !$_->{'node'}{'dead'}} @opened) {
                $best = $r if !$best or $r->{'subtree'} < $best->{'subtree'};
            }
            return $best;
        };
        my $e     = $root->() // return ();
        my $steps = 0;
        while (1) {

            # (the tree rule is what makes this walk end; without it a macro
            # could lead back up -- was: 'cycle cycle', Festival.pm:4690)
            Carp::confess('by value: the walk down the tree does not end') if ++$steps > 100_000;
            $settle->($e);
            if ($e->{'node'}{'dead'}) {
                $e = $root->() // return ();
                next;
            }
            my ($nodes, $dead) = @$e{ 'son_node', 'son_dead' };
            my @live = grep {!$dead->[$_] and !$nodes->[$_]{'dead'}} 0 .. $#$nodes;
            Carp::confess('by value: a live position without a live macro') if !@live;
            $e->{'node'}{'value'} = List::Util::max(map {$nodes->[$_]{'value'}} @live);
            my $k;
            if ($e->{'subtree'} % $epsilon == 0) {
                $k               = $e->{'next_son'};
                $k               = ($k + 1) % @$nodes while $dead->[$k] or $nodes->[$k]{'dead'};
                $e->{'next_son'} = ($k + 1) % @$nodes;
            }
            else {
                foreach my $j (@live) {
                    $k = $j if !defined $k or $nodes->[$j]{'value'} > $nodes->[$k]{'value'};
                }
            }
            my $under = $nodes->[$k]{'opened'};
            return ($e, $k) if !$under;
            $e = $under;
        } ## end while (1)
    }; ## end $greedy_pick = sub

    # what a line of play is judged by when the best one is looked for: the
    # best score met on the way to it -- or, by value, the position's own
    # (was: update_best_so_far, Festival.pm:6369)
    my $judge = $spec->{'greedy'} ? sub ($e) {score_of($e->{'node'})} : sub ($e) {score_of($e->{'best_past'})};
    my $best_so_far;
    foreach my $root (@{ $spec->{'roots'} }) {
        my $e = $open->($root, undef, undef);
        $best_so_far = $e if !$best_so_far or $better->($judge->($e), $judge->($best_so_far));
    }
    my ($turn, $idle, $result, $goal) = (0, 0, 'exhausted', undef);
    while ($idle <= 2 * @ring + 2) {
        $turn++;
        if (Time::HiRes::time() - $started > $spec->{'limit'} or run_aborted()) {$result = 'timeout'; last}

        # the pick: by value until the slide begins, from the cells otherwise;
        # an expansion and the index of one of its macros
        my ($e, $k, $cell);
        my $by_value = ($spec->{'greedy'} and !$state->{'found'}) ? 1 : 0;
        if ($by_value) {
            ($e, $k) = $greedy_pick->();
            last if !$e;
            $cell = $spec->{'cell'}->(score_of($e->{'best_past'}));
        }
        else {
            if ($turn & 1 or $state->{'found'}) {
                $cell    = $ring[$turn_of];
                $turn_of = ($turn_of + 1) % @ring;
            }
            else {
                $cell = $spec->{'cell'}->(score_of($best_so_far->{'best_past'}));
            }
            ($e, $k) = $pick->($cell);
            if (!$e) {$idle++; next}

            # on the slide nothing is picked but the slide itself
            if ($state->{'found'} and $e->{'weight'} + $e->{'son_weight'}[$k] >= 0) {
                $enqueue->($queue{$cell}, $e);
                $idle++;
                next;
            }
        } ## end else [ if ($by_value) ]
        $idle = 0;
        my $move = move_unpack($e->{'son_move'}[$k]);
        $move->{'pull'} = $mine;
        my $view = $live->($e);

        # (by value the expansion was never taken out of its queue, so it is
        # not put back either)
        if ($spec->{'dead'} and $spec->{'dead'}->($view, $move)) {
            $e->{'son_node'}[$k]{'dead'} = $e->{'son_dead'}[$k] = 1;
            $settle->($e);
            $set_best->($e);
            $enqueue->($queue{$cell}, $e) if defined $e->{'best'} and !$by_value;
            next;
        }

        # `refuse` strikes out the MACRO and says nothing about the position
        # it leads to: another macro may lead there and be welcome
        if ($spec->{'refuse'} and $spec->{'refuse'}->($view, $move)) {
            $e->{'son_dead'}[$k] = 1;
            $settle->($e);
            $set_best->($e);
            $enqueue->($queue{$cell}, $e) if defined $e->{'best'} and !$by_value;
            next;
        }
        my $new = $open->(apply($view, $move), $e, { 'move' => $move, 'weight' => $e->{'son_weight'}[$k] });
        $set_best->($e);
        $enqueue->($queue{ $spec->{'cell'}->(score_of($e->{'best_past'})) }, $e) if defined $e->{'best'} and !$by_value;
        $best_so_far = $new if $better->($judge->($new), $judge->($best_so_far));
        if ($new->{'solved'}) {
            ($result, $goal) = ('solved', $new);
            last;
        }
        $no_way_out->($best_so_far);
        $best_so_far = $best_alive->() // last if $best_so_far->{'node'}{'dead'};

        # a position with 64 positions opened under it (128 pulling) is looked
        # at slowly, once; what that finds is a stuck pattern
        for (my $up = $new; $up; $up = $up->{'father'}) {
            learn_stuck_pattern($live->($up), $mine, $spec->{'opt'} // {}) if $up->{'subtree'} == 64 + 64 * $mine;
        }

        # pulling, a pattern that catches the best line of play is tried on the
        # whole tree at once: whatever it catches is dead with all under it
        if ($mine and in_stuck_pattern($live->($best_so_far), 1)) {
            $bury->($_) foreach grep {!$_->{'node'}{'dead'} and in_stuck_pattern($live->($_), 1)} @opened;
            $best_so_far = $best_alive->() // last;
        }
    } ## end while ($idle <= 2 * @ring...)
    my @line;
    for (my $e = $goal; $e; $e = $e->{'father'}) {unshift @line, $e}
    return {
        'result' => $result,
        'line'   => \@line,
        'best'   => $best_so_far,
        'met'    => $state->{'found'},
        'tree'   => \@opened,
        'opened' => scalar @opened,
        'seen'   => scalar keys %node,
        'time'   => Time::HiRes::time() - $started,
    };
} ## end sub feature_search

# What the tree packs, unpacked: a node's score as the hash the mode's subs
# take (its keys travel with the node), a macro's four numbers, and an
# expansion's view with the player's region flooded afresh -- for whoever
# reads a tree after the search (the plan, the steps, the gates).
sub score_of ($node) {
    my %score;
    @score{ @{ $node->{'keys'} } } = unpack 'd*', $node->{'score'};
    return \%score;
}
sub move_pack ($m) {return pack 'nnnC', @$m{ 'from', 'to', 'man' }, $m->{'isbase'} ? 1 : 0}

sub move_unpack ($packed) {
    my ($from, $to, $man, $isbase) = unpack 'nnnC', $packed;
    return { 'from' => $from, 'to' => $to, 'man' => $man, 'isbase' => $isbase };
}
sub live_view ($e) {return set_reach({ %{ $e->{'view'} } })}

# The player's steps for a line of play: lower case for a step, upper case for
# a push, u r d l -- the form the project stores solutions in.  Each macro is
# asked for again, this time with its route, and between two pushes the player
# walks the shortest way round the boxes to where he has to stand.
#
# was: sol_moves_string and find_sol_move (Festival.pm)
sub steps_of ($line, $opt = {}) {
    my %letter = (-$Width => 'u', 1 => 'r', $Width => 'd', -1 => 'l');
    my $steps  = '';
    foreach my $i (1 .. $#$line) {
        my ($from_e, $to_e) = @$line[$i - 1, $i];
        my $view = live_view($from_e);

        # THE macro the search made, not just any macro into the same position:
        # two boxes can each go round and come back to their own cell and leave
        # the same position behind, with the player on different cells
        my $made    = $to_e->{'via'}{'move'};
        my ($moves) = possible_moves($view, 0, { %$opt, 'route' => 1 });
        my ($m) = grep {$_->{'from'} == $made->{'from'} and $_->{'to'} == $made->{'to'} and $_->{'man'} == $made->{'man'}} @$moves
            or Carp::confess('steps_of: the macro of the line is not among the macros of its position');
        my %box = %{ $view->{'box'} };
        my $sok = $view->{'sok'};
        foreach my $push (@{ $m->{'route'} }) {
            my ($c, $to) = @$push;
            my $stance = $Cm{$c}{$to};

            # walk to the stance
            my %came = ($sok => undef);
            my @q    = ($sok);
            my $bh   = 0;
            while ($bh < @q and !exists $came{$stance}) {
                my $p = $q[$bh++];
                foreach my $nb (@{ $Cg{$p} }) {
                    next if exists $came{$nb} or $box{$nb};
                    $came{$nb} = $p;
                    push @q, $nb;
                }
            }
            Carp::confess("steps_of: the player cannot get from $sok to $stance") if !exists $came{$stance};
            my $walk = '';
            for (my $p = $stance; defined $came{$p}; $p = $came{$p}) {$walk = $letter{ $p - $came{$p} } . $walk}
            $steps .= $walk . uc $letter{ $to - $c };
            delete $box{$c};
            $box{$to} = 1;
            $sok = $c;
        } ## end foreach my $push (@{ $m->{'route'...}})
    } ## end foreach my $i (1 .. $#$line)
    return $steps;
} ## end sub steps_of

# ---------------------------------------------------------------------------
# The plan
# ---------------------------------------------------------------------------
#
# A backward search that has pulled the boxes off the goals has, read the other
# way round, found an ORDER IN WHICH TO PUT THEM THERE.  The plan is that line
# of play turned round: a list of steps
#
#   {from => cell, to => cell, until => index}
#
# "a box comes from `from` and is put on `to`, and stays there until step
# `until` takes it away again" -- until -1 means for good.  from -2 means the
# box is simply standing on `to` when the plan begins (those steps are the best
# backward position itself), from -1 that it comes from nowhere (the backward
# search had taken the box off the board at a base).
#
# Nothing in the forward search FOLLOWS the plan.  It is a yardstick: packed()
# says how many steps of it a position has behind it, and that number is the
# first thing a position is judged by and the first coordinate of its cell.
# The plan of a backward line of play ($line as feature_search returns it,
# root first).
#
# was: get_parking_plan (Festival.pm:5522) with recompute_until (5474),
# fix_consecutive_pushes (5490) and move_mandatory_boxes_to_beginning (5457)
sub plan_of ($line) {
    my $best = $line->[-1];
    my @plan = map {{ 'from' => -2, 'to' => $_, 'until' => -1 }} sort {$b <=> $a} keys %{ $best->{'view'}{'box'} };
    for (my $e = $best; $e->{'father'}; $e = $e->{'father'}) {
        my $m = $e->{'via'}{'move'};
        my ($from, $to) = ($m->{'from'}, $m->{'isbase'} ? -1 : $m->{'to'});
        push @plan, { 'from' => $to, 'to' => $from, 'until' => -1 } if $from != $to;
    }
    plan_untils(\@plan);

    # two steps that move one box on, a -> b and then b -> c straight after,
    # are one step a -> c; a step that goes nowhere is none.  Over and over,
    # until neither is to be found.  The boxes standing there at the start
    # (from -2) are left as they are.  (The original's loop restarts from the
    # second step after every change and never looks at the last one, so what
    # it merges depends on the order it looks in.)
    my $changed = 1;
    while ($changed) {
        $changed = 0;
        foreach my $i (0 .. $#plan) {
            next if $plan[$i]{'from'} == -2;
            if ($plan[$i]{'to'} == $plan[$i]{'from'}) {
                splice @plan, $i, 1;
                $changed = 1;
                last;
            }
            next if $i == $#plan or $plan[$i]{'to'} != $plan[$i + 1]{'from'};
            $plan[$i]{'to'} = $plan[$i + 1]{'to'};
            splice @plan, $i + 1, 1;
            $changed = 1;
            last;
        }
    } ## end while ($changed)
    plan_untils(\@plan);

    # the boxes that stand where they will stay come first
    my @stay = grep {$_->{'from'} == -2 and $_->{'until'} == -1} @plan;
    my @rest = grep {$_->{'from'} != -2 or $_->{'until'} != -1} @plan;
    return [@stay, @rest];
} ## end sub plan_of

# until: the first later step that takes the box of this step away again
sub plan_untils ($plan) {
    foreach my $i (0 .. $#$plan) {
        $plan->[$i]{'until'} = -1;
        foreach my $j ($i + 1 .. $#$plan) {
            next if $plan->[$j]{'from'} != $plan->[$i]{'to'};
            $plan->[$i]{'until'} = $j;
            last;
        }
    }
    return;
}

# When the backward search took no box off the board, only the steps that put a
# box somewhere FOR GOOD are kept -- one per box -- and where each came from is
# forgotten.  (A plan with boxes missing is kept whole.)
#
# was: reduce_parking_order (Festival.pm:6561) and keep_only_perm (5562)
sub plan_for_good ($plan) {
    return $plan if keys %Start != grep {$_->{'from'} == -2} @$plan;
    return [map {{%$_, 'from' => $_->{'from'} == -2 ? -2 : -1}} grep {$_->{'until'} == -1} @$plan];
}

# How much of the plan a position has behind it.
#
# If a box that has to be standing where it will stay is not there, the answer
# is only how many of those are.  Otherwise it is the first step, counting from
# the END, that has not been made -- a step whose box was to be taken away
# again counts as made once the plan has got past the step that takes it --
# less the boxes of the start that are neither in place nor due to have left.
#
# was: score_parked_boxes (Festival.pm:5607) with its three helpers
sub packed ($view, $plan) {
    my $box   = $view->{'box'};
    my @there = map  {$box->{ $_->{'to'} } ? 1 : 0} @$plan;
    my $start = grep {$_->{'from'} == -2} @$plan;
    my @must  = grep {$plan->[$_]{'until'} == -1} 0 .. $start - 1;
    return scalar(grep {$there[$_]} @must) if grep {!$there[$_]} @must;
    my $done = @$plan;
    foreach my $i (reverse $start .. $#$plan) {
        next       if $there[$i];
        $done = $i if $plan->[$i]{'until'} == -1 or $plan->[$i]{'until'} >= $done;
    }
    my $good = grep {$there[$_] or $plan->[$_]{'until'} < $done} 0 .. $start - 1;
    return $done - ($start - $good);
}

# The cell the plan wants filled next, or -1 if there is none to name.
#
# was: next_parking_place (Festival.pm:5651)
sub next_place ($view, $plan) {
    my $box = $view->{'box'};
    return -1 if grep {$_->{'from'} == -2 and $_->{'until'} == -1 and !$box->{ $_->{'to'} }} @$plan;
    my $start = 0;
    $start++ while $start < @$plan and $plan->[$start]{'from'} == -2;
    my $done = @$plan;
    foreach my $i (reverse $start .. $#$plan) {
        next       if $box->{ $plan->[$i]{'to'} };
        $done = $i if $plan->[$i]{'until'} == -1 or $plan->[$i]{'until'} >= $done;
    }
    return $done == @$plan ? -1 : $plan->[$done]{'to'};
}

# OUT OF PLAN: for every stage of the plan, the cells from which a box can no
# longer be brought to any place the plan still has to fill.  The boxes the
# plan has put down for good by then are walls; from the places still to be
# filled a box is pulled backwards as far as it will go; whatever floor that
# does not reach (and is not one of the cells no box may stand on anyway) is
# out of plan for that stage.  It is the engine's "dead for this position" idea
# (live_cells) asked of the plan instead of the goals.
#
# Returns {zone => [{cell => 1}, ...], far => [{cell => pushes}, ...]}, one of
# each per stage: `far` is how many pushes a cell is from the zone, which is
# what the advisor that clears boxes out of it steers by.
#
# was: prepare_oop_zones (Festival.pm:3174), get_oop_zone_for_step (3115) and
# get_oop_distance_for_step (3160), and it is the original's in three things
# that look odd and are kept because the plain reading LOST a game: stage k
# has step k itself put down already; when the zone changes at a stage, the
# stages since the last change are given the NEW zone, so a stage usually
# works with the zone of the change ahead of it; and the distance from the
# zone is measured on a board furnished otherwise than the zone's -- the
# boxes standing BEFORE the stage (never fewer than the boxes of the start),
# those due to be taken away later included.  (2026-10-01, campaign
# ab-fest01-1: with "stage k = k steps done, zone and distance on one board"
# game 40361 went from solved in 76 positions to unsolved in 323; put back,
# it is 76 again.)
sub out_of_plan_zones ($plan) {
    my (@zone, @far);
    foreach my $stage (0 .. $#$plan - 1) {
        my %parked = map {$_->{'to'} => 1} grep {$_->{'until'} == -1} @$plan[0 .. $stage];
        my $view   = { 'box' => {}, 'frozen' => \%parked, 'reach' => {} };
        my @ahead  = map {$_->{'to'}} @$plan[$stage + 1 .. $#$plan];
        my %source = (%{ box_spread($view, \@ahead, 1) }, map {$_ => 1} @ahead);
        $zone[$stage] = { map {$_ => 1} grep {!$parked{$_} and !$Impossible{$_} and !exists $source{$_}} keys %Floor };
    }
    my ($now, $since) = ('', 0);
    my $flat = sub ($z) {join ',', sort {$a <=> $b} keys %$z};
    my @used = map {{}} 0 .. $#$plan + 1;
    foreach my $stage (0 .. $#$plan - 1) {
        $used[$stage] = $zone[$stage] if !%{ $used[$stage] };
    }
    foreach my $stage (0 .. $#$plan - 1) {
        next if $flat->($zone[$stage]) eq $now;
        $now      = $flat->($zone[$stage]);
        $used[$_] = $zone[$stage] foreach $since .. $stage;
        $since    = $stage;
    }
    my $start = grep {$_->{'from'} == -2} @$plan;
    foreach my $stage (0 .. $#$plan - 1) {
        my $upto   = $stage < $start ? $start : $stage;
        my %parked = map {$_->{'to'} => 1} grep {$_->{'until'} == -1 or $_->{'until'} >= $upto} @$plan[0 .. $upto - 1];
        $far[$stage] = box_spread({ 'box' => {}, 'frozen' => \%parked, 'reach' => {} }, [keys %{ $used[$stage] }], 0);
    }
    return { 'zone' => \@used, 'far' => \@far };
} ## end sub out_of_plan_zones

# How many boxes stand in another box's way: a box counts when, standing where
# it does, it takes goals away from some other box on the board (blocks{}{},
# %Blocks from the record, worked out for the level by
# Games::Sokoban::FestDev::blocking).
#
# was: hotspots_score over find_hotspots (Festival.pm:2965-2986)
sub in_the_way ($view, $blocks) {
    my @boxes = keys %{ $view->{'box'} };
    return scalar grep {
        my $blocker = $_;
        grep {$_ != $blocker and $blocks->{$_}{$blocker}} @boxes
    } @boxes;
}

# Everything a plan-driven forward search needs worked out once: the plan, its
# zones, who blocks whom, and how far every cell is from the goals (pulling
# back from all the goals at once over the empty level -- the record's
# %Goals_near).
#
# was: setup_plan_features (Festival.pm) and init_scored_distance (3356)
sub plan_context ($plan, $blocks) {
    return {
        'plan'     => $plan,
        'zones'    => out_of_plan_zones($plan),
        'blocks'   => $blocks,
        'goal_far' => \%Goals_near,
    };
}

# The numbers a plan-driven forward search judges a position by.
#
# was: score_board (Festival.pm:6704), the NORMAL / FORWARD_WITH_BASES branch
sub forward_score ($view, $ctx) {
    my $box    = $view->{'box'};
    my $packed = packed($view, $ctx->{'plan'});
    my $zone   = $ctx->{'zones'}{'zone'}[$packed] // {};
    my $far    = 0;
    $far += $ctx->{'goal_far'}{$_} // 1000000 foreach keys %$box;
    return {
        'packed'  => $packed,
        'regions' => scalar @{ (regions($view))[1] },
        'rooms'   => rooms_cut_apart($view),
        'astray'  => scalar(grep {$zone->{$_}} keys %$box),
        'in_way'  => in_the_way($view, $ctx->{'blocks'}),
        'far'     => $far,
    };
} ## end sub forward_score

# ... and which of two such scores is the better: more of the plan done, the
# floor in fewer pieces, fewer joins between rooms broken, fewer boxes astray,
# fewer in the way -- and then, of all things, the boxes FARTHER from the
# goals.  (That last line is the original's.  By the time it is reached
# everything that matters is equal; it seems to prefer the position that has
# kept its boxes out of the goal area.)
#
# was: is_better_score (Festival.pm:5991), the NORMAL push branch
sub forward_better ($s1, $s2) {
    return $s1->{'packed'} > $s2->{'packed'}   if $s1->{'packed'} != $s2->{'packed'};
    return $s1->{'regions'} < $s2->{'regions'} if $s1->{'regions'} != $s2->{'regions'};
    return $s1->{'rooms'} < $s2->{'rooms'}     if $s1->{'rooms'} != $s2->{'rooms'};
    return $s1->{'astray'} < $s2->{'astray'}   if $s1->{'astray'} != $s2->{'astray'};
    return $s1->{'in_way'} < $s2->{'in_way'}   if $s1->{'in_way'} != $s2->{'in_way'};
    return $s1->{'far'} > $s2->{'far'};
}

# The advisors of the plan-driven forward search.  Each names AT MOST ONE macro
# of the position -- by its place in @$moves -- and none may name one that
# undoes part of the plan.  Returns {advisor => index}, an advisor with
# nothing to say being left out.
#
#   pack          the best macro that gets the plan a step further
#   connectivity  ... that joins pieces of the free floor
#   rooms         ... that mends a join between rooms
#   in_way        ... that takes a box out of another box's way
#   astray        clear the zone that is out of plan: of the macros that take a
#                 box farther from it (and could be undone), the one whose box
#                 is nearest to it, and of those the one that goes farthest
#   opener        make room at the place the plan wants filled next: of the
#                 macros that move a box away from that place, the box nearest
#                 to it, carried farthest -- but only when no macro gets the
#                 plan further by itself
#   explorer      the best macro after which some box can be pushed that could
#                 not be before
#
# $scores are the scores of the positions the macros lead to, $afters the
# views.  "Best" is forward_better throughout.
#
# was: set_advisors_inner (Festival.pm:7692), its forward half: choose_advisor
# (6070) four times, new_oop_advisor (3213), pick_opener (7653), explorer
# (7620) with are_new_moves (7597).  The eighth, imagine, never speaks in this
# kind of search.
sub forward_advisors ($view, $base, $moves, $scores, $afters, $ctx) {
    my %said;
    my @keeps   = grep {$scores->[$_]{'packed'} >= $base->{'packed'}} 0 .. $#$moves;
    my $best_of = sub (@which) {
        my $best;
        foreach my $i (@which) {
            $best = $i if !defined $best or forward_better($scores->[$i], $scores->[$best]);
        }
        return $best;
    };
    my %gain = (
        'pack'         => sub ($s) {$s->{'packed'} > $base->{'packed'}},
        'connectivity' => sub ($s) {$s->{'regions'} < $base->{'regions'}},
        'rooms'        => sub ($s) {$s->{'rooms'} < $base->{'rooms'}},
        'in_way'       => sub ($s) {$s->{'in_way'} < $base->{'in_way'}},
    );
    foreach my $name (keys %gain) {
        my $i = $best_of->(grep {$gain{$name}->($scores->[$_])} @keeps);
        $said{$name} = $i if defined $i;
    }

    # nearest first, then farthest carried: the shape two of them share
    my $nearest_carried_farthest = sub ($where, @which) {
        my ($best, $near, $carried);
        foreach my $i (@which) {
            my ($from, $to) = ($where->{ $moves->[$i]{'from'} }, $where->{ $moves->[$i]{'to'} });
            next if defined $near and $from > $near;
            if (!defined $near or $from < $near) {($best, $near, $carried) = ($i, $from, $to); next}
            ($best, $carried) = ($i, $to) if $to > $carried;
        }
        return $best;
    };
    if ($base->{'astray'}) {
        my $far = $ctx->{'zones'}{'far'}[$base->{'packed'}] // {};
        my $i   = $nearest_carried_farthest->(
            $far,
            grep {
                my ($from, $to) = @{ $moves->[$_] }{ 'from', 'to' };
                        $scores->[$_]{'regions'} <= $base->{'regions'}
                    and $scores->[$_]{'rooms'} <= $base->{'rooms'}
                    and $scores->[$_]{'astray'} <= $base->{'astray'}
                    and defined $D{$to}{$from}
                    and defined $far->{$from}
                    and defined $far->{$to}
                    and $far->{$to} > $far->{$from}
                } @keeps
        );
        $said{'astray'} = $i if defined $i;
    } ## end if ($base->{'astray'})
    my $next = next_place($view, $ctx->{'plan'});
    if ($next != -1 and !grep {$scores->[$_]{'packed'} > $base->{'packed'}} 0 .. $#$moves) {
        my %steps = map {$_ => $Walk{$next}{$_} // 1000000} map {@{$_}{ 'from', 'to' }} @$moves;
        my $i     = $nearest_carried_farthest->(
            \%steps,
            grep {
                        $scores->[$_]{'regions'} <= $base->{'regions'}
                    and $scores->[$_]{'rooms'} <= $base->{'rooms'}
                    and $steps{ $moves->[$_]{'to'} } >= $steps{ $moves->[$_]{'from'} }
                } @keeps
        );
        $said{'opener'} = $i if defined $i;
    }
    my ($box, $reach) = @$view{ 'box', 'reach' };
    my $i = $best_of->(
        grep {
            my ($m, $after) = ($moves->[$_], $afters->[$_]);
            defined $D{ $m->{'to'} }{ $m->{'from'} } and grep {
                my $p = $_;
                $after->{'box'}{$p} and grep {
                    my ($stance, $to) = @{ $N{$p} }[$_, $_ ^ 2];
                            !$reach->{$stance}
                        and !$box->{$stance}
                        and $after->{'reach'}{$stance}
                        and !($Wall{$to} or $after->{'box'}{$to})
                    } 0 .. 3
                } keys %$box
            } @keeps
    );
    $said{'explorer'} = $i if defined $i;
    return \%said;
} ## end sub forward_advisors

# ---------------------------------------------------------------------------
# Bases
# ---------------------------------------------------------------------------
#
# A plan wants more than "where the boxes stand before they go home": it wants
# the whole order, first box to last.  The backward search that gives it starts
# from the solved level like any other, and has one thing the others have not:
# it may FINISH with a box.  A BASE is a cell a box starts on.  A box pulled
# onto a base has been traced back to the start -- so box and base both leave
# the board, the level gets smaller, and the search goes on with the rest until
# nothing is left.  Turned round, that line of play says in which order the
# boxes set out and where each of them goes.
#
# Two questions guard the taking off, because a box taken off wrongly is a plan
# that cannot be played:
#
#   * the base must be one of the BIGGEST GROUP OF BASES THAT CAN REACH EACH
#     OTHER (a box can be pushed from any of them to any other, the boxes of the
#     position standing as walls), and the player must be able to walk to all
#     of that group.  Those are the bases in the open; a base tucked away behind
#     the boxes waits until they are gone;
#   * the boxes that stay must still be matchable to the bases that stay, one
#     to one, each box on a cell it could have been pushed to from its base.
#
# And when a box CAN be taken off, nothing else is offered: every macro of the
# position that is not a taking off is thrown away, and of the takings off each
# box keeps one -- the first.
#
# The view of this search carries `base`.  Everything that follows is reached
# through possible_moves and apply; nothing else in the engine knows of bases.
# The cells a box may be pulled to while these bases wait: those a box could
# have been pushed to from one of them on the empty level, and the bases
# themselves.
#
# was: compute_possible_from_bases (Festival.pm:4883)
sub base_landing ($bases) {
    return $Base_landing{ join ',', sort {$a <=> $b} keys %$bases } //= do {
        my $spread = box_spread({ 'box' => {}, 'frozen' => {} }, [keys %$bases], 0);
        +{ (map {$_ => 1} keys %$spread), %$bases };
    };
}

# The biggest group of free bases that can reach each other, as a set.
#
# Two bases belong together when a box can be pushed from each to the other;
# a group is everything joined that way, directly or through other bases.  If
# several groups are the biggest, all of them are returned.
#
# was: compute_bases_scc (Festival.pm:4924).  The original takes the bases in
# order of cell and lets one that has no group yet take in every later base
# it is joined to directly -- one that already had a group included -- so
# where "joined" does not carry over (it goes by sides of the box) its groups
# depend on that order.  Here they do not.
sub biggest_base_group ($v) {
    my $box   = $v->{'box'};
    my @bases = sort {$a <=> $b} grep {!$box->{$_}} keys %{ $v->{'base'} };
    my $board = { 'box' => {}, 'frozen' => {%$box} };
    my %side;
    my @reach = map {
        my $spread = box_spread($board, [$_], 0, 0, \%side);
        +{ %$spread, $_ => 0 };
    } @bases;
    my @group = (-1) x @bases;
    my @size;
    foreach my $i (0 .. $#bases) {
        next if $group[$i] != -1;
        my $id = @size;
        my @q  = ($i);
        $group[$i] = $id;
        my $bh = 0;
        while ($bh < @q) {
            my $k = $q[$bh++];
            foreach my $j (grep {$group[$_] == -1} 0 .. $#bases) {
                next if !defined $reach[$k]{ $bases[$j] } or !defined $reach[$j]{ $bases[$k] };
                $group[$j] = $id;
                push @q, $j;
            }
        }
        push @size, scalar @q;
    } ## end foreach my $i (0 .. $#bases)
    my $most = List::Util::max(0, @size);
    return { map {$bases[$_] => 1} grep {$size[$group[$_]] == $most} 0 .. $#bases };
} ## end sub biggest_base_group

# Is it worth calling a pull from c1 to c2 a journey home -- are the two cells
# far enough apart?  Six steps on foot are; so are two different rooms; so is a
# room and a cell outside it that is neither at its mouth nor in line with the
# box.  Two cells that are both in no room at all are never far enough.
#
# was: boxes_in_different_rooms (Festival.pm:4831)
sub far_enough_apart ($c1, $c2) {
    return 1 if ($Walk{$c1}{$c2} // 1000000) >= 6;
    my ($r1, $r2) = ($Room{$c1}, $Room{$c2});
    return $r1 != $r2 ? 1 : 0 if defined $r1  and defined $r2;
    return 0                  if !defined $r1 and !defined $r2;
    return 0                  if defined $r1  and $Room_area[$r1]{$c2};
    return 0                  if defined $r2  and $Room_area[$r2]{$c1};
    return (int($c1 / $Width) != int($c2 / $Width) and $c1 % $Width != $c2 % $Width) ? 1 : 0;
}

# Can every box be given a base of its own that it could have been pushed from?
#
# was: test_base_matching (Festival.pm:4902) over check_matching_deadlock
# (3464), its pull half
sub boxes_match_bases ($box, $base) {
    my @boxes = keys %$box;
    my @bases = keys %$base;
    return 1 if !@boxes;
    return 0 if @boxes > @bases;
    my @cost = map {
        my $from = $_;
        [map {defined $D{$from}{ $boxes[$_] // -1 } ? 0 : 1} 0 .. $#bases]
    } @bases;
    return Games::Sokoban::Solver::Munkres::assign(\@cost) == @bases - @boxes ? 1 : 0;
}

# Mark the macros that take a box off the board (`isbase` => 1) -- and if there
# are any, hand back those alone, one per box.
#
# was: mark_sink_squares_moves (Festival.pm:4987)
sub mark_base_moves ($v, $moves) {
    my @moves = in_original_order(@$moves);
    my $open  = biggest_base_group($v);
    return @moves if grep {!$v->{'reach'}{$_}} keys %$open;
    my (@home, %done);
    foreach my $m (@moves) {
        my ($from, $to) = @$m{ 'from', 'to' };
        next if $done{$from} or !$open->{$to} or !far_enough_apart($from, $to);
        my %box  = %{ $v->{'box'} };
        my %base = %{ $v->{'base'} };
        delete $box{$from};
        delete $base{$to};
        next if !boxes_match_bases(\%box, \%base);
        $done{$from} = 1;
        push @home, { %$m, 'isbase' => 1 };
    }
    return @home ? @home : @moves;
} ## end sub mark_base_moves

# What the backward search with bases judges a position by: how many boxes are
# still on the board, the free floor in how many pieces, how many boxes still
# on goals, how many joins between rooms broken -- and how far the boxes are
# from the goals, which here is wanted LARGE: the search is running away from
# them.  $away is {cell => pushes to every goal, added up} -- the record's
# %Goals_away.
#
# was: score_board (Festival.pm:6704), the NORMAL / BASE_SEARCH pull branch,
# over init_scored_distance (3356)
sub backward_score ($view, $away) {
    my @boxes = keys %{ $view->{'box'} };
    my $far   = 0;
    $far += $away->{$_} foreach @boxes;
    return {
        'boxes'    => scalar @boxes,
        'regions'  => scalar @{ (regions($view))[1] },
        'on_goals' => scalar(grep {$Goal{$_}} @boxes),
        'rooms'    => rooms_cut_apart($view),
        'away'     => $far,
    };
}

# was: is_better_score (Festival.pm:5991), the NORMAL pull branch
sub backward_better ($s1, $s2) {
    return $s1->{'boxes'} < $s2->{'boxes'}       if $s1->{'boxes'} != $s2->{'boxes'};
    return $s1->{'regions'} < $s2->{'regions'}   if $s1->{'regions'} != $s2->{'regions'};
    return $s1->{'on_goals'} < $s2->{'on_goals'} if $s1->{'on_goals'} != $s2->{'on_goals'};
    return $s1->{'rooms'} < $s2->{'rooms'}       if $s1->{'rooms'} != $s2->{'rooms'};
    return $s1->{'away'} > $s2->{'away'};
}

# The advisors of that search.  As forward: each names at most one macro, by
# its place in @$moves; returns {advisor => index}.
#
#   pack          if a box can be taken off: the first such macro whose box
#                 stands on plain floor (neither goal nor base); failing that
#                 the one that leaves a goal hole last, keeps the floor in the
#                 fewest pieces, and has walked farthest.
#                 Otherwise: a macro that pulls a box OFF A GOAL without
#                 breaking up the floor or the rooms and takes it farther from
#                 the goals -- out of a goal hole last; then into the "kill
#                 zone" (below); then floor, rooms, and the longest pull
#   connectivity  the best macro that joins pieces of the free floor
#   rooms         the best macro that mends a join between rooms
#   explorer      the best macro after which some box can be pulled that could
#                 not be before
#
# and when `pack` takes a box off, the other three are silenced: there is
# nothing to weigh against going home.
#
# THE KILL ZONE is every cell that is six steps or more on foot from every
# base of the biggest group and that a box could be pushed to from that group
# with the boxes standing as walls.  (The original's loop leaves after the
# first cell it marks, so its zone is one cell -- the first by number.)
#
# was: set_advisors_inner (Festival.pm:7692), its pull half:
# packing_search_advisor (5148), find_best_base_pull (5118),
# pick_pull_advisor_normal (5052) with get_kill_zone (4856), choose_advisor
# (6070) twice, explorer (7620), discard_advisors_in_base_search (3561)
sub backward_advisors ($view, $base, $moves, $scores, $afters) {
    my %said;
    my $box     = $view->{'box'};
    my $best_of = sub (@which) {
        my $best;
        foreach my $i (@which) {
            $best = $i if !defined $best or backward_better($scores->[$i], $scores->[$best]);
        }
        return $best;
    };
    my $pick = sub ($ahead, @which) {    # the first that nothing later is ahead of
        my $best;
        foreach my $c (@which) {
            $best = $c if !$best or $ahead->($c, $best);
        }
        return $best ? $best->{'i'} : undef;
    };
    if (my @home = grep {$moves->[$_]{'isbase'}} 0 .. $#$moves) {
        my ($plain) = grep {
            my $from = $moves->[$_]{'from'};
            !$Goal{$from} and !$view->{'base'}{$from}
        } @home;
        $said{'pack'} = $plain // $pick->(
            sub ($new, $old) {
                return $new->{'hole'} < $old->{'hole'}       if $new->{'hole'} != $old->{'hole'};
                return $new->{'regions'} < $old->{'regions'} if $new->{'regions'} != $old->{'regions'};
                return $new->{'walk'} > $old->{'walk'};
            },
            map {
                my $m    = $moves->[$_];
                my %left = %$box;
                delete $left{ $m->{'from'} };
                $left{ $m->{'to'} } = 1;    # counted with the box ON the base, not gone
                +{
                    'i'       => $_,
                    'hole'    => $Goal_hole{ $m->{'from'} } ? 1 : 0,
                    'regions' => scalar @{ (regions({ 'box' => \%left, 'frozen' => {} }))[1] },
                    'walk'    => $Walk{ $m->{'to'} }{ $m->{'from'} } // 1000000,
                 };
                } @home
        );
        return \%said;
    } ## end if (my @home = grep {$moves...})
    my %kill;
    if ($view->{'base'}) {
        my $group = biggest_base_group($view);
        my @far   = grep {
            my $p = $_;
            !grep {($Walk{$p}{$_} // 1000000) < 6} keys %$group
        } keys %Floor;
        if (@far) {
            my $spread = box_spread({ 'box' => {}, 'frozen' => {%$box} }, [keys %$group], 0);
            $kill{$_} = 1 foreach grep {defined $spread->{$_}} @far;
        }
    }
    my $i = $pick->(
        sub ($new, $old) {
            return $new->{'hole'} < $old->{'hole'}       if $new->{'hole'} != $old->{'hole'};
            return $new->{'kill'} > $old->{'kill'}       if $new->{'kill'} != $old->{'kill'};
            return $new->{'regions'} < $old->{'regions'} if $new->{'regions'} != $old->{'regions'};
            return $new->{'rooms'} < $old->{'rooms'}     if $new->{'rooms'} != $old->{'rooms'};
            return $new->{'pulls'} > $old->{'pulls'};
        },
        map {
            my ($m, $s) = ($moves->[$_], $scores->[$_]);
            +{
                'i'       => $_,
                'hole'    => $Goal_hole{ $m->{'from'} } ? 1 : 0,
                'kill'    => $kill{ $m->{'to'} }        ? 1 : 0,
                'regions' => $s->{'regions'},
                'rooms'   => $s->{'rooms'},
                'pulls'   => $D{ $m->{'to'} }{ $m->{'from'} } // 1000000,
             };
        } grep {
                    $Goal{ $moves->[$_]{'from'} }
                and $scores->[$_]{'regions'} <= $base->{'regions'}
                and $scores->[$_]{'rooms'} <= $base->{'rooms'}
                and $scores->[$_]{'away'} > $base->{'away'}
            } 0 .. $#$moves
    );
    $said{'pack'}         = $i if defined $i;
    $i                    = $best_of->(grep {$scores->[$_]{'regions'} < $base->{'regions'}} 0 .. $#$moves);
    $said{'connectivity'} = $i if defined $i;
    $i                    = $best_of->(grep {$scores->[$_]{'rooms'} < $base->{'rooms'}} 0 .. $#$moves);
    $said{'rooms'}        = $i if defined $i;

    # a box that stands in both positions, a cell beside it the player could
    # not get to and now can, and room behind him to pull
    my $reach = $view->{'reach'};
    $i = $best_of->(
        grep {
            my $after = $afters->[$_];
            grep {
                my $p = $_;
                $after->{'box'}{$p} and grep {
                    my ($d, $stance) = ($_, $N{$p}[$_]);
                            !$reach->{$stance}
                        and !$box->{$stance}
                        and $after->{'reach'}{$stance}
                        and !grep {$Wall{$_} or $after->{'box'}{$_}}
                        $N{$stance}[$d]
                    } 0 .. 3
                } keys %$box
            } 0 .. $#$moves
    );
    $said{'explorer'} = $i if defined $i;
    return \%said;
} ## end sub backward_advisors

# A pull is only worth anything if the push it stands for could be MADE.  The
# forward search moves nothing but the edge boxes of a corral when there is
# one; so look at the position the pull leads to the way the forward search
# will: if its floor is in pieces and there is a corral, the box just pulled
# must be one of the corral's edge boxes -- and a box cannot be taken off the
# board there at all.
#
# Asked when a macro is PICKED, not when it is generated: it costs a freezing
# and a corral.
#
# was: can_played_reversed (Festival.pm:3443)
sub can_be_played_forward ($view, $m) {
    my $after = apply($view, $m);
    return 1 if $after->{'reach'}{$Sok0} and !grep {!$Start{$_}} keys %{ $after->{'box'} };
    return 1 if @{ (regions($after))[1] } <= 1;
    my $work = { 'box' => $after->{'box'}, 'frozen' => {}, 'sok' => $after->{'sok'}, 'reach' => { %{ $after->{'reach'} } } };
    freeze_fixed($work);
    my $only = corral_boxes($work) or return 1;
    return 0 if $m->{'isbase'};
    return $only->{ $m->{'to'} } ? 1 : 0;
}

# The backward search with bases.  $perimeter is the table it shares with the
# forward search that will follow.  Returns what feature_search returns; the
# line of play a plan is made of ends at {'best'}.
#
# was: packing_search (Festival.pm:7914) in BASE_SEARCH
sub base_search ($limit, $perimeter) {
    my $away = \%Goals_away;
    my $nbox = keys %Start;
    my @roots;
    foreach my $zone (@{ (regions({ 'box' => {%Goal}, 'frozen' => {} }))[1] }) {
        my $root = set_reach({ 'box' => {%Goal}, 'frozen' => {}, 'sok' => $zone->[0] });
        next if !@{ (possible_moves($root, 1, {}))[0] } or start_is_dead($root);
        $root->{'base'} = {%Start};
        push @roots, $root;
    }
    return undef if !@roots;
    return feature_search(
        {
            'roots'     => \@roots,
            'pull'      => 1,
            'perimeter' => $perimeter,
            'limit'     => $limit,
            'weighted'  => 1,
            'moves'     => sub ($view, $state) {possible_moves($view, 1, {})},
            'dead'      => sub ($view, $m) {picked_is_dead($view, $m, 1)},
            'refuse'    => sub ($view, $m) {!can_be_played_forward($view, $m)},
            'score'     => sub ($view) {backward_score($view, $away)},
            'better'    => \&backward_better,
            'cell'      => sub ($s) {"$s->{'boxes'},$s->{'on_goals'},$s->{'regions'},$s->{'rooms'}"},

            # over when the board is empty -- or when what is left stands where
            # boxes start and the player can walk to where he starts
            'solved' => sub ($view) {$view->{'reach'}{$Sok0} and !grep {!$Start{$_}} keys %{ $view->{'box'} }},

            # the forward search can only ever be in a position with every box on
            # the board; those are the ones written down, and without the bases
            'meet_key' => sub ($view) {
                return undef if keys %{ $view->{'box'} } != $nbox;
                return poskey({ 'box' => $view->{'box'}, 'reach' => $view->{'reach'} });
            },
            'advise' => sub ($e) {
                my @sons = @{ $e->{'sons'} };
                return [] if !@sons;
                my $said = backward_advisors(
                    $e->{'view'},
                    score_of($e->{'node'}),
                    [map {$_->{'move'}} @sons],
                    [map {score_of($_->{'node'})} @sons],
                    [map {$_->{'after'}} @sons]
                );
                return [values %$said];
            },
        }
    );
} ## end sub base_search

# ---------------------------------------------------------------------------
# The backward score of the HF family: HF, BICON, MAXDIST, MAXDIST2
# ---------------------------------------------------------------------------
#
# Three of the original's strategies are HF with another backward score -- the
# forward half is HF verbatim -- so the four share one score sub and one
# `better`, told apart by the name of the variant:
#
#   hf        regions, rooms, stuck boxes, away = the push distances to every
#             goal, added up over the boxes
#   bicon     the same, plus the bridge cells
#   maxdist   the same plus the bridge cells, and away = the matching distance
#   maxdist2  away = the matching distance, no bridge cells
#
# was: fill_hf_scores (Festival.pm:5379), the pull half, with
# set_max_dist_data_in_node (5394) for the two MAXDIST strategies
# Is there a side a box on p could be got at from: a neighbour that is not a
# wall (a box will do) and beyond it a free cell for the player?
# was: can_be_accessed_from_some_direction (Festival.pm:5159)
sub box_can_be_got_at ($view, $p) {
    my ($box, $frozen) = @$view{ 'box', 'frozen' };
    foreach my $d (0 .. 3) {
        my $near = $N{$p}[$d];
        next if $Wall{$near} or $frozen->{$near};
        my $far = $N{$near}[$d];
        return 1 if !($Wall{$far} or $frozen->{$far} or $box->{$far});
    }
    return 0;
}

# How many free floor cells lie on no cycle of the free floor -- cells the
# player can only ever pass through one way, bridges and dead ends.  A goal
# with no box on it counts as on a cycle whatever its shape.
#
# A cell is on a cycle when one of the steps out of it is: a step between two
# free cells that is not the only way from the one to the other.  A depth-first
# walk over the free cells finds the steps that ARE the only way: each cell
# keeps the depth it was found at and the shallowest depth that can be got
# back to from it or from anything found under it without using the step it
# was found by (`low`).  The step down to a cell is on a cycle when that
# cell's low is no deeper than its father's depth, and so is every step to a
# cell found earlier that is not the father.
# was: biconnect_score and biconnect_dfs (Festival.pm:866, 847), whose walk
# takes a neighbour's low where its depth is wanted and so gives an answer
# that depends on the order the directions are taken in; this one does not
sub bridge_cells ($view) {
    my ($box, $frozen) = @$view{ 'box', 'frozen' };
    my (%depth, %low, %on_cycle);
    my $walk = sub ($p, $father, $depth) {
        no warnings 'recursion';
        $depth{$p} = $low{$p} = $depth;
        foreach my $q (@{ $Cg{$p} }) {
            next if $q == $father or $frozen->{$q} or $box->{$q};
            if (defined $depth{$q}) {
                $low{$p}      = $depth{$q} if $depth{$q} < $low{$p};
                $on_cycle{$p} = $on_cycle{$q} = 1;
                next;
            }
            __SUB__->($q, $p, $depth + 1);
            $low{$p}      = $low{$q}          if $low{$q} < $low{$p};
            $on_cycle{$p} = $on_cycle{$q} = 1 if $low{$q} <= $depth;
        }
        return;
    }; ## end sub
    foreach my $p (sort {$a <=> $b} keys %Floor) {
        next if defined $depth{$p} or $frozen->{$p} or $box->{$p};
        $walk->($p, -1, 0);
    }
    $on_cycle{$_} = 1 foreach grep {!$box->{$_} and !$frozen->{$_}} keys %Goal;
    return keys(%Floor) - keys(%Start) - keys(%on_cycle);
} ## end sub bridge_cells

# Every box matched to one goal so that the push distances add up to the
# least; a pair the table has no entry for costs a million.
# was: compute_match_distance (Festival.pm:2988) -- the original gets a son's
# number by swapping one row of the father's matrix; the number is the same,
# so every position is simply asked afresh here
sub goals_matching ($view) {
    my @goals = sort {$a <=> $b} keys %Goal;
    my @cost  = map {
        my $p = $_;
        [map {$D{$p}{$_} // 1000000} @goals]
    } sort {$a <=> $b} keys %{ $view->{'box'} };
    Carp::confess('goals_matching: boxes and goals differ in number') if @cost != @goals;
    return Games::Sokoban::Solver::Munkres::assign(\@cost);
}

# The backward score of the family; $away is the record's %Goals_away.
# was: fill_hf_scores (Festival.pm:5379), the pull half: hf_hotspots (5168),
# get_distance_in_hf_search (5364), and for the two MAXDIST strategies
# set_max_dist_data_in_node (5394)
sub hf_backward_score ($view, $away, $variant) {
    my @boxes = keys %{ $view->{'box'} };
    my $score = {
        'regions' => scalar @{ (regions($view))[1] },
        'rooms'   => rooms_cut_apart($view),
        'stuck'   => scalar(grep {!box_can_be_got_at($view, $_)} @boxes),
        'bridges' => 0,
        'away'    => 0,
    };
    $score->{'bridges'} = bridge_cells($view) if $variant eq 'bicon' or $variant eq 'maxdist';
    if ($variant eq 'maxdist' or $variant eq 'maxdist2') {
        $score->{'away'} = goals_matching($view);
    }
    else {
        $score->{'away'} += $away->{$_} foreach @boxes;
    }
    return $score;
} ## end sub hf_backward_score

# In that order: the free floor in fewer pieces, fewer joins between rooms
# broken, then -- only with the floor in one piece -- fewer boxes that cannot
# be got at and fewer bridge cells, and last the boxes farther away.
# was: is_better_hf_score (Festival.pm:5193), the pull branch
sub hf_backward_better ($s1, $s2) {
    return $s1->{'regions'} < $s2->{'regions'} if $s1->{'regions'} != $s2->{'regions'};
    return $s1->{'rooms'} < $s2->{'rooms'}     if $s1->{'rooms'} != $s2->{'rooms'};
    if ($s1->{'regions'} == 1) {
        return $s1->{'stuck'} < $s2->{'stuck'}     if $s1->{'stuck'} != $s2->{'stuck'};
        return $s1->{'bridges'} < $s2->{'bridges'} if $s1->{'bridges'} != $s2->{'bridges'};
    }
    return $s1->{'away'} > $s2->{'away'};
}

# The one advisor of the HF family, and of REV: the macro that leads to the
# best score, provided that beats the position's own.  A macro to a position
# already opened is not named, nor one that pulls a box out of a cell of
# $skip_from (the HF family, pulling: out of a goal hole -- the box is where
# it belongs and would only have to go back).  Returns what `advise` returns:
# [index] or [].
# was: set_default_advisor (Festival.pm:6104)
sub advise_best_son ($e, $better, $skip_from = {}) {
    my ($best, $score) = (undef, score_of($e->{'node'}));
    foreach my $i (0 .. $#{ $e->{'sons'} }) {
        my $son = $e->{'sons'}[$i];
        next if $son->{'node'}{'opened'} or $skip_from->{ $son->{'move'}{'from'} };
        my $his = score_of($son->{'node'});
        next if !$better->($his, $score);
        ($best, $score) = ($i, $his);
    }
    return defined $best ? [$best] : [];
}

# ---------------------------------------------------------------------------
# The first real mode: HF -- and its three variants
# ---------------------------------------------------------------------------
#
# was: strategy 3 of solve_with_alg (Festival.pm) -- packing_search and then
# FESS twice, all in HF_SEARCH; the mode the drivers call FF_HF.  Strategies
# 4, 5 and 1 (FF_BICON, FF_MAXDIST, FF_MAXDIST2) are the same with the
# backward search in BICON_SEARCH, MAX_DIST_SEARCH, MAX_DIST_SEARCH2
#
# The idea: most of what makes a level hard is boxes standing in each other's
# way.  So first find out where the boxes WANT to be before they go home -- an
# arrangement in which they hinder nobody -- and then make the forward search
# aim for that arrangement instead of for the goals.
#
# BACKWARD, a third of the time and no more than 40 s (pull_time).  Start from
# the solved level and PULL the
# boxes off the goals.  Judge a position by: the free floor in one piece, no
# joins between rooms broken, no box that cannot be got at from any side, and
# -- last -- the boxes far from the goals.  The best position this reaches is
# the IMAGINED arrangement.  Every position it opens goes into the perimeter.
#
# FORWARD, the rest.  Judge a position by: the free floor in one piece, as many
# boxes as possible on cells of the imagined arrangement, few boxes in the way,
# and the boxes close to the imagined cells (each box matched to one cell, the
# cheapest matching over the push table).  The forward search never tries to
# put a box on a goal.  It does not have to: the imagined arrangement and all
# that led to it are in the perimeter, so as soon as the forward search gets
# near it meets an entry, and slides home down the backward tree.
#
# The forward half runs twice, as the original does: three quarters of its
# time with every macro free (so the queue order is the score alone), then the
# rest with the advisors' weights on.
#
# One advisor only, the same both ways: the macro that leads to the best score,
# provided that beats the position's own.  (Pulling, a box is not advised OUT
# of a goal hole: it is where it belongs and will only have to go back.)
#
# Both halves ask picked_is_dead of every macro they pick, and the backward
# half starts only from regions that pass start_is_dead.
#
# $opt->{'variant'} names the backward score -- hf (the default), bicon,
# maxdist or maxdist2, see hf_backward_score above; the three wrappers below
# are what the mode table calls.
# HOW LONG A MODE'S FIRST SEARCH RUNS: its third of the limit, as in the
# original, but no more than $PULL_CAP seconds (1.02).  The first search is
# the one that prepares the ground for the forward search -- pulling the boxes
# off the goals, or in REV pushing them away from the start -- and a third of
# a LONG limit is far more of it than a level needs: at a limit of 300 s most
# solutions came some 100 s of pulling plus a few seconds of pushing, where
# the same levels at 60 s were solved in 22-35 s.  Measured at 300 s against
# the plain third, twice, on two populations of 40 games: cap-300-1 (the HF
# family) 54 pairs solved either way, 4 lost, 6 won, 49 of the 54 sooner;
# cap-300-2 (all eight modes) 84 either way, 7 lost, 17 won, 65 sooner, the
# mean time of a solution 130.5 -> 84.2 s.  $thirds is how many thirds the
# mode gives that search (the chain modes two); the cap is multiplied likewise.
# The dragonfly is left out on purpose: its pull search IS the search and has
# the whole limit.
my $PULL_CAP = 40;

sub pull_time ($limit, $thirds = 1) {
    my $time = $thirds * $limit / 3;
    return $thirds * $PULL_CAP < $time ? $thirds * $PULL_CAP : $time;
}

sub solve_hf ($limit, $opt = {}) {
    my $started = Time::HiRes::time();
    my $variant = $opt->{'variant'} // 'hf';
    my %perimeter;

    # ---- backward: where do the boxes want to be?
    my $away = \%Goals_away;                           # how far a cell is from the goals, all of them together
    my $home = { 'box' => {%Goal}, 'frozen' => {} };
    my @roots;
    foreach my $zone (@{ (regions($home))[1] }) {
        my $root = set_reach({ 'box' => {%Goal}, 'frozen' => {}, 'sok' => $zone->[0] });
        push @roots, $root if @{ (possible_moves($root, 1, {}))[0] } and !start_is_dead($root);
    }
    return ('TIMEOUT', '', 0, 0, { 'why' => 'nothing can be pulled off the goals' }) if !@roots;
    my $back = feature_search(
        {
            'roots'     => \@roots,
            'pull'      => 1,
            'perimeter' => \%perimeter,
            'limit'     => pull_time($limit),
            'weighted'  => 1,
            'moves'     => sub ($view, $state) {possible_moves($view, 1, {})},
            'dead'      => sub ($view, $m) {picked_is_dead($view, $m, 1)},
            'solved'    => sub ($view) {$view->{'reach'}{$Sok0} and !grep {!$Start{$_}} keys %{ $view->{'box'} }},
            'better'    => \&hf_backward_better,
            'cell'      => sub ($s) {"$s->{'regions'},$s->{'rooms'}"},
            'advise'    => sub ($e) {advise_best_son($e, \&hf_backward_better, \%Goal_hole)},
            'score'     => sub ($view) {hf_backward_score($view, $away, $variant)},
        }
    );
    return hf_forward($limit, $started, \%perimeter, $back, $opt);
} ## end sub solve_hf

# The forward half of HF, which the chain modes below share: the imagined
# arrangement is the best position of $back, the backward search just run.
# Returns what solve_hf returns.
sub hf_forward ($limit, $started, $perimeter, $back, $opt) {
    my $best     = live_view($back->{'best'});
    my %imagined = %{ $best->{'box'} };
    my @imagined = sort {$a <=> $b} keys %imagined;

    # where a box may be left standing however wasteful it looks: the original
    # asks whether the cell's byte on the imagined board is anything but zero
    # -- a box there, or the player's region there (walls and goals are not
    # landing cells).  Reproduced as it is, region included: the boxes alone
    # were measured against it on 90 paired games and came out even (memory
    # project_fest_imagined_region_exemption).
    # (was: is_inefficient_position, Festival.pm:2567)
    my %keep = (%imagined, %{ $best->{'reach'} });

    # ---- forward: get to that arrangement; the perimeter does the rest
    my $fwd_better = sub ($s1, $s2) {
        my ($ok1, $ok2) = ($s1->{'to_imagined'} < 1000000, $s2->{'to_imagined'} < 1000000);
        return $ok1                                if $ok1 != $ok2;
        return $s1->{'regions'} < $s2->{'regions'} if $s1->{'regions'} != $s2->{'regions'};
        return $s1->{'imagine'} > $s2->{'imagine'} if $s1->{'imagine'} != $s2->{'imagine'};
        return $s1->{'in_way'} < $s2->{'in_way'}   if $s1->{'in_way'} != $s2->{'in_way'};
        return $s1->{'to_imagined'} < $s2->{'to_imagined'};
    };
    my $fwd_score = sub ($view) {
        my ($box, $frozen) = @$view{ 'box', 'frozen' };
        my @boxes  = sort {$a <=> $b} keys %$box;
        my $in_way = 0;
        foreach my $p (grep {!$imagined{$_}} @boxes) {
            $in_way++ if grep {$Wall{$_} or $frozen->{$_} or $box->{$_}} @{ $N{$p} };
        }
        $in_way += grep {!$box->{$_} and !box_can_be_got_at($view, $_)} @imagined;

        # every box to one imagined cell, as cheaply as the push table allows;
        # a box shut in a full 2x2 block goes nowhere, so it is "at" its own
        # cell or the whole thing is impossible
        my @cost = map {
            my $p = $_;
            is_frozen_in_square($view, $p)
                ? [map {$_ == $p ? 0 : 1000000} @imagined]
                : [map {$D{$p}{$_} // 1000000} @imagined]
        } @boxes;
        return {
            'regions'     => scalar @{ (regions($view))[1] },
            'imagine'     => scalar(grep {$imagined{$_}} @boxes),
            'in_way'      => $in_way,
            'to_imagined' => Games::Sokoban::Solver::Munkres::assign(\@cost),
        };
    }; ## end sub
    my ($found, $opened) = (undef, $back->{'opened'});
    foreach my $run ([0, 0.75], [1, 1]) {
        my ($weighted, $share) = @$run;
        my $left = $limit - (Time::HiRes::time() - $started);
        last if $left <= 0;
        $found = feature_search(
            {
                'roots'     => [start_view()],
                'pull'      => 0,
                'perimeter' => $perimeter,
                'limit'     => $left * $share,
                'weighted'  => $weighted,
                'dead'      => sub ($view, $m) {picked_is_dead($view, $m, 0)},
                'solved'    => sub ($view) {!grep {!$Goal{$_}} keys %{ $view->{'box'} }},
                'score'     => $fwd_score,
                'better'    => $fwd_better,
                'cell'      => sub ($s) {"$s->{'regions'},$s->{'imagine'}"},
                'advise'    => sub ($e) {advise_best_son($e, $fwd_better)},
                'moves'     => sub ($view, $state) {
                    my $loose = ($state->{'found'} or $state->{'loose'}) ? 1 : 0;
                    possible_moves(
                        $view, 0,
                        {
                            %$opt,
                            'keep'        => \%keep,
                            'corral'      => $loose ? 0 : 1,
                            'inefficient' => $loose ? 0 : 1,
                        }
                    );
                },
            }
        );
        $opened += $found->{'opened'};
        last if $found->{'result'} eq 'solved';
    } ## end foreach my $run ([0, 0.75],...)
    my $doba = Time::HiRes::time() - $started;
    my %told = ('backward' => $back, 'forward' => $found, 'imagined' => \@imagined, 'perimeter' => scalar keys %$perimeter);
    return ('TIMEOUT', '', $doba, $opened, \%told) if !$found or $found->{'result'} ne 'solved';

    # the steps: the macros of the slide were made with the corral and the
    # "wasteful" test off, so they are looked up the same way
    my $steps = steps_of($found->{'line'}, { %$opt, 'keep' => \%keep, 'corral' => 0, 'inefficient' => 0 });
    return ('SOLVED', $steps, $doba, $opened, \%told);
} ## end sub hf_forward

# was: strategies 4, 5 and 1 of solve_with_alg (Festival.pm:8467) -- FF_BICON,
# FF_MAXDIST, FF_MAXDIST2
sub solve_bicon   ($limit, $opt = {}) {return solve_hf($limit, { %$opt, 'variant' => 'bicon' })}
sub solve_maxdist ($limit, $opt = {}) {return solve_hf($limit, { %$opt, 'variant' => 'maxdist' })}

sub solve_maxdist2 ($limit, $opt = {}) {
    if (my $chain = chain_variant('maxdist2')) {return solve_chain($limit, $opt, @$chain)}
    return solve_hf($limit, { %$opt, 'variant' => 'maxdist2' });
}

# ---------------------------------------------------------------------------
# The second mode: BASE, the one with a plan
# ---------------------------------------------------------------------------
#
# was: strategy 0 of solve_with_alg (Festival.pm) -- packing_search in
# BASE_SEARCH, setup_plan_features, FESS in FORWARD_WITH_BASES; the mode the
# drivers call FF_BASE
#
# BACKWARD, a third of the time (pull_time): the search with bases (above).  Its best line
# of play, turned round, is the PLAN.
#
# FORWARD, the rest.  A position is judged first of all by how much of the plan
# it has behind it, then by the floor, the rooms, the boxes that stand where
# the plan has no use for them, the boxes in each other's way.  Seven advisors
# each name a macro.  Nothing follows the plan step by step -- it is only ever
# a yardstick -- and the forward search may still stumble on the backward
# tree's first positions (those with every box still on the board) and slide
# home down it.
#
# A box may be left standing on any cell the plan uses, however wasteful that
# looks to the move generator.
#
# As in HF, both halves ask picked_is_dead of every macro they pick and the
# backward half starts only from regions that pass start_is_dead.
sub solve_base ($limit, $opt = {}) {
    if (my $chain = chain_variant('base')) {return solve_chain($limit, $opt, @$chain)}
    my $started = Time::HiRes::time();
    my %perimeter;
    my $back = base_search(pull_time($limit), \%perimeter)
        or return ('TIMEOUT', '', 0, 0, { 'why' => 'nothing can be pulled off the goals' });
    my @line;
    for (my $e = $back->{'best'}; $e; $e = $e->{'father'}) {unshift @line, $e}
    my $whole = plan_of(\@line);
    my $plan  = plan_for_good($whole);
    my %keep  = map {$_->{'to'} => 1} @$whole;
    my $ctx   = plan_context($plan, \%Blocks);
    my $left  = $limit - (Time::HiRes::time() - $started);
    my %told  = ('backward' => $back, 'plan' => $plan, 'perimeter' => scalar keys %perimeter);
    my $found = $left <= 0 ? undef : feature_search(
        {
            'roots'     => [start_view()],
            'pull'      => 0,
            'perimeter' => \%perimeter,
            'limit'     => $left,
            'weighted'  => 1,
            'dead'      => sub ($view, $m) {picked_is_dead($view, $m, 0)},
            'solved'    => sub ($view) {!grep {!$Goal{$_}} keys %{ $view->{'box'} }},
            'score'     => sub ($view) {forward_score($view, $ctx)},
            'better'    => \&forward_better,
            'cell'      => sub ($s) {"$s->{'packed'},$s->{'regions'},$s->{'astray'}"},
            'advise'    => sub ($e) {
                my @sons = @{ $e->{'sons'} };
                return [] if !@sons;
                my $said = forward_advisors(
                    $e->{'view'},
                    score_of($e->{'node'}),
                    [map {$_->{'move'}} @sons],
                    [map {score_of($_->{'node'})} @sons],
                    [map {$_->{'after'}} @sons], $ctx
                );
                return [values %$said];
            },
            'moves' => sub ($view, $state) {
                my $loose = ($state->{'found'} or $state->{'loose'}) ? 1 : 0;
                possible_moves(
                    $view, 0,
                    {
                        %$opt,
                        'keep'        => \%keep,
                        'corral'      => $loose ? 0 : 1,
                        'inefficient' => $loose ? 0 : 1,
                    }
                );
            },
        }
    );
    $told{'forward'} = $found;
    my $doba   = Time::HiRes::time() - $started;
    my $opened = $back->{'opened'} + ($found ? $found->{'opened'} : 0);
    return ('TIMEOUT', '', $doba, $opened, \%told) if !$found or $found->{'result'} ne 'solved';
    my $steps = steps_of($found->{'line'}, { %$opt, 'keep' => \%keep, 'corral' => 0, 'inefficient' => 0 });
    return ('SOLVED', $steps, $doba, $opened, \%told);
} ## end sub solve_base

# ---------------------------------------------------------------------------
# The mode REV: push the boxes away first
# ---------------------------------------------------------------------------
#
# was: strategy 6 of solve_with_alg (Festival.pm:8467) -- REV_SEARCH in both
# halves: FESS in the packing slot, then packing_search and FESS again in the
# forward slot; the mode the drivers call FF_REV
#
# HF finds where the boxes want to be by pulling them off the goals.  REV
# finds it the other way round, by PUSHING them away from the start -- as far
# from the goals as they will go, into an arrangement in which every box can
# still be pushed somewhere.  Three searches:
#
#   1  push, a third of the time (pull_time), from the start.  A position is judged by the
#      free floor in one piece, no joins between rooms broken, as few boxes as
#      possible that stand OFF a goal and can be pushed nowhere ("stuck"), and
#      -- last -- the boxes far away: from the stuck boxes on foot when there
#      are any, else from the goals.  The best position found is the IMAGINED
#      arrangement, and the boxes the freezing walls in on it are its WALLED
#      cells.  Every position opened goes into the perimeter.
#
#   2  pull, the rest of the time, from the solved level towards that
#      arrangement.  A position is judged by whether its boxes can be matched
#      to the imagined cells at all, the free floor in one piece, (with the
#      floor in pieces) the boxes far from the goals, then as many boxes as
#      possible ON imagined cells, then the matching cheap.  A box standing on
#      a walled cell is not pulled, and a box may be left on an imagined cell
#      however wasteful that looks.  This search has to meet the first one's
#      perimeter -- if it does not, the mode gives up and says so -- and once
#      it has, it slides down the push tree to the start, writing the
#      positions of the slide down for the third search.
#
#   3  push again, what is left of the time, judged as the first: it meets the
#      pull tree's entries and slides down them to the solved level.
#
# One advisor: the macro to the best score if that beats the position's own,
# and pushing, before anything else, the first macro that takes a box INTO a
# goal hole.
#
# Two things the model does that the original does not, both on purpose.  The
# original does not write the LAST position of a pull search into the
# perimeter (its loop leaves on "solved" before it gets there), so its third
# search cannot start sliding at its root and has to open some son first; here
# every opened position is written down, the root of the third search is one
# of them, and it starts on the slide at once (the loose generator, see
# feature_search).  And the original's push table overestimates now and then;
# the model's distances are exact.
# Can a box on p be pushed somewhere: a push the map has, its landing cell
# free, the player's cell behind the box free, and the push not dead on
# arrival?
# was: can_be_pushed_to_direction (Festival.pm:5298), which asked the bare
# geometry
sub can_be_pushed_somewhere ($view, $p) {
    my ($box, $frozen) = @$view{ 'box', 'frozen' };
    my $cm = $Cm{$p} or return 0;
    foreach my $d (0 .. 3) {
        my $to     = $N{$p}[$d];
        my $stance = $cm->{$to} // next;
        next if $frozen->{$to}     or $box->{$to};
        next if $frozen->{$stance} or $box->{$stance};
        next if dead_push($view, $p, $d);
        return 1;
    }
    return 0;
}

# The boxes off a goal that can be pushed nowhere: the "stuck" of this mode.
# was: get_rev_hotspots and rev_hotspots (Festival.pm:5305, 5336)
sub rev_stuck ($view) {
    return [grep {!$Goal{$_} and !can_be_pushed_somewhere($view, $_)} sort {$a <=> $b} keys %{ $view->{'box'} }];
}

# How far the boxes are, added up: from the nearest stuck box on foot (boxes
# ignored) when there are stuck boxes, else from the nearest goal by pushes.
# was: rev_hotspots_distance (Festival.pm:5319) with expand_group (822) and
# get_scored_distance (3374)
sub rev_far ($view, $stuck, $near_goal) {
    my $sum = 0;
    foreach my $p (keys %{ $view->{'box'} }) {
        $sum += @$stuck ? min(map {$Walk{$_}{$p} // 1000000} @$stuck) : ($near_goal->{$p} // 1000000);
    }
    return $sum;
}

# was: set_score_in_rev_mode (Festival.pm:5352), the push half, with the
# common part of score_board (6704)
sub rev_push_score ($view, $near_goal) {
    my $stuck = rev_stuck($view);
    return {
        'regions' => scalar @{ (regions($view))[1] },
        'rooms'   => rooms_cut_apart($view),
        'stuck'   => scalar @$stuck,
        'far'     => rev_far($view, $stuck, $near_goal),
    };
}

# was: is_better_rev_score (Festival.pm:5228), the push branch
sub rev_push_better ($s1, $s2) {
    return $s1->{'regions'} < $s2->{'regions'} if $s1->{'regions'} != $s2->{'regions'};
    return $s1->{'rooms'} < $s2->{'rooms'}     if $s1->{'rooms'} != $s2->{'rooms'};
    return $s1->{'stuck'} < $s2->{'stuck'}     if $s1->{'stuck'} != $s2->{'stuck'};
    return $s1->{'far'} > $s2->{'far'};
}

# The push advisor: the first macro that takes a box into a goal hole, else
# the best son.
# was: set_rev_advisor (Festival.pm:6419), the push half
sub rev_push_advise ($e) {
    my @sons = @{ $e->{'sons'} };
    my ($hole) = grep {$Goal_hole{ $sons[$_]{'move'}{'to'} }} 0 .. $#sons;
    return [$hole] if defined $hole;
    return advise_best_son($e, \&rev_push_better);
}

# Every box matched to one imagined cell so that the pushes FROM the imagined
# cells TO the boxes -- that is, the pulls from the boxes to the cells -- add
# up to the least; a million where the table has no entry.
# was: compute_rev_distance (Festival.pm:3064)
sub imagined_matching ($view, $imagined) {
    my @cost = map {
        my $p = $_;
        [map {$D{$_}{$p} // 1000000} @$imagined]
    } sort {$a <=> $b} keys %{ $view->{'box'} };
    Carp::confess('imagined_matching: boxes and imagined cells differ in number') if @cost != @$imagined;
    return Games::Sokoban::Solver::Munkres::assign(\@cost);
}

# was: set_score_in_rev_mode (Festival.pm:5352), the pull half, with
# compare_to_imagined_hf (5342) and set_rev_distance (5278)
sub rev_pull_score ($view, $away, $imagined) {
    my $box = $view->{'box'};
    my $far = 0;
    $far += $away->{$_} foreach keys %$box;
    return {
        'regions'     => scalar @{ (regions($view))[1] },
        'imagine'     => scalar(grep {$box->{$_}} @$imagined),
        'away'        => $far,
        'to_imagined' => imagined_matching($view, $imagined),
    };
}

# was: is_better_rev_score (Festival.pm:5228), the pull branch
sub rev_pull_better ($s1, $s2) {
    my ($ok1, $ok2) = ($s1->{'to_imagined'} < 1000000, $s2->{'to_imagined'} < 1000000);
    return $ok1                                if $ok1 != $ok2;
    return $s1->{'regions'} < $s2->{'regions'} if $s1->{'regions'} != $s2->{'regions'};
    if ($s1->{'regions'} > 1) {
        return $s1->{'away'} > $s2->{'away'} if $s1->{'away'} != $s2->{'away'};
    }
    return $s1->{'imagine'} > $s2->{'imagine'} if $s1->{'imagine'} != $s2->{'imagine'};
    return $s1->{'to_imagined'} < $s2->{'to_imagined'};
}

# was: strategy 6 of solve_with_alg (Festival.pm:8467), with
# packing_search_control (8404) and forward_search_control (8430) in
# REV_SEARCH, setup_rev_board (5265)
sub solve_rev ($limit, $opt = {}) {
    my $started   = Time::HiRes::time();
    my $near_goal = \%Goals_near;
    my %perimeter;
    my $push_spec = sub ($left) {
        return {
            'roots'     => [start_view()],
            'pull'      => 0,
            'perimeter' => \%perimeter,
            'limit'     => $left,
            'weighted'  => 1,
            'dead'      => sub ($view, $m) {picked_is_dead($view, $m, 0)},
            'solved'    => sub ($view) {!grep {!$Goal{$_}} keys %{ $view->{'box'} }},
            'score'     => sub ($view) {rev_push_score($view, $near_goal)},
            'better'    => \&rev_push_better,
            'cell'      => sub ($s) {"$s->{'regions'}"},
            'advise'    => \&rev_push_advise,
            'moves'     => sub ($view, $state) {
                my $loose = ($state->{'found'} or $state->{'loose'}) ? 1 : 0;
                possible_moves($view, 0, { %$opt, 'corral' => $loose ? 0 : 1, 'inefficient' => $loose ? 0 : 1 });
            },
        };
    }; ## end sub
    my $elapsed = sub {Time::HiRes::time() - $started};

    # ---- 1: push the boxes away
    my $away_search = feature_search($push_spec->(pull_time($limit)));
    my $opened      = $away_search->{'opened'};
    my %told        = ('away' => $away_search);
    if ($away_search->{'result'} eq 'solved') {
        $told{'forward'} = $away_search;
        return ('SOLVED', steps_of($away_search->{'line'}, { %$opt, 'corral' => 0, 'inefficient' => 0 }),
            $elapsed->(), $opened, \%told);
    }
    my $best     = live_view($away_search->{'best'});
    my @imagined = sort {$a <=> $b} keys %{ $best->{'box'} };
    my $walled =
        freeze_fixed({ 'box' => $best->{'box'}, 'frozen' => {}, 'sok' => $best->{'sok'}, 'reach' => { %{ $best->{'reach'} } } })
        ->{'frozen'};
    @told{ 'imagined', 'walled' } = (\@imagined, $walled);

    # where a pulled box may be left standing however wasteful it looks: as in
    # HF, any cell whose byte on the imagined board is not zero -- here the
    # board is the raw one, so a box there, the player's region there, or a
    # goal.  Reproduced as it is (the boxes alone measured even, as in HF).
    # (was: is_inefficient_position, 2571)
    my %keep = (%{ $best->{'box'} }, %{ $best->{'reach'} }, %Goal);

    # ---- 2: pull the boxes off the goals towards that arrangement
    my $away = \%Goals_away;
    my @roots;
    foreach my $zone (@{ (regions({ 'box' => {%Goal}, 'frozen' => {} }))[1] }) {
        my $root = set_reach({ 'box' => {%Goal}, 'frozen' => {}, 'sok' => $zone->[0] });
        push @roots, $root if @{ (possible_moves($root, 1, {}))[0] } and !start_is_dead($root);
    }
    return ('FAILED', '', $elapsed->(), $opened, { %told, 'why' => 'nothing can be pulled off the goals' }) if !@roots;
    my $left = $limit - $elapsed->();
    return ('TIMEOUT', '', $elapsed->(), $opened, { %told, 'why' => 'no time for the pull search' }) if $left <= 0;
    my $back = feature_search(
        {
            'roots'     => \@roots,
            'pull'      => 1,
            'perimeter' => \%perimeter,
            'limit'     => $left,
            'weighted'  => 1,
            'dead'      => sub ($view, $m) {picked_is_dead($view, $m, 1)},
            'solved'    => sub ($view) {$view->{'reach'}{$Sok0} and !grep {!$Start{$_}} keys %{ $view->{'box'} }},
            'score'     => sub ($view) {rev_pull_score($view, $away, \@imagined)},
            'better'    => \&rev_pull_better,
            'cell'      => sub ($s) {"$s->{'imagine'},$s->{'regions'}"},
            'advise'    => sub ($e) {advise_best_son($e, \&rev_pull_better)},
            'moves'     => sub ($view, $state) {
                my ($moves) = possible_moves($view, 1, { 'keep' => \%keep });
                return $state->{'found'} ? $moves : [grep {!$walled->{ $_->{'from'} }} @$moves];
            },
        }
    );
    $opened += $back->{'opened'};
    @told{ 'backward', 'perimeter' } = ($back, scalar keys %perimeter);

    # (a search that walked away with budget in hand FAILED, and says why; one
    # that used its budget up is a TIMEOUT whatever it was doing -- the
    # engine's own rule since 0.10)
    if (!$back->{'met'}) {
        my $doba = $elapsed->();
        return ($doba >= $limit ? 'TIMEOUT' : 'FAILED', '', $doba, $opened, { %told, 'why' => 'perimeter not reached' });
    }

    # ---- 3: push again, down the pull tree
    $left = $limit - $elapsed->();
    return ('TIMEOUT', '', $elapsed->(), $opened, { %told, 'why' => 'no time for the forward search' }) if $left <= 0;
    my $found = feature_search($push_spec->($left));
    $opened += $found->{'opened'};
    $told{'forward'} = $found;
    my $doba = $elapsed->();
    return ('TIMEOUT', '', $doba, $opened, \%told) if $found->{'result'} ne 'solved';
    my $steps = steps_of($found->{'line'}, { %$opt, 'corral' => 0, 'inefficient' => 0 });
    return ('SOLVED', $steps, $doba, $opened, \%told);
} ## end sub solve_rev

# ---------------------------------------------------------------------------
# The mode DRAGONFLY: a pull search without a tree, then a naive push search
# ---------------------------------------------------------------------------
#
# was: strategy 7 of solve_with_alg (Festival.pm:8467) -- dragonfly_search
# (8237) in the packing slot, FESS in NAIVE_SEARCH in the forward slot; the
# mode the drivers call FF_DRAGONFLY
#
# THE DRAGONFLY is the lightest of the backward searches: no cells, no
# advisors, no tree -- one heap of positions, ordered by how far the boxes are
# from where they start (every box matched to one start cell, the cheapest
# matching over the pull table) and, at a tie, by how many stand on a start
# cell already, then by age.  A node keeps only the pull that made it and its
# father; its position is replayed from the root when it is expanded (hence
# the name: it weighs next to nothing).  The perimeter table doubles as the
# record of what has been seen.  Expanding a node: its own pull is first put
# to the expensive tests of a whole position -- all of them but the matching
# test, which this search leaves out -- then every pull the position has,
# less those the corral rule strikes out; a child that is a position already
# seen, or whose boxes cannot be matched to the start cells at all, is
# dropped.  It runs until the heap is empty, the level's start is reached or
# the time is up -- and its time is THE WHOLE LIMIT (three
# times the packing third), so the forward search below only ever runs when
# the dragonfly stopped early.  Nothing else is handed over: no imagined
# arrangement, no plan.
#
# THE CORRAL RULE: with the free floor in pieces and a corral on the wallified
# board, a pull is struck out when it pulls the box the last pull placed, or
# when after it the player's access round that box is what it was before --
# unless it reaches the start.  (The original's comment: a corral that was not
# dealt with on the way here is a contradiction.)  At a root there is no last
# pull; there is no corral either, since every goal has its box.
#
# THE NAIVE SEARCH, forward: the big tree with the plainest answers -- score =
# the matching distance to the goals and the boxes still on their start
# cells, better = nearer, then more on start cells; cell = boxes on start
# cells; no advisors, so every macro costs one.  It meets the dragonfly's
# entries and slides down them.
# The pulls the corral rule strikes out, by index into @$moves; $last is the
# cell the last pull left its box on, undef at a root.
# was: mark_moves_when_corral (Festival.pm:8125)
sub struck_by_corral ($view, $moves, $last) {
    return {} if !defined $last;
    return {} if @{ (regions($view))[1] } == 1;
    my $work = { 'box' => $view->{'box'}, 'frozen' => {}, 'sok' => $view->{'sok'}, 'reach' => { %{ $view->{'reach'} } } };
    freeze_fixed($work);
    return {} if !corral_boxes($work);
    my %struck;
    my $reach = $view->{'reach'};
    foreach my $i (0 .. $#$moves) {
        my $m = $moves->[$i];
        if ($m->{'from'} == $last) {$struck{$i} = 1; next}
        my $after = apply($view, $m);
        next if $after->{'reach'}{$Sok0} and !grep {!$Start{$_}} keys %{ $after->{'box'} };
        $struck{$i} = 1 if !grep {($after->{'reach'}{$_} ? 1 : 0) != ($reach->{$_} ? 1 : 0)} @{ $N{$last} };
    }
    return \%struck;
} ## end sub struck_by_corral

# The search itself.  Writes every position it generates into $perimeter as
# the pull side, at the depth it was first generated at, and returns what it
# did: result (solved | exhausted | timeout), nodes, popped, expanded,
# dead (a node whose own pull failed the tests), struck, unmatched, met (a
# child the push side had already been to).
# was: dragonfly_search (Festival.pm:8237) with add_dragonfly_root (8081),
# dragonfly_get_board (8102), dragonfly_expand_node (8159),
# dragonfly_node_is_solved (8230), the heap (507-570),
# dragonfly_mark_visited_hashes (3688), dragonfly_update_perimeter (3704)
sub dragonfly_search ($limit, $perimeter, $opt = {}) {
    my $started = Time::HiRes::time();
    my @bases   = sort {$a <=> $b} keys %Start;
    my (@node, @heap);
    my %told = map {$_ => 0} qw(nodes popped expanded dead struck unmatched met);

    # the heap: nearest first, then most boxes on start cells, then the older
    my $ahead = sub ($i, $j) {
        my ($x, $y) = @node[$i, $j];
        return $x->{'dist'} < $y->{'dist'}     if $x->{'dist'} != $y->{'dist'};
        return $x->{'packed'} > $y->{'packed'} if $x->{'packed'} != $y->{'packed'};
        return $i < $j;
    };
    my $enqueue = sub ($i) {
        push @heap, $i;
        my $k = $#heap;
        while ($k > 0) {
            my $up = int(($k - 1) / 2);
            last if !$ahead->($heap[$k], $heap[$up]);
            @heap[$k, $up] = @heap[$up, $k];
            $k = $up;
        }
    };
    my $dequeue = sub () {
        return undef if !@heap;
        my $top  = $heap[0];
        my $last = pop @heap;
        if (@heap) {
            $heap[0] = $last;
            my $k = 0;
            while (1) {
                my ($l, $r, $first) = (2 * $k + 1, 2 * $k + 2, $k);
                $first = $l if $l < @heap and $ahead->($heap[$l], $heap[$first]);
                $first = $r if $r < @heap and $ahead->($heap[$r], $heap[$first]);
                last if $first == $k;
                @heap[$k, $first] = @heap[$first, $k];
                $k = $first;
            }
        }
        return $top;
    }; ## end $dequeue = sub

    # a node's position: the pulls back to the root replayed on the root's
    # boxes, the player where the last one left him, one flood
    my $view_of = sub ($i) {
        my @moves;
        my $e = $node[$i];
        while (!$e->{'root'}) {
            unshift @moves, $e->{'move'};
            $e = $node[$e->{'father'}];
        }
        my %box = %{ $e->{'root'}{'box'} };
        my $man = $e->{'root'}{'sok'};
        foreach my $m (@moves) {
            delete $box{ $m->{'from'} };
            $box{ $m->{'to'} } = 1;
            $man = $m->{'man'};
        }
        return set_reach({ 'box' => \%box, 'frozen' => {}, 'sok' => $man });
    }; ## end sub
    my $on_start = sub ($view) {scalar grep {$Start{$_}} keys %{ $view->{'box'} }};

    # the roots: the solved level, the player in each region of it
    foreach my $zone (@{ (regions({ 'box' => {%Goal}, 'frozen' => {} }))[1] }) {
        my $root = set_reach({ 'box' => {%Goal}, 'frozen' => {}, 'sok' => $zone->[0] });
        push @node,
            { 'root' => $root, 'depth' => 0, 'dist' => imagined_matching($root, \@bases), 'packed' => $on_start->($root) };
        $enqueue->($#node);
        my $key = poskey($root);
        $perimeter->{$key} = [1, 0] if !$perimeter->{$key} or $perimeter->{$key}[0] != 1;
    }
    my $result = 'exhausted';
    while (1) {
        if (Time::HiRes::time() - $started > $limit or run_aborted()) {$result = 'timeout'; last}
        my $i = $dequeue->() // last;
        my $e = $node[$i];
        $told{'popped'}++;

        # reached the start?  (a matching at no cost means every box on a
        # start cell; then the player has to be where he starts)
        if ($e->{'dist'} <= 0) {
            my $v = $view_of->($i);
            if ($v->{'reach'}{$Sok0} and !grep {!$Start{$_}} keys %{ $v->{'box'} }) {
                $result = 'solved';
                last;
            }
        }

        # the node's own pull put to the expensive tests, once, now
        if (!$e->{'root'} and picked_is_dead($view_of->($e->{'father'}), $e->{'move'}, 1, { %$opt, 'no_matching' => 1 })) {
            $told{'dead'}++;
            next;
        }
        my $v       = $view_of->($i);
        my ($moves) = possible_moves($v, 1, {});
        my @moves   = in_original_order(@$moves);
        next if !@moves;
        $told{'expanded'}++;
        my $struck = struck_by_corral($v, \@moves, $e->{'root'} ? undef : $e->{'move'}{'to'});

        # what is known of the children BEFORE any of them is written down;
        # of two macros to one position the first becomes a node (in the
        # original both do)
        my @child = map {
            my $after = apply($v, $_);
            my $key   = poskey($after);
            { 'after' => $after, 'key' => $key, 'seen' => $perimeter->{$key} }
        } @moves;
        my (@written, %made);
        foreach my $k (0 .. $#moves) {
            my $c = $child[$k];
            next if $c->{'seen'} and $c->{'seen'}[0] == 1;    # been here
            if ($struck->{$k}) {$told{'struck'}++; next}
            my $dist = imagined_matching($c->{'after'}, \@bases);
            if ($dist >= 1000000) {$told{'unmatched'}++; next}
            next if $made{ $c->{'key'} }++;
            if ($c->{'seen'}) {                               # the push side has been here: it goes first
                $dist = -2000 + $c->{'seen'}[1];
                $told{'met'}++;
            }
            push @node,
                {
                    'father' => $i,
                    'move'   => $moves[$k],
                    'depth'  => $e->{'depth'} + 1,
                    'dist'   => $dist,
                    'packed' => $on_start->($c->{'after'})
                };
            $enqueue->($#node);
            push @written, $c;
        } ## end foreach my $k (0 .. $#moves)
        foreach my $c (@written) {
            my $old = $perimeter->{ $c->{'key'} };
            next if $old and $old->[0] == 1 and $old->[1] <= $e->{'depth'} + 1;
            $perimeter->{ $c->{'key'} } = [1, $e->{'depth'} + 1];
        }
    } ## end while (1)
    $told{'nodes'} = scalar @node;
    return { %told, 'result' => $result, 'time' => Time::HiRes::time() - $started };
} ## end sub dragonfly_search

# The naive search's score: nearer to the goals first (every box matched to
# one goal), then more boxes still on their start cells.
# was: score_board (Festival.pm:6704) in NAIVE_SEARCH with
# set_naive_data_in_node (5418), and is_better_score (5991), its NAIVE branch
sub naive_score ($view) {
    return { 'near' => goals_matching($view), 'at_start' => scalar grep {$Start{$_}} keys %{ $view->{'box'} } };
}

sub naive_better ($s1, $s2) {
    return $s1->{'near'} < $s2->{'near'} if $s1->{'near'} != $s2->{'near'};
    return $s1->{'at_start'} > $s2->{'at_start'};
}

# was: strategy 7 of solve_with_alg (Festival.pm:8467), with
# packing_search_control (8404) giving the dragonfly three times the third
# and forward_search_control (8430) the rest in NAIVE_SEARCH
sub solve_dragonfly ($limit, $opt = {}) {
    my $started = Time::HiRes::time();
    my $elapsed = sub {Time::HiRes::time() - $started};
    my %perimeter;
    my $back = dragonfly_search(3 * int($limit / 3), \%perimeter, $opt);
    my %told = ('backward' => $back, 'perimeter' => scalar keys %perimeter);
    my $left = $limit - $elapsed->();
    return ('TIMEOUT', '', $elapsed->(), $back->{'popped'}, { %told, 'why' => 'no time for the forward search' }) if $left <= 0;
    my $found = feature_search(
        {
            'roots'     => [start_view()],
            'pull'      => 0,
            'perimeter' => \%perimeter,
            'limit'     => $left,
            'weighted'  => 1,
            'dead'      => sub ($view, $m) {picked_is_dead($view, $m, 0)},
            'solved'    => sub ($view) {!grep {!$Goal{$_}} keys %{ $view->{'box'} }},
            'score'     => \&naive_score,
            'better'    => \&naive_better,
            'cell'      => sub ($s) {"$s->{'at_start'}"},
            'advise'    => sub ($e) {[]},
            'moves'     => sub ($view, $state) {
                my $loose = ($state->{'found'} or $state->{'loose'}) ? 1 : 0;
                possible_moves($view, 0, { %$opt, 'corral' => $loose ? 0 : 1, 'inefficient' => $loose ? 0 : 1 });
            },
        }
    );
    $told{'forward'} = $found;
    my $doba   = $elapsed->();
    my $opened = $back->{'popped'} + $found->{'opened'};
    return ('TIMEOUT', '', $doba, $opened, \%told) if $found->{'result'} ne 'solved';
    my $steps = steps_of($found->{'line'}, { %$opt, 'corral' => 0, 'inefficient' => 0 });
    return ('SOLVED', $steps, $doba, $opened, \%told);
} ## end sub solve_dragonfly

# ---------------------------------------------------------------------------
# The mode GIRL: a learned value instead of a ladder of scores
# ---------------------------------------------------------------------------
#
# was: strategy 2 of solve_with_alg (Festival.pm:8467) -- packing_search and
# FESS in GIRL_SEARCH; the mode the drivers call FF_GIRL
#
# Every other mode judges a position by a LADDER of numbers, one deciding
# after the other.  GIRL boils the numbers down to ONE: a weighted sum of a
# few of them, normalised to the level -- how many boxes stand on goals, in
# how many pieces the floor is, how far the boxes are from the goals (by pulls
# from all the goals at once, as BASE's forward score measures it), and,
# pushing, how much of the plan is done and how far the boxes overlap the
# plan's cells -- with 0.95 to the power of the boxes still off the goals
# thrown in.  The weights are constants of the original (learned once, by its
# author, hence the name: Greedy-Is-Really-Learning, or so one supposes; the
# code says only "RL").  The value is what the tree is walked by -- see the
# greedy regime in feature_search -- both pulling and pushing.
#
# BACKWARD, a third of the time (pull_time), without bases: pull from the solved level;
# the plan is the line to the best-valued position of the tree -- or rather
# to the highest of its ancestors whose value is within a tenth of it.
#
# FORWARD, the rest: the value with the plan in it; no advisors; the tree is
# walked by value until it meets the backward tree's entries, and then slides.
#
# A box may be left standing on any cell of the plan, however wasteful that
# looks (was: used_in_plan).
my @GIRL_PULL_WEIGHTS = (-0.185353, -0.217472,  0.154112, 0.382115, 0.471096, 0.195508);
my @GIRL_PUSH_WEIGHTS = ( 0.468630, -0.177816, -0.233347, 0.052064, 0.326019, 0.164538, 0.348762, -0.141263);

# How far the boxes overlap the plan: walking the plan step by step, a box on
# the cell a step puts a box on counts one, a box on the cell a step takes a
# box from counts one off, and the best total on the way is the answer.
# was: overlap_score (Festival.pm:1061)
sub overlap ($view, $whole) {
    my $box = $view->{'box'};
    my ($score, $best) = (0, -1);
    foreach my $step (@$whole) {
        $score++       if $box->{ $step->{'to'} };
        $score--       if $step->{'from'} >= 0 and $box->{ $step->{'from'} };
        $best = $score if $score >= $best;
    }
    return @$whole ? $best : 0;
}

# The numbers the value is made of; pushing, with the plan ($plans->{'plan'}
# for good, $plans->{'whole'} as it was made).
# was: fill_girl_scores (Festival.pm:6490) with the common part of score_board
sub girl_score ($view, $pull, $ctx, $plans = undef) {
    my @boxes = keys %{ $view->{'box'} };
    my $far   = 0;
    $far += $ctx->{'near'}{$_} // 1000000 foreach @boxes;
    my $s = {
        'on_goals' => scalar(grep {$Goal{$_}} @boxes),
        'regions'  => scalar @{ (regions($view))[1] },
        'far'      => $far,
    };
    if (!$pull) {
        $s->{'packed'}  = packed($view, $plans->{'plan'});
        $s->{'overlap'} = overlap($view, $plans->{'whole'});
    }
    return $s;
} ## end sub girl_score

# The value: the weighted sum, in the original's order of terms.
# was: score_to_value with prepare_vector_of_basic_features (Festival.pm:5947)
sub girl_value ($s, $pull, $ctx) {
    my ($n, $inv, $norm, $gamma) = @$ctx{ 'n', 'inv', 'norm', 'gamma' };
    my @f =
        $pull
        ? ($s->{'on_goals'} * $inv, $s->{'regions'} * $inv, $s->{'far'} * $norm, $gamma->[$s->{'on_goals'}], $gamma->[$n], 1)
        : (
            $s->{'packed'} * $inv,
            $s->{'on_goals'} * $inv,
            $s->{'regions'} * $inv,
            $s->{'far'} * $norm,
            $s->{'overlap'} * $inv,
            $gamma->[$n - $s->{'on_goals'}],
            $gamma->[$n], 1
          );
    my $w   = $pull ? \@GIRL_PULL_WEIGHTS : \@GIRL_PUSH_WEIGHTS;
    my $sum = 0;
    $sum += $f[$_] * $w->[$_] foreach 0 .. $#f;
    return $sum;
} ## end sub girl_value

# The plan node of a backward tree: the best-valued position of the whole
# tree, and then the highest of its ancestors whose value comes within a
# tenth of that.
# was: find_best_RL_parking_node (Festival.pm:6449)
sub girl_plan_node ($tree, $ctx) {
    my ($node, $max);
    foreach my $e (grep {!$_->{'node'}{'dead'}} @$tree) {
        my $v = girl_value(score_of($e->{'node'}), 1, $ctx);
        ($node, $max) = ($e, $v) if !defined $max or $v > $max;
    }
    return undef if !$node;
    for (my $e = $node; $e; $e = $e->{'father'}) {
        $node = $e if girl_value(score_of($e->{'node'}), 1, $ctx) > $max - 0.1;
    }
    return $node;
}

# was: strategy 2 of solve_with_alg (Festival.pm:8467), with conclude_parking
# (6474) and setup_plan_features (8382) for GIRL
sub solve_girl ($limit, $opt = {}) {
    if (my $chain = chain_variant('girl')) {return solve_chain($limit, $opt, @$chain)}
    my $started = Time::HiRes::time();
    my $elapsed = sub {Time::HiRes::time() - $started};
    my %perimeter;
    my $ctx     = $Girl_context;
    my $epsilon = keys(%Start) + 1;
    my $greedy  = sub ($pull) {{ 'value' => sub ($s) {girl_value($s, $pull, $ctx)}, 'epsilon' => $epsilon }};
    my $better  = sub ($pull) {sub ($s1, $s2) {girl_value($s1, $pull, $ctx) > girl_value($s2, $pull, $ctx)}};

    # ---- backward: pull, by value
    my (@known, @roots);
    foreach my $zone (@{ (regions({ 'box' => {%Goal}, 'frozen' => {} }))[1] }) {
        my $root = set_reach({ 'box' => {%Goal}, 'frozen' => {}, 'sok' => $zone->[0] });
        next if !@{ (possible_moves($root, 1, {}))[0] };
        push @known, $root;
        push @roots, $root if !start_is_dead($root);
    }
    return ('FAILED', '', 0, 0, { 'why' => 'nothing can be pulled off the goals' }) if !@roots;
    my $back = feature_search(
        {
            'roots'     => \@roots,
            'known'     => \@known,
            'pull'      => 1,
            'perimeter' => \%perimeter,
            'limit'     => pull_time($limit),
            'weighted'  => 1,
            'greedy'    => $greedy->(1),
            'moves'     => sub ($view, $state) {possible_moves($view, 1, {})},
            'dead'      => sub ($view, $m) {picked_is_dead($view, $m, 1)},
            'solved'    => sub ($view) {$view->{'reach'}{$Sok0} and !grep {!$Start{$_}} keys %{ $view->{'box'} }},
            'score'     => sub ($view) {girl_score($view, 1, $ctx)},
            'better'    => $better->(1),
            'cell'      => sub ($s) {"$s->{'on_goals'},$s->{'regions'}"},
            'advise'    => sub ($e) {[]},
        }
    );
    my $opened = $back->{'opened'};
    my %told   = ('backward' => $back);
    my $node   = girl_plan_node($back->{'tree'}, $ctx)
        or return ('FAILED', '', $elapsed->(), $opened, { %told, 'why' => 'could not find a packing order' });
    my @line;
    for (my $e = $node; $e; $e = $e->{'father'}) {unshift @line, $e}
    my $whole = plan_of(\@line);
    my $plan  = plan_for_good($whole);
    my %keep  = map {$_->{'to'} => 1} @$whole;
    @told{ 'plan', 'perimeter' } = ($plan, scalar keys %perimeter);

    # ---- forward: push, by value, with the plan
    my $left = $limit - $elapsed->();
    return ('TIMEOUT', '', $elapsed->(), $opened, { %told, 'why' => 'no time for the forward search' }) if $left <= 0;
    my $found = feature_search(
        {
            'roots'     => [start_view()],
            'pull'      => 0,
            'perimeter' => \%perimeter,
            'limit'     => $left,
            'weighted'  => 1,
            'greedy'    => $greedy->(0),
            'dead'      => sub ($view, $m) {picked_is_dead($view, $m, 0)},
            'solved'    => sub ($view) {!grep {!$Goal{$_}} keys %{ $view->{'box'} }},
            'score'     => sub ($view) {girl_score($view, 0, $ctx, { 'plan' => $plan, 'whole' => $whole })},
            'better'    => $better->(0),
            'cell'      => sub ($s) {"$s->{'packed'},$s->{'regions'}"},
            'advise'    => sub ($e) {[]},
            'moves'     => sub ($view, $state) {
                my $loose = ($state->{'found'} or $state->{'loose'}) ? 1 : 0;
                possible_moves($view, 0,
                    { %$opt, 'keep' => \%keep, 'corral' => $loose ? 0 : 1, 'inefficient' => $loose ? 0 : 1 });
            },
        }
    );
    $opened += $found->{'opened'};
    $told{'forward'} = $found;
    my $doba = $elapsed->();
    return ('TIMEOUT', '', $doba, $opened, \%told) if $found->{'result'} ne 'solved';
    my $steps = steps_of($found->{'line'}, { %$opt, 'keep' => \%keep, 'corral' => 0, 'inefficient' => 0 });
    return ('SOLVED', $steps, $doba, $opened, \%told);
} ## end sub solve_girl

# ---------------------------------------------------------------------------
# The chain levels: snail and netlock
# ---------------------------------------------------------------------------
#
# The level's chain analysis ($Snail: which kind of chain level, its target,
# the chain) is in the record (Games::Sokoban::FestDev::snail_analysis); what
# is here is the modes' use of it.
#
# was: detect_snail_level and analyze_chain (Festival_Parser.pm:3718, 3673),
# set_snail_parameters and set_netlock_parameters (Festival.pm:2165, 2238),
# fill_snail_scores (2123), fill_netlock_scores (2217), is_better_score's
# SNAIL and NETLOCK branches (5991), packing_search_control's doubled time
# (8404)
#
# Two kinds of level get searches of their own -- not modes, but stand-ins
# that three of the modes turn into on them.  Both are told by PEELING: with a
# box on every goal that a box starts on, and one more on a goal in question,
# how many layers of boxes have to be pulled away before that one can be
# pulled at all (a box can be pulled when some neighbour and the cell beyond
# it are free; taking a layer away frees the boxes next to it, and those a
# cell beyond a free cell).  The goal that is hardest to reach is the TARGET.
# Twenty layers or more make a SNAIL: a long chain of goals wound into the
# level, the target at its far end, to be filled from the deep end out.  Ten
# or more make a NETLOCK: a net of goals, with a grid of cells in step with
# the target (same parity of row and column).  9 and 25 games of the 32 237.
#
# On such a level, pulling, BASE becomes the snail search (netlock search on
# a netlock level), MAXDIST2 the same with a plainer score, GIRL the netlock
# search with the value out; the backward third of the time is doubled; and
# the forward half of all three is HF's.  The searches are the big tree with
# these answers:
#
#   snail    the target empty first; then fewer boxes the player cannot touch;
#            fewer boxes hemmed in on six of their eight sides (the plainer
#            score leaves this out); then, with the target empty, the chain
#            filled farther from its deep end -- with a box on it, more "box,
#            gap, box" pairs (again left out by the plainer score); and last
#            the boxes matched farther from the goals.  No advisors, and the
#            weights off.
#   netlock  fewer pieces of floor; the target's box easier to peel (0 with
#            the target empty, a thousand when it cannot be peeled at all);
#            then more boxes on the grid and more that can be pulled -- or,
#            for the plan-following variants, "box, gap, box" pairs and boxes
#            on goals in their place.  The one advisor of the HF family.
#
# The scores' names in the original are borrowed from other modes'
# (out_of_plan, biconnect, hotspots ...); they are named here for what they
# count.
# Can a box on p be pulled somewhere: a neighbour free, and the cell beyond
# it free too?  (The player is not asked about.)
# was: simple_box_can_be_pulled (Festival_Parser.pm:3577)
sub pullable_somewhere ($box, $p) {
    foreach my $d (0 .. 3) {
        my $q = $N{$p}[$d];
        next if $Wall{$q} or $box->{$q};
        my $far = $N{$q}[$d];
        return 1 if !($Wall{$far} or $box->{$far});
    }
    return 0;
}

# How many layers away from being pullable every box is (-1: never), by
# peeling: the boxes that can be pulled now are layer 0 and are taken off;
# a box next to one taken off with the cell on its other side free, or a
# cell beyond a free cell from one, is the next layer; and so on.
# was: compute_pull_order (Festival.pm:2009)
sub peel_order ($box_in) {
    my %box     = %$box_in;
    my %order   = map  {$_ => -1} keys %box;
    my @current = grep {pullable_somewhere(\%box, $_)} sort {$a <=> $b} keys %box;
    my %seen    = map  {$_ => 1} @current;
    my $depth   = 0;
    while (@current) {
        foreach my $p (@current) {
            $order{$p} = $depth;
            delete $box{$p};
        }
        $depth++;
        my @next;
        foreach my $p (@current) {
            foreach my $d (0 .. 3) {
                my $q = $N{$p}[$d];
                next if !$box{$q} or $seen{$q};
                my $behind = $N{$p}[$d ^ 2];
                next if $Wall{$behind} or $box{$behind};
                $seen{$q} = 1;
                push @next, $q;
            }
            foreach my $d (0 .. 3) {
                my $q = $N{$p}[$d];
                next if $Wall{$q} or $box{$q};
                my $far = $N{$q}[$d];
                next if !$box{$far} or $seen{$far};
                $seen{$far} = 1;
                push @next, $far;
            }
        } ## end foreach my $p (@current)
        @current = @next;
    } ## end while (@current)
    return \%order;
} ## end sub peel_order

# The counts the two scores are made of.
# was: touched_boxes, count_101, unlikely_pattern, pullable_boxes,
# boxes_on_grid (Festival.pm:2064, 2077, 2091, 2000, 2207)
sub touched_boxes ($view) {
    my $reach = $view->{'reach'};
    return scalar grep {my $p = $_; grep {$reach->{$_}} @{ $N{$p} }} keys %{ $view->{'box'} };
}

sub box_gap_box ($box) {
    my $n = 0;
    foreach my $p (keys %$box) {
        foreach my $d (1, 2) {    # right, down
            my $q = $N{$p}[$d];
            next if $Wall{$q} or $box->{$q};
            $n++ if $box->{ $N{$q}[$d] };
        }
    }
    return $n;
}

sub hemmed_in ($box) {
    return scalar grep {my $p = $_; 6 <= grep {$Wall{$_} or $box->{$_}} @{ $N8{$p} }} keys %$box;
}

sub pullable_boxes ($box) {
    return scalar grep {pullable_somewhere($box, $_)} keys %$box;
}

# How far from the deep end the chain is filled: the first chain cell from
# the target out (the target itself not asked) that has no box, or the whole
# length.
# was: snail_packed (Festival.pm:2105)
sub snail_packed ($box) {
    my %empty = map {$Snail->{'dist'}{$_} => 1} grep {!$box->{$_}} keys %{ $Snail->{'dist'} };
    foreach my $i (1 .. $Snail->{'len'} - 1) {
        return $i if $empty{$i};
    }
    return $Snail->{'len'};
}

# was: fill_snail_scores (Festival.pm:2123) with set_max_dist_data_in_node
# (5394) for the matching; $alg 0 = BASE's, 1 = MAXDIST2's plainer score
sub snail_score ($view, $alg) {
    my $box = $view->{'box'};
    my $out = $box->{ $Snail->{'target'} } ? 1 : 0;
    return {
        'target_taken' => $out,
        'untouched'    => keys(%Start) - touched_boxes($view),
        'hemmed'       => $alg == 0            ? hemmed_in($box)   : 0,
        'packed'       => $out                 ? 0                 : snail_packed($box),
        'pairs'        => ($out and $alg == 0) ? box_gap_box($box) : 0,
        'far'          => goals_matching($view),
    };
}

# was: is_better_snail_score (Festival.pm:2141)
sub snail_better ($s1, $s2) {
    return $s1->{'target_taken'} < $s2->{'target_taken'} if $s1->{'target_taken'} != $s2->{'target_taken'};
    return $s1->{'untouched'} < $s2->{'untouched'}       if $s1->{'untouched'} != $s2->{'untouched'};
    return $s1->{'hemmed'} < $s2->{'hemmed'}             if $s1->{'hemmed'} != $s2->{'hemmed'};
    if ($s1->{'target_taken'} == 0) {
        return $s1->{'packed'} > $s2->{'packed'} if $s1->{'packed'} != $s2->{'packed'};
    }
    else {
        return $s1->{'pairs'} > $s2->{'pairs'} if $s1->{'pairs'} != $s2->{'pairs'};
    }
    return $s1->{'far'} > $s2->{'far'};
}

# was: netlock_score and fill_netlock_scores (Festival.pm:2194, 2217); $alg
# 0 = BASE's, 1 = MAXDIST2's, 2 = GIRL's on a netlock level, 3 = GIRL's on a
# snail level
sub netlock_score ($view, $alg) {
    my $box    = $view->{'box'};
    my $target = $Snail->{'target'};
    my $peel   = 0;
    if ($box->{$target}) {
        my $layers = peel_order($box)->{$target};
        $peel = $layers == -1 ? 1000 : $layers;
    }
    my $on_grid = scalar grep {$Snail->{'grid'}{$_}} keys %$box;
    my ($rooms, $imagine) = ($on_grid, 0);
    if ($peel == 0) {
        $imagine = pullable_boxes($box);
    }
    else {
        ($rooms, $imagine) = (box_gap_box($box), $on_grid) if $alg == 0;
        $imagine = pullable_boxes($box) if $alg == 2;
    }
    if ($alg == 3) {
        $rooms   = scalar grep {$Goal{$_}} keys %$box;
        $imagine = box_gap_box($box);
    }
    return { 'regions' => scalar @{ (regions($view))[1] }, 'peel' => $peel, 'rooms' => $rooms, 'imagine' => $imagine };
} ## end sub netlock_score

# was: is_better_score (Festival.pm:5991), the NETLOCK branch
sub netlock_better ($s1, $s2) {
    return $s1->{'regions'} < $s2->{'regions'} if $s1->{'regions'} != $s2->{'regions'};
    return $s1->{'peel'} < $s2->{'peel'}       if $s1->{'peel'} != $s2->{'peel'};
    return $s1->{'rooms'} > $s2->{'rooms'}     if $s1->{'rooms'} != $s2->{'rooms'};
    return $s1->{'imagine'} > $s2->{'imagine'};
}

# Which stand-in a mode turns into on this level: [kind, alg, weighted], or
# nothing on an ordinary level.
# was: set_snail_parameters and set_netlock_parameters (Festival.pm:2165, 2238)
sub chain_variant ($mode) {
    my $kind = $Snail ? $Snail->{'kind'} : '';
    return undef if !$kind;
    my %table = (
        'snail'   => { 'base' => ['snail',   0, 0], 'maxdist2' => ['snail',   1, 0], 'girl' => ['netlock', 3, 1] },
        'netlock' => { 'base' => ['netlock', 0, 1], 'maxdist2' => ['netlock', 1, 1], 'girl' => ['netlock', 2, 1] },
    );
    return $table{$kind}{$mode};
}

# The stand-in itself: the backward search of the kind, for two thirds (pull_time) of
# the time, then HF's forward half.
# was: packing_search_control (Festival.pm:8404) with the search type turned,
# and forward_search_control (8430) turning the forward search into HF
sub solve_chain ($limit, $opt, $kind, $alg, $weighted) {
    my $started = Time::HiRes::time();
    my %perimeter;
    my @roots;
    foreach my $zone (@{ (regions({ 'box' => {%Goal}, 'frozen' => {} }))[1] }) {
        my $root = set_reach({ 'box' => {%Goal}, 'frozen' => {}, 'sok' => $zone->[0] });
        push @roots, $root if @{ (possible_moves($root, 1, {}))[0] } and !start_is_dead($root);
    }
    return ('FAILED', '', 0, 0, { 'why' => 'nothing can be pulled off the goals' }) if !@roots;
    my $snail = $kind eq 'snail';
    my $back  = feature_search(
        {
            'roots'     => \@roots,
            'pull'      => 1,
            'perimeter' => \%perimeter,
            'limit'     => pull_time($limit, 2),
            'weighted'  => $weighted,
            'moves'     => sub ($view, $state) {possible_moves($view, 1, {})},
            'dead'      => sub ($view, $m) {picked_is_dead($view, $m, 1)},
            'solved'    => sub ($view) {$view->{'reach'}{$Sok0} and !grep {!$Start{$_}} keys %{ $view->{'box'} }},
            'score'  => $snail ? sub ($view) {snail_score($view, $alg)} : sub ($view) {netlock_score($view, $alg)},
            'better' => $snail ? \&snail_better                         : \&netlock_better,
            'cell'   => $snail ? sub ($s) {"$s->{'packed'}"}            : sub ($s) {"$s->{'peel'},$s->{'regions'},$s->{'rooms'}"},
            'advise' => $snail ? sub ($e) {[]} : sub ($e) {advise_best_son($e, \&netlock_better, \%Goal_hole)},
        }
    );
    return hf_forward($limit, $started, \%perimeter, $back, $opt);
} ## end sub solve_chain

# ---------------------------------------------------------------------------
# The face: the eight modes by the names the drivers use
# ---------------------------------------------------------------------------
#
# was: modes and solve (Festival.pm:8295, 8518) with solve_with_alg (8467)
# and its two tables of search types; the order is the original's %FF_MODE.
# The names are the original's with E_ in place of FF_ (USER 2026-09-30):
# they end up in firstbet.method, and there a solution of this engine must not
# pass for one of Festival.pm's.  Which mode turns into which stand-in on a
# snail or a netlock level is each mode's own business (chain_variant).
#
# run() takes the level out of its packed record (take_level) and returns
# what every mode returns: reason, the steps, seconds, positions opened, and
# what the mode has to tell about its run.  The seconds are the search's own:
# taking the level is not in them.
#
# solve() is the same in the shape of every engine here -- the gameid first,
# ($reason, $path, $seconds, $positions) back, what the mode had to say in
# $LastFail, blok from $BLOK -- and under the run control: a run stopped from
# outside reports IGNORE or MEMCAP instead of the TIMEOUT its search saw.
my @MODES = qw(E_BASE E_MAXDIST2 E_GIRL E_HF E_BICON E_MAXDIST E_REV E_DRAGONFLY);
my %SOLVE = (
    'E_BASE'      => \&solve_base,
    'E_MAXDIST2'  => \&solve_maxdist2,
    'E_GIRL'      => \&solve_girl,
    'E_HF'        => \&solve_hf,
    'E_BICON'     => \&solve_bicon,
    'E_MAXDIST'   => \&solve_maxdist,
    'E_REV'       => \&solve_rev,
    'E_DRAGONFLY' => \&solve_dragonfly,
);
sub modes () {return @MODES}

# THE STEPS OF A SOLUTION ARE WRITTEN AGAIN FROM THEIR PUSHES before they leave
# (1.03, USER 2026-10-12): a solution is a row of elementary pushes -- the
# player walks to a box and pushes it one cell -- whatever a search calls a
# position and however far a macro carries a box, and every engine of the
# project passes its path through one procedure while the level is still in
# memory (Games::Sokoban::Path): the pushes up to the one after which every
# goal is under a box; pushes that only take the boxes away and bring them
# back left out where that makes the path shorter; a shortest walk to each.
# steps_of() walks the shortest way already.  What this adds, on the 34 053
# solved paths of matrix fm-1:
#   * THE END (456 paths).  A search here asks "solved?" of the position a
#     macro ends in and of no position the macro passes through, and the last
#     macro of a solution is often the one that leads into the pull search's
#     tree -- the box goes over its goal and round, to come to it from the side
#     that leaves the player in the part of the floor the pull search began in.
#     The level is solved the moment the box first stands on its goal; in all
#     456 that one box alone moves afterwards.
#   * A BOX CARRIED AWAY AND BROUGHT BACK (1 174 paths): two macros, or a
#     macro passing through a position the line of play had been in, give the
#     same boxes twice -- the tree knows positions only where a macro ends.
# No search is touched.
sub run ($blob, $limit, $mode, $opt = {}) {
    my $run = $SOLVE{$mode} or Carp::confess("run: no such mode '$mode' (" . join(' ', @MODES) . ')');
    take_level($blob);
    my ($reason, $steps, @rest) = $run->($limit, $opt);
    $steps = Games::Sokoban::Solver::Path::rebuilt(
        'path'   => $steps,
        'width'  => $Width,
        'floor'  => [keys %Floor],
        'goals'  => [keys %Goal],
        'boxes'  => [keys %Start],
        'player' => $Sok0,
        )
        if $reason eq 'SOLVED';
    return ($reason, $steps, @rest);
} ## end sub run

sub solve ($gameid, $blob, $limit, $mode) {
    ($Abort, $Next_poll, $Tick, $LastFail) = ('', 0, 0, '');
    my ($reason, $steps, $doba, $opened, $told) = run($blob, $limit, $mode, { 'blok' => $BLOK });
    return ('SOLVED', $steps, $doba, $opened) if $reason eq 'SOLVED';

    # stopped from outside: whatever the mode says about why it stopped short
    # (FF_REV: "perimeter not reached") is only the stop seen from inside
    return ($Abort, $steps, $doba, $opened) if $Abort;
    $LastFail = $told->{'why'} // '';
    return ($reason, $steps, $doba, $opened);
}
1;
__END__

=head1 NAME

Games::Sokoban::Solver::Fest - the Festival search rewritten in plain Perl: eight strategies over a prepared level record

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Fest ();

    my @modes = Games::Sokoban::Solver::Fest::modes();     # E_BASE E_BICON E_MAXDIST E_MAXDIST2 E_GIRL E_HF E_REV E_DRAGONFLY
    my ($reason, $path, $seconds, $positions)
        = Games::Sokoban::Solver::Fest::solve($label, $analysis_blob, 60, 'E_REV');

=head1 DESCRIPTION

Yaron Shoham's Festival solver, written again in Perl with positions and
views as hashes per cell instead of the C transcription's flat arrays (that
transcription is L<Games::Sokoban::Solver::Festival>). The same eight
strategies, each dividing its budget between a pull search from the goals, a
packing search and a forward search; slower than the transcription by a
factor of two to four, and in the Sokoban project's campaigns it solved
levels the transcription did not.

The level comes in as the record L<Games::Sokoban::Solver::Fest::Analysis>
packs (C<analysis_record>); the engine reads nothing else and loads no other
module for it. This is Games::Sokoban::Fest 1.03 of the Sokoban project with
the modules it leans on rewired; the search is untouched.

=head1 INTERFACE

=head2 modes

The eight mode names, C<E_BASE E_BICON E_MAXDIST E_MAXDIST2 E_GIRL E_HF E_REV
E_DRAGONFLY>.

=head2 solve

    my ($reason, $path, $seconds, $positions) = solve($label, $analysis_blob, $limit, $mode);

The shape every engine of the distribution has. C<$reason> is C<SOLVED>,
C<TIMEOUT>, C<FAILED> (the mode walked away with budget in hand; C<$LastFail>
says why), C<IGNORE> or C<MEMCAP>. A record stamped by other analysis code
is refused with a death. The path is written again from its pushes before it
is returned.

=head2 run

    my ($reason, $steps, $seconds, $positions, \%told) = run($analysis_blob, $limit, $mode, \%opt);

The same search with everything the mode has to tell in C<%told>; C<%opt> may
carry C<blok> (see below).

=head2 Run control

    our $BLOK       1 = the Parser's deadlock table is tested in every mode as well (the program sets 1)
    our $MAX_GB     stop as MEMCAP over this many GiB of the whole machine; 0 = off
    our $RACE_FLAG  a hash reference, label => true: the level is won elsewhere
    our $RACE_GID   the label this solve is running
    our $LastFail   why the last solve stopped short, in the mode's words ('' when it has nothing to say)

The engine prints nothing.

=head1 CAVEATS

A mode divides its limit between its phases, so the result at a short limit
depends on the clock: the same level and mode can come out differently run to
run. The analysis of a large level takes seconds (about five on the largest
levels measured).

=head1 SEE ALSO

L<Games::Sokoban::Solver>, L<Games::Sokoban::Solver::Fest::Analysis>,
L<Games::Sokoban::Solver::Festival>, L<Games::Sokoban::Solver::Portfolio>.

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>. The Festival algorithm is
Yaron Shoham's (Festival 3.1).

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
