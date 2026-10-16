package Games::Sokoban::Solver::Fest::Analysis;

# THE LEVEL, PREPARED FOR Games::Sokoban::Solver::Fest -- all eight modes of it.
#
# prepare($gm) takes the Parser's analysis hash and works out everything the
# engine needs to know about the level before any search starts, and returns
# it as ONE RECORD (analysis_record packs it into the string the engine takes):
#
#   * the maps and tables that can be read off the shape (geometry() and the
#     builders under it -- what Parser.pm used to be),
#   * the three things only a search can find, plus the chain analysis
#     (search_analysis): the forbidden pairs, the forbidden pull pairs, the
#     envelope rules, the snail/netlock verdict,
#   * and the facts about the level that single modes used to work out for
#     themselves at every run (install): how many goals a blocker takes away
#     (%Blocks, BASE), how far every cell is from the goals (%Goals_away, the
#     HF family, BASE, REV), from which cells a box reaches the goals
#     (%Goals_near, REV, GIRL), GIRL's constants ($Girl_context), and the joins
#     between rooms on the empty level ($Room_links0).
#
# The record is SELF-CONTAINED: it carries what it takes from the Parser's hash
# as well, so the engine reads nothing but it (Fest::take_level) and does not
# load this module at all: the role the Parser has for Firstbet and the
# optimal solver.
#
# The questions about positions that the analysis searches ask -- the moves of
# a position, the freezing, the dead-macro tests -- are COPIES of the engine's
# own, without their comments, which are there.
#
# Lineage: Games::Sokoban::FestDev 1.00 of the Sokoban project.
#
# Two facts make the model possible, both verified against the live database:
#
#   * Festival's rectangle and this project's %Game blob are ONE coordinate
#     space -- same width/height, same cell numbers for boxes, goals and the
#     player, and Festival's set of active cells ("inner") is exactly the key
#     set of %Game{cg}, with identical adjacency.
#   * No level has a floor cell on the rim of its rectangle (32 237 games, not
#     one).  So every neighbour of a floor cell, diagonal ones included, is a
#     cell of the rectangle, and a neighbour is ALWAYS A NUMBER: either a floor
#     cell or a wall cell, never "nothing".  geometry() refuses a level that
#     breaks this rather than letting anything downstream wonder.
use v5.42;
use Carp           ();
use Compress::Zlib ();
use List::Util ('min');
use Scalar::Util                    ();
use Storable                        ();
use Time::HiRes                     ();
use Games::Sokoban::Solver::Data    ();
use Games::Sokoban::Solver::Munkres ();
our $VERSION = '0.01';

# The level being prepared, one variable per key of the record (record()
# gathers them).  From the Parser's hash as it stands: %Blok %Cg %Cm %Floor
# %Goal %Start $Sok0 $Width.  From geometry(): %Cp %D %Goal_hole %Impossible
# %N %N8 %Pattern %Pattern_at %Room @Room_area %Side %Tunnel_pull %Tunnel_push
# %Walk %Wall.  From search_analysis(): %Mpdb %Pull_mpdb @Envelope $Snail.
# Worked out by install(): %Blocks %Goals_away %Goals_near $Girl_context
# $Room_links0.
my (
    %Blocks,      %Blok,        %Cg,         %Cm,         %Cp,         %D,    %Floor,
    %Goal,        %Goal_hole,   %Goals_away, %Goals_near, %Impossible, %Mpdb, %N,
    %N8,          %Pattern,     %Pattern_at, %Pull_mpdb,  %Room,       %Side, %Start,
    %Tunnel_pull, %Tunnel_push, %Walk,       %Wall
   );
my (@Envelope, @Room_area);
my ($Girl_context, $Room_links0, $Snail, $Sok0, $Width);

# What the copies of the engine's subs keep between calls while the analysis
# searches run: the same caches Fest.pm keeps, cleared by install().
my (%Base_landing, %Dead_cache, %Far_pulls, @Stuck);

# The stamp on a record.  Bump it when what a record holds changes shape or
# meaning -- and the engine's RECORD_STAMP with it: Fest::take_level refuses a
# record with another one.  ('fest analysis 1' was the four products of the
# search alone.)
our $ANALYSIS_STAMP = 'fest record 2';

# Subs are named for what they answer, not for what the C transcription called
# them.  Where a sub replaces one of Festival's, its comment carries a
#
#     # was: <old name> (Festival.pm:NNNN)
#
# line, so that anything here can be read against the original it came from.
#
# Direction order is Festival's own: 0 up, 1 right, 2 down, 3 left, and the
# ring of eight runs clockwise from up, so direction d sits at ring index 2d
# and the odd indices are the diagonals.
# ---------------------------------------------------------------------------
# The level, read off its shape
# ---------------------------------------------------------------------------
#
# geometry() does not copy what %Game already holds; install() takes that
# from the %Game blob as it stands, and record() puts the two side by side:
#
#   cg{p}         [the floor cells next to p] -- the walk graph; its keys ARE
#                 the floor.  Every question about WALKING goes through it and
#                 never meets a wall, exactly as in Firstbet
#   cm{box}{to}   = the cell the player pushes from -- only pushes worth making
#   goal, baggage, player, w
#   blok{from}{to}  the deadlock table of single pushes, as bit strings
#
# so that the two engines read one and the same level.
#
# What geometry() returns is what %Game does not have:
#
#   n{p}          [4 neighbours of floor cell p] by direction, each a floor or
#                 a wall cell
#   n8{p}         [8 neighbours] by direction, same.  These two are for the
#                 questions about a SHAPE -- a corner, a full 2x2 block, a
#                 diagonal -- where a wall is part of what is being asked
#   wall{q}       every wall cell that touches a floor cell, corners included
#   cp{box}{to}   = the cell the player steps back onto when pulling
#   side{p}{q}    with a box on p, WHICH REGION the floor neighbour q is in
#   d{from}{to}   pushes to bring a box from one cell to another, empty board
#   walk{from}{to}  player steps between two cells, boxes ignored
#   impossible{p}   a box can never usefully stand on p
#
# was: init_board_geometry (Festival.pm:317) plus init_inner and
# init_index_x_y (Festival_Parser.pm:608, 625).  The third of those has no
# successor at all: it built the dense renumbering of the active cells, and
# that second numbering is exactly the ballast this rewrite is removing.
sub geometry ($gm) {
    my %g;
    my ($w, $h) = ($gm->{'w'}, $gm->{'h'});
    Carp::confess('geometry: no level dimensions') if !$w or !$h;
    $g{'w'} = $w;
    $g{'h'} = $h;

    # The active cells.  %Game{cg} is the player-walk graph, so its keys are
    # every cell the player can ever stand on -- which is what Festival calls
    # the inner cells.
    $g{'floor'} = { map {$_ => 1} keys %{ $gm->{'cg'} } };
    $g{'cg'}    = $gm->{'cg'};
    $g{'cm'}    = $gm->{'cm'} // {};

    # Neighbours.  This is the only place in the whole model where the row
    # stride is used.  The rim test is what makes plain arithmetic safe: a
    # floor cell off the rim has all eight neighbours inside the rectangle.
    my @step4 = (-$w, 1, $w, -1);
    my @step8 = (-$w, -$w + 1, 1, $w + 1, $w, $w - 1, -1, -$w - 1);
    foreach my $p (keys %{ $g{'floor'} }) {
        my ($y, $x) = (int($p / $w), $p % $w);
        Carp::confess("geometry: floor cell $p on the rim of the rectangle")
            if $y == 0
            or $x == 0
            or $y == $h - 1
            or $x == $w - 1;
        $g{'n'}{$p}  = [map {$p + $_} @step4];
        $g{'n8'}{$p} = [map {$p + $_} @step8];
        foreach my $q (@{ $g{'n8'}{$p} }) {
            $g{'wall'}{$q} = 1 if !$g{'floor'}{$q};
        }
    }
    $g{'goal'}  = { map {$_ => 1} @{ $gm->{'goal'} } };
    $g{'start'} = { map {$_ => 1} @{ $gm->{'baggage'} } };
    $g{'sok0'}  = $gm->{'player'};
    pull_map(\%g);
    sides(\%g);
    distances(\%g);
    impossible_cells(\%g);
    tunnels(\%g);
    goal_holes(\%g);
    rooms(\%g);
    pattern_placements(\%g);

    # the working copies of what %Game holds: used above, handed to nobody
    delete @g{ 'w', 'h', 'floor', 'cg', 'cm', 'goal', 'start', 'sok0' };
    return \%g;
} ## end sub geometry

# FOUR PRODUCTS OF THE ANALYSIS ARE FOUND BY SEARCHING, not by looking at the
# level: the original decides them with a small best-first search over the
# engine's own move generator, and so does search_analysis() below -- seconds
# a game where everything else in this module is a few hundredths.  Their
# shapes, cell-keyed:
#
#   mpdb{a}{b}, pull_mpdb{a}{b}   two cells that may never BOTH hold a box
#                                 (kept in both directions)
#   envelope                      [{box => [cells], allowed => {cells}}, ...]:
#                                 if something stands on every one of `box`
#                                 and the player's region lies inside `allowed`,
#                                 the boxes on those cells can never move again
#
# was: @Mpdb_list, @Pull_mpdb_list (pairs of dense indices) and
# @New_envelope_patterns (one byte board per pattern: BOX on the cells, SOKOBAN
# on the allowed region)
# The record (record() below) as the engine takes it: compressed.  Fest::
# take_level unpacks it with thaw(uncompress(...)) and checks the stamp itself.
sub analysis_record ($record) {
    return Compress::Zlib::compress(Storable::nfreeze($record));
}

# The deadlock pattern library, laid over the level once.
#
# Festival carries 116 push patterns and 60 pull patterns, each a window of
# 3x4, 4x3 or 4x4 cells in which some cells are "don't care" and the rest must
# hold exactly one thing.  Only four things ever occur:
#
#     wall          a wall -- or a frozen box, which answers as one
#     box           a box that is not frozen and not on a goal
#     void          (push) an empty cell, not a goal, the player CANNOT reach
#     reach         (pull) an empty cell, not a goal, the player CAN reach
#
# The original slides every window over the board around the box that has just
# moved and compares bytes.  Most of that comparison is about the level and
# not about the position: a window whose "wall" falls on a wall, whose "box"
# falls on floor that is not a goal, and so on.  So it is done here, once: the
# library is laid over the level at every place it fits, the walls drop out of
# it, and what is handed on is a list of PLACEMENTS that mention floor cells
# only --
#
#     {box => [cells], void => [cells], frozen => [cells]}     push
#     {box => [cells], reach => [cells], frozen => [cells]}    pull
#
# "if all of these hold boxes, all of these are empty and out of his reach, and
# all of these are frozen, the position is dead" -- together with
# pattern_at{push|pull}{cell}, the placements whose window covers that cell,
# which is the question the engine asks after moving a box there.  It is the
# same turn the project's own blok table takes.
#
# `frozen` is the price of being exact: a pattern wall may fall on a FLOOR cell
# and still match, if a frozen box stands there.  Measured over 60 games and
# 11 550 candidate moves, 111 of 115 matches needed no frozen cell at all, 4
# needed one or two, none more -- while placements that would need three or
# more are 60 % of the list.  They are kept: the original is the oracle.
#
# (For the pull patterns they were once dropped, on the grounds that a pull
# board is never frozen.  The pull searches of the game are not -- but the
# distance test pulls back from the solved level on a board that HAS frozen
# cells, and the original's patterns see them as walls.  Found by the gate of
# that test, stage 13d.)
#
# was: prepare_pattern_offsets (Festival.pm:8311), check_deadlock_pattern
# (2510) and the sliding half of check_all_patterns (2536)
my $Library;    # the frozen tables; level-independent, so read once per process

sub pattern_placements ($g) {
    $Library //= Games::Sokoban::Solver::Data::load('fest_patterns.stor');
    my ($w, $h, $floor, $goal) = @$g{ 'w', 'h', 'floor', 'goal' };
    foreach my $kind (['push', 'patterns', 'void'], ['pull', 'pull_patterns', 'reach']) {
        my ($mode, $table, $empty) = @$kind;
        my (@placed, %at);
        foreach my $pt (@{ $Library->{$table} }) {
            foreach my $y (0 .. $h - 1 - $pt->{'maxcy'}) {
            WINDOW: foreach my $x (0 .. $w - 1 - $pt->{'maxcx'}) {
                    my %need = ('box' => [], $empty => [], 'frozen' => []);
                    foreach my $c (@{ $pt->{'cells'} }) {
                        my ($dy, $dx, $what) = @$c;
                        my $q = ($y + $dy) * $w + $x + $dx;
                        if ($what == 1) {    # wall
                            push @{ $need{'frozen'} }, $q if $floor->{$q};
                            next;
                        }
                        Carp::confess("pattern library: unknown cell byte $what in a $mode pattern")
                            if $what != 2 and $what != ($mode eq 'push' ? 0 : 8);
                        next WINDOW if !$floor->{$q} or $goal->{$q};
                        push @{ $need{ $what == 2 ? 'box' : $empty } }, $q;
                    }
                    push @placed, \%need;

                    # the cells of the window, which may hang over the edge of
                    # the rectangle on the side where the pattern has nothing
                    foreach my $yy ($y .. $y + $pt->{'y'} - 1) {
                        foreach my $xx ($x .. $x + $pt->{'x'} - 1) {
                            next if $yy >= $h or $xx >= $w;
                            my $q = $yy * $w + $xx;
                            push @{ $at{$q} }, $#placed if $floor->{$q};
                        }
                    }
                } ## end WINDOW: foreach my $x (0 .. $w - 1 ...)
            } ## end foreach my $y (0 .. $h - 1 ...)
        } ## end foreach my $pt (@{ $Library...})
        $g->{'pattern'}{$mode}    = \@placed;
        $g->{'pattern_at'}{$mode} = \%at;
    } ## end foreach my $kind (['push', ...])
    return;
} ## end sub pattern_placements

# tunnel_push{p}, tunnel_pull{p} = a box should not be LEFT STANDING on p.
#
# A tunnel is a straight run of two or more floor cells with a wall on both
# sides of every one of them.  A box in a tunnel can only go on the way it
# came or back, and nothing can pass it, so stopping there is never better
# than pushing on to the far end: the engine throws away every move that ends
# inside one.  The one cell it may be worth stopping on is the FIRST cell of
# the run (the left end, or the top end), and that only when there is a reason
# to be in the tunnel at all -- a goal somewhere in it when pushing, a box
# that starts in it when pulling.
#
# was: set_forbidden_tunnel (Festival_Parser.pm:3578), two whole-rectangle
# sweeps with the row stride written into every line.  Here a cell is in a
# horizontal tunnel when the cells above and below it are walls, the run is
# walked along the neighbour map, and the two directions are one loop.
#
# That only the first cell is ever excused, and not the last or the cell with
# the goal on it, reads like an accident of the original's loop rather than a
# decision.  It is reproduced, because the stored analysis is the oracle.
sub tunnels ($g) {
    my ($floor, $wall, $n) = @$g{ 'floor', 'wall', 'n' };
    $g->{'tunnel_push'} = {};
    $g->{'tunnel_pull'} = {};

    # $across: the two directions the walls are in; $back, $on: along the run
    foreach my $dir ([0, 2, 3, 1], [3, 1, 0, 2]) {
        my ($side1, $side2, $back, $on) = @$dir;
        my $in_tunnel = sub ($p) {$floor->{$p} and $wall->{ $n->{$p}[$side1] } and $wall->{ $n->{$p}[$side2] }};
        foreach my $p (keys %$floor) {
            next if !$in_tunnel->($p) or $in_tunnel->($n->{$p}[$back]);
            my @run = ($p);
            push @run, $n->{ $run[-1] }[$on] while $in_tunnel->($n->{ $run[-1] }[$on]);
            next if @run < 2;
            $g->{'tunnel_push'}{$_} = $g->{'tunnel_pull'}{$_} = 1 foreach @run;
            delete $g->{'tunnel_push'}{$p} if !grep {$g->{'goal'}{$_}} @run;
            delete $g->{'tunnel_pull'}{$p} if !grep {$g->{'start'}{$_}} @run;
        }
    }
    return;
} ## end sub tunnels

# goal_hole{p}   = a goal at the bottom of a dead end: walls on three sides.
#                  A box pushed in can never come out and blocks nothing, so
#                  such a goal can be filled at any time -- and once it is, it
#                  is as good as wall, which may make the goal in front of it
#                  the bottom of the dead end in its turn.  So the set is found
#                  by filling and looking again.
#
# was: mark_target_holes and is_square_a_target_hole (Festival_Parser.pm:
# 2132-2170), $target_holes.  The original also marks $semi_holes, goals in a
# corner (mark_semi_holes); nothing in the engine reads them, so they are not
# worked out here.
#
# %Game has a relative of the first: its `hole` is a dead-end corridor with
# goals in it, five cells or longer, kept with a table of the orders in which
# it may be filled.  This one is about single goal cells and has no minimum
# length.  The two overlap where a hole's goals are packed against its blind
# end: measured over 120 games with a hole, 629 of the 665 goals in holes are
# goal_hole cells, and in 121 holes of 145 every goal is.  The rest are goals
# with plain floor between them and the end of the hole, which a box can be
# pushed past -- no goal hole, and the very case the hole's table is for.
sub goal_holes ($g) {
    my ($goal, $wall, $n) = @$g{ 'goal', 'wall', 'n' };
    my %filled;
    my $changed = 1;
    while ($changed) {
        $changed = 0;
        foreach my $p (grep {!$filled{$_}} keys %$goal) {
            next if 3 != grep {$wall->{$_} or $filled{$_}} @{ $n->{$p} };
            $filled{$p} = 1;
            $changed = 1;
        }
    }
    $g->{'goal_hole'} = \%filled;
    return;
} ## end sub goal_holes

# room{p} = the number of the room cell p belongs to.  Festival's idea of a
# room is OPEN FLOOR: a 2x2 block of floor is a piece of room, blocks that
# share a side make one room, and a block with no such neighbour is not a room
# at all.  Everything else -- corridors, corners, the one-wide bits -- belongs
# to no room.  Boxes and goals are not looked at.
#
# room_area{t} = the cells of room t and the floor cells right beside them:
# the room with the mouths of its corridors.
#
# Where two rooms touch only at a corner, the cell they would share belongs to
# neither.  More than 70 rooms and the level is treated as having none.
#
# was: new_mark_rooms (Festival_Parser.pm:3214), $rooms_board and $rooms_num;
# init_rooms_deadlock (5246), @room_with_corridors and @room_size.  The
# original found the blocks by their top-left corner cell and numbered the
# rooms by flooding a board of those corners; the same is done here with the
# corner cells as a set, and the numbering comes out the same because it goes
# by the smallest corner cell.
#
# %Game has nothing like it.  Firstbet's FEATURE mode has rooms of its own,
# cut at the doorways (cells whose removal splits the floor); the two are
# different ideas and are not interchangeable.
sub rooms ($g) {
    my ($floor, $n, $n8) = @$g{ 'floor', 'n', 'n8' };
    $g->{'room'}      = {};
    $g->{'room_area'} = [];

    # the top-left cells of the 2x2 blocks of floor, less the lonely ones
    my %corner = map {$_ => 1} grep {
        my $p = $_;
        !grep {!$floor->{$_}} @{ $n8->{$p} }[2, 3, 4]
    } keys %$floor;
    my %kept = map {$_ => 1} grep {
        my $p = $_;
        grep {$corner{$_}} @{ $n->{$p} }
    } keys %corner;

    # blocks that share a side -- corners one step apart -- make one room
    my (%of_corner, @corners_of);
    foreach my $start (sort {$a <=> $b} keys %kept) {
        next if defined $of_corner{$start};
        my $id = @corners_of;
        my @q  = ($start);
        $of_corner{$start} = $id;
        my $bh = 0;
        while ($bh < @q) {
            foreach my $nb (grep {$kept{$_}} @{ $n->{ $q[$bh++] } }) {
                next if defined $of_corner{$nb};
                $of_corner{$nb} = $id;
                push @q, $nb;
            }
        }
        push @corners_of, \@q;
    } ## end foreach my $start (sort {$a...})
    return if @corners_of > 70;

    # a block's four cells take its room; where two blocks of different rooms
    # overlap the later corner wins, as it did in the original's sweep
    foreach my $p (sort {$a <=> $b} keys %kept) {
        $g->{'room'}{$_} = $of_corner{$p} foreach $p, @{ $n8->{$p} }[2, 4, 3];
    }

    # ... except the one cell two blocks share when they touch corner to
    # corner and nothing else: that is nobody's
    foreach my $shared (keys %{ $g->{'room'} }) {
        my ($up, $left, $up_left) = @{ $n8->{$shared} }[0, 6, 7];
        my @is = map {$kept{$_} ? 1 : 0} $up_left, $up, $left, $shared;
        delete $g->{'room'}{$shared} if $is[0] == $is[3] and $is[1] == $is[2] and $is[0] != $is[1];
    }
    foreach my $t (0 .. $#corners_of) {
        my %area;
        foreach my $p (grep {$g->{'room'}{$_} == $t} keys %{ $g->{'room'} }) {
            $area{$p} = 1;
            $area{$_} = 1 foreach grep {$floor->{$_}} @{ $n->{$p} };
        }
        $g->{'room_area'}[$t] = \%area;
    }
    return;
} ## end sub rooms

# %Game's cm{box}{to} = the cell the player must stand on to push the box from
# box to to.  It is used as it stands and not rebuilt, because it is not raw
# geometry -- it is the set of pushes that are actually WORTH making, and three
# separate prunings have already been applied to it:
#
#   * a push onto an avoid cell is gone, and so is every push off one;
#   * a push whose 5x6 local pattern is insoluble is gone (Parser.pm:306,
#     against the frozen Patterns.sqlite3) -- "a box arriving here from this
#     direction can never leave again";
#   * a cell no box can ever reach from its starting place is gone with all
#     its edges (prune_unreachable, Parser.pm:109).
#
# All three are statements about the level alone: where the other boxes stand
# does not enter into any of them, which is exactly why they belong in the
# static map and not in a test the search repeats a million times.  Measured
# over 1 500 games, they remove 26.6 % of the geometrically possible pushes,
# and 1 491 of those games are affected.
#
# Every cell in the map, key or value, is a floor cell.  That is what lets the
# engine walk these maps without ever asking whether a cell is a wall.
#
# was: the static half of init_push (Festival.pm:1531).  That one is handed a
# board and rebuilds an edge array of Index_num*4 entries for it, every time --
# and it prunes none of the three, because Festival has no equivalent of the
# pattern library at analysis time.
# cp{box}{to} = the cell the player VACATES INTO when he pulls the box from box
# to to.  He has to be standing on `to` when he starts -- the cell the box is
# about to occupy -- and he steps back one further, onto the value.  Both cells
# have to be free, which is the whole of simple_box_can_be_pulled.
#
# THE PULL MAP IS THE PUSH MAP TRANSPOSED, value and all:
#
#     cp{A}{B} == cm{B}{A}
#
# because a pull of a box from A to B is the undoing of a push of that box from
# B to A, and the cell the player stands on to make that push is the cell he
# ends up on having unmade it.  Box at 11 pushed to 12 with the player on 10;
# undone, the box goes 12 -> 11 and the player 11 -> 10.
#
# Which means the pull map inherits the push map's three prunings for free, and
# inherits them CORRECTLY: an edge dropped from the push map is a push no
# solution contains, so the pull that would undo it leads nowhere either.
#
# Read the pair as: cm{p} is where a box on p can GO, cp{p} is where it came
# FROM.  They are not each other's complement and neither implies the other --
# a goal in a corner has no cm entry at all, because a box that arrives there
# can never be pushed again, and it has a full set of cp entries, because boxes
# arrive there from every side.  (That asymmetry is also why the project's
# distance tables have no row for such a cell: Parser::route walks keys %Cmk.)
#
# was: the static half of init_pull (Festival.pm:1550), same story as push_map.
# It is also the map that retires simple_box_can_be_pulled's walk over the
# byte board.
sub pull_map ($g) {
    foreach my $p (keys %{ $g->{'cm'} }) {
        foreach my $to (keys %{ $g->{'cm'}{$p} }) {
            $g->{'cp'}{$to}{$p} = $g->{'cm'}{$p}{$to};
        }
    }
    return;
}

# side{p}{q} = with a box standing on p, WHICH REGION its floor neighbour q is
# in.  Two neighbours carry the same number when the player can walk from one
# to the other around the box, and different numbers when the box cuts them
# apart -- which is what a one-wide corridor does.  A wall neighbour is simply
# not in the map: nobody can stand there.
#
# was: zones_around_place (Festival.pm:776), called once per cell out of
# init_shift (1504) and thrown away after each board.  It is a fact about the
# level, so it is computed once here.
sub sides ($g) {
    $g->{'side'}{$_} = side_labels($g, $_, {}) foreach keys %{ $g->{'floor'} };
    return;
}

# The labels for one cell, with the cells of $blocked counting as walls too.
# The engine calls this for a board with frozen cells on it, which can cut
# apart two sides that the bare level leaves joined.
sub side_labels ($g, $p, $blocked) {
    my %label;
    my $next = 0;
    foreach my $start (@{ $g->{'cg'}{$p} }) {
        next if $blocked->{$start} or defined $label{$start};
        my $mark = $next++;
        my %seen = ($start => 1);
        my @q    = ($start);
        my $bh   = 0;
        while ($bh < @q) {
            my $c = $q[$bh++];
            foreach my $nb (@{ $g->{'cg'}{$c} }) {
                next if $nb == $p or $seen{$nb} or $blocked->{$nb};
                $seen{$nb} = 1;
                push @q, $nb;
            }
        }
        foreach my $other (@{ $g->{'cg'}{$p} }) {
            $label{$other} = $mark if $seen{$other};
        }
    } ## end foreach my $start (@{ $g->{...}})
    return \%label;
} ## end sub side_labels

# ---------------------------------------------------------------------------
# The two distance tables
# ---------------------------------------------------------------------------
#
# was: $Distance_from_to and $Bfs_distance_from_to (Festival.pm:241-242), built
# by set_distances (Festival_Parser.pm:4723)
#
# Both were index_num x index_num matrices packed into one string, read as
# vec($Distance_from_to, $from * $Index_num + $to, 32).  That multiplication is
# the reason the dense index space had to exist at all: it is an addressing
# scheme, and nothing else in the engine needs the renumbering.
#
#   d{from}{to}     pushes, to move a box from one cell to another on a board
#                   with no other boxes on it
#   walk{from}{to}  player steps between two cells, boxes ignored
#
# An entry that is not there means it cannot be done.  The old table said the
# same thing with the number 1000000, which every reader then had to know
# about and compare against; an absent key needs no sentinel and no comparison.
#
# The push table is a walk over cm, so it inherits cm's prunings: a box that
# can only get somewhere through a push no solution ever makes is, here,
# unable to get there.  That makes these distances longer than Festival's, or
# absent where Festival has a number -- never shorter.
#
# AND IT IS NOT A PLAIN WALK OVER cm, which is the thing worth understanding
# here.  A box does not move by itself: between two pushes in different
# directions the player has to get to the other side of it, and side{} says
# whether he can.  So the state is not the cell but the PAIR (cell, which side
# of the box he is on) -- changing side costs nothing when the two sides are
# one region, and is impossible when the box cuts them apart.  In a corridor
# one cell wide, a box can only keep going the way it was already going.
#
# Festival says the same thing with a graph of Index_num*4 vertices, a
# zero-cost "shift" table of Index_num*16 entries and a cost-one "push" table,
# relaxed by do_graph_iterations.  Its relaxation does not give the minimum:
# a shift costs no push but it costs one ROUND of the level-by-level walk, and
# a vertex keeps the weight it was first stamped with, so a route that changes
# sides often can lose the race to a heavier one that only pushes straight on.
# The stored table is an upper estimate (eq_dist.pl counts by how much).
sub distances ($g) {
    foreach my $from (keys %{ $g->{'floor'} }) {
        my %d  = ($from => 0);
        my @q  = ($from);
        my $bh = 0;
        while ($bh < @q) {
            my $p = $q[$bh++];
            foreach my $nb (@{ $g->{'cg'}{$p} }) {
                next if exists $d{$nb};
                $d{$nb} = $d{$p} + 1;
                push @q, $nb;
            }
        }
        $g->{'walk'}{$from} = \%d;
    }
    foreach my $from (keys %{ $g->{'floor'} }) {
        $g->{'d'}{$from} = push_spread($g, $from, $g->{'cm'});
    }
    return;
} ## end sub distances

# Breadth-first over (cell, side) pairs, counting pushes.  The player's side is
# carried along because it decides which pushes are available next: a push is
# available when the cell he must push from is on his side of the box, and he
# ends up where the box was -- so after a push his side of the new cell is the
# one the old cell lies on.
#
# The map is a parameter so that a gate can run the same walk over raw
# geometry.
sub push_spread ($g, $from, $cm) {
    my (%d, %seen);
    my @q;
    foreach my $s (values %{ $g->{'side'}{$from} }) {
        next if $seen{"$from/$s"}++;
        push @q, [$from, $s, 0];
    }
    my $bh = 0;
    $d{$from} = 0 if @q;
    while ($bh < @q) {
        my ($p, $s, $n) = @{ $q[$bh++] };
        foreach my $to (keys %{ $cm->{$p} // {} }) {
            next if $g->{'side'}{$p}{ $cm->{$p}{$to} } != $s;
            my $land = $g->{'side'}{$to}{$p};
            next if $seen{"$to/$land"}++;
            $d{$to} //= $n + 1;
            push @q, [$to, $land, $n + 1];
        }
    }
    return \%d;
} ## end sub push_spread

# impossible{p} = a box can never usefully stand on p: either no box of the
# starting position can be brought there, or a box standing there can be
# brought to no goal.  Both are questions put to the push table d, and that is
# all there is to it -- the table says "on an otherwise empty board", so what
# it rules out is ruled out on every board.
#
# was: @Impossible_place, built by compute_can_get_to_dest,
# compute_can_from_start and set_impossible_places (Festival_Parser.pm:
# 4035-4054) and stored under the dense index.
#
# Every avoid cell is in here (measured: no counterexample), and about a third
# of the games have cells in here that are not avoid cells -- this asks about
# the WAY to a cell, avoid asks about the cell itself.
sub impossible_cells ($g) {
    my @start = keys %{ $g->{'start'} };
    my @goal  = keys %{ $g->{'goal'} };
    $g->{'impossible'} = {};
    foreach my $p (keys %{ $g->{'floor'} }) {
        next if (grep {defined $g->{'d'}{$_}{$p}} @start) and (grep {defined $g->{'d'}{$p}{$_}} @goal);
        $g->{'impossible'}{$p} = 1;
    }
    return;
}

# ---------------------------------------------------------------------------
# Copies of the engine's own questions, for the analysis searches
# ---------------------------------------------------------------------------
#
# Verbatim from Fest.pm, where their comments are.
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

sub region_of ($v) {
    return min(keys %{ $v->{'reach'} }) // -1;
}

sub poskey ($v) {
    my $key = join(',', sort {$a <=> $b} keys %{ $v->{'box'} }) . '|' . region_of($v);
    $key .= '|' . join(',', sort {$a <=> $b} keys %{ $v->{'base'} }) if $v->{'base'};
    return $key;
}

sub touches_unreachable ($v, $p) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    foreach my $q (@{ $N8{$p} }) {
        next     if $Wall{$q} or $frozen->{$q} or $box->{$q};
        return 1 if !$reach->{$q};
    }
    return 0;
}

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

sub push_move ($v, $from, $to) {
    my $cm     = $Cm{$from} or return undef;
    my $stance = $cm->{$to} // return undef;
    return undef if $v->{'frozen'}{$to} or $v->{'box'}{$to} or !$v->{'reach'}{$stance};
    return { 'from' => $from, 'to' => $to, 'man' => $from, 'pull' => 0 };
}

sub pull_move ($v, $from, $to) {
    my $cp   = $Cp{$from} or return undef;
    my $back = $cp->{$to} // return undef;
    return undef if !$v->{'reach'}{$to} or $v->{'frozen'}{$back} or $v->{'box'}{$back};
    return { 'from' => $from, 'to' => $to, 'man' => $back, 'pull' => 1 };
}

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

sub freeze_crystaline ($v) {
    my ($box, $frozen) = @$v{ 'box', 'frozen' };
    my %home    = map {$_ => 1} grep {!$frozen->{$_}} keys %Goal;
    my $removed = 1;
    while ($removed) {
        $removed = 0;
    HOME: foreach my $p (keys %home) {
            foreach my $d (0 .. 3) {
                my $to = $N{$p}[$d];
                next if $Wall{$to} or $frozen->{$to} or $home{$to};
                my $beyond = $N{$to}[$d];
                next if $Wall{$beyond} or $frozen->{$beyond} or $home{$beyond};
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

sub stance_in_dead_pocket ($v, $box_cell, $stance) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    return 0 if $box->{$stance};
    return 0 if 1 != grep {!$frozen->{$_}} @{ $Cg{$stance} };
    return 0 if $reach->{$stance} and !$reach->{$box_cell};
    return 1;
}

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

sub forbidden_pair ($v, $pair) {
    my ($box, $frozen) = @$v{ 'box', 'frozen' };
    foreach my $p (keys %$box) {
        next     if $frozen->{$p} or !$pair->{$p};
        return 1 if grep {$box->{$_} and !$frozen->{$_}} keys %{ $pair->{$p} };
    }
    return 0;
}

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

sub can_go_on_pulling ($v) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    return 1 if $reach->{$Sok0} and !grep {!$Start{$_}} keys %$box;
    foreach my $p (keys %$box) {
        foreach my $d (0 .. 3) {
            my $stand = $N{$p}[$d];
            next if !$reach->{$stand};
            my $back = $N{$stand}[$d];
            return 1 if !($Wall{$back} or $frozen->{$back} or $box->{$back});
        }
    }
    return 0;
}

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
                return 'unknown' if @{ $last->{'sons'} } > 1000;
                return 'solved'  if grep {$_->{'packed'} == $nbox} @{ $last->{'sons'} };
                return '';
            },
        }
    );
    return { 'solved' => 1, 'dead' => 0, 'unknown' => -1 }->{$result};
} ## end sub can_be_packed

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

sub can_go_on_pulling_far ($v) {
    my ($box, $frozen, $reach) = @$v{ 'box', 'frozen', 'reach' };
    return 1 if $reach->{$Sok0} and !grep {!$Start{$_}} keys %$box;
    return 1 if keys %$reach > 1;
    return scalar grep {$frozen->{$_}} map {@{ $N{$_} }} keys %$reach;
}

sub base_landing ($bases) {
    return $Base_landing{ join ',', sort {$a <=> $b} keys %$bases } //= do {
        my $spread = box_spread({ 'box' => {}, 'frozen' => {} }, [keys %$bases], 0);
        +{ (map {$_ => 1} keys %$spread), %$bases };
    };
}

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
    my $next  = 0;
    foreach my $i (0 .. $#bases) {
        next if $group[$i] != -1;
        foreach my $j ($i .. $#bases) {
            $group[$j] = $next if defined $reach[$i]{ $bases[$j] } and defined $reach[$j]{ $bases[$i] };
        }
        $next++;
    }
    my @size = map {
        my $i = $_;
        scalar grep {$group[$_] == $group[$i]} $i .. $#bases
    } 0 .. $#bases;
    my $most = List::Util::max(0, @size);
    my %out;
    foreach my $i (grep {$size[$_] == $most} 0 .. $#bases) {
        $out{ $bases[$_] } = 1 foreach grep {$group[$_] == $group[$i]} $i .. $#bases;
    }
    return \%out;
} ## end sub biggest_base_group

sub far_enough_apart ($c1, $c2) {
    return 1 if ($Walk{$c1}{$c2} // 1000000) >= 6;
    my ($r1, $r2) = ($Room{$c1}, $Room{$c2});
    return $r1 != $r2 ? 1 : 0 if defined $r1  and defined $r2;
    return 0                  if !defined $r1 and !defined $r2;
    return 0                  if defined $r1  and $Room_area[$r1]{$c2};
    return 0                  if defined $r2  and $Room_area[$r2]{$c1};
    return (int($c1 / $Width) != int($c2 / $Width) and $c1 % $Width != $c2 % $Width) ? 1 : 0;
}

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

sub pullable_somewhere ($box, $p) {
    foreach my $d (0 .. 3) {
        my $q = $N{$p}[$d];
        next if $Wall{$q} or $box->{$q};
        my $far = $N{$q}[$d];
        return 1 if !($Wall{$far} or $box->{$far});
    }
    return 0;
}

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

# ---------------------------------------------------------------------------
# What only a search can tell about the level
# ---------------------------------------------------------------------------
# blocks{p}{blocker} = how many goals a box on p LOSES when another box stands
# on the blocker's cell and never moves -- of the goals it could be brought to
# on an empty board; and completely{p}{blocker} = 1 when it loses all of them.
# Returns (\%blocks, \%completely).  Cells a box can never usefully stand on,
# and goals, are left out on both sides: a box on a goal is where it belongs,
# not in the way.  `completely` is what forbidden_pairs picks its candidates
# by; `blocks` is installed as %Blocks, the "hotspots" of the plan mode BASE
# (Games::Sokoban::Fest::plan_context).
#
# was: init_hotspots (Festival_Parser.pm:4382), $blocks_place and
# $completely_blocks -- two more index_num x index_num matrices in a string.
# The original rebuilt its whole graph once per blocker; here the blocker is one
# frozen cell of a view, and the sides of the cells, which are what the blocker
# changes, are worked out once per blocker and shared by all the questions.
sub blocking () {
    my @cells = sort {$a <=> $b} grep {!$Impossible{$_} and !$Goal{$_}} keys %Floor;
    my $empty = { 'box' => {}, 'frozen' => {}, 'reach' => {} };
    my (%goals_from, %blocks, %completely, %side0);
    foreach my $p (@cells) {
        $goals_from{$p} = grep {$Goal{$_}} keys %{ box_spread($empty, [$p], 0, 0, \%side0) };
    }
    foreach my $blocker (@cells) {
        my $view = { 'box' => {}, 'frozen' => { $blocker => 1 }, 'reach' => {} };
        my %side;
        foreach my $p (@cells) {
            next if $p == $blocker;
            my $left = grep {$Goal{$_}} keys %{ box_spread($view, [$p], 0, 0, \%side) };
            $blocks{$p}{$blocker}     = $goals_from{$p} - $left;
            $completely{$p}{$blocker} = 1 if !$left;
        }
    }
    return (\%blocks, \%completely);
} ## end sub blocking

# The forbidden pairs: two cells such that boxes standing on both can never
# both be brought home, whatever else is on the board.  Found by trying -- the
# two boxes alone on the level, the player everywhere at once, can_be_packed
# with room for a hundred positions -- and a pair goes on the list only when
# that comes back with a PROOF that it cannot be done.
#
# Most pairs are never tried.  A pair is a candidate only if each of its two
# cells completely blocks the other (blocking() above), which is what makes
# this affordable; and it is dropped again if it is none of this test's
# business: both cells goals, the floor cut in two, the plain "two boxes side
# by side along a wall", or a shape the pattern library already knows.
#
# The list being built is the list the search consults (why_dead asks %Mpdb),
# so a pair found early prunes the searches that come after it, and the pairs
# are tried in the order of their cells, as the original tries them.  It saves
# work and, measured, changes no answer: with the feedback switched off the
# same 80 games gave the same pairs.  It could only matter to a search that
# runs out of its hundred positions, and a search of two boxes hardly does.
#
# Fills %Mpdb and returns it as {a}{b} = {b}{a} = 1.
#
# was: build_mpdb2 (Festival_Parser.pm:4644)
sub forbidden_pairs () {
    %Mpdb = ();
    return {} if keys %Start == 1;
    my @rules = @Envelope;
    @Envelope = ();    # they are worked out after the pairs, with their help
    my (undef, $completely) = blocking();
    my @cells = sort {$a <=> $b} grep {!$Impossible{$_} and !$Tunnel_push{$_}} keys %Floor;
    foreach my $i (0 .. $#cells - 1) {
        my $c1 = $cells[$i];
        foreach my $c2 (@cells[$i + 1 .. $#cells]) {
            next if !$completely->{$c1}{$c2} or !$completely->{$c2}{$c1};
            my $v = { 'box' => { $c1 => 1, $c2 => 1 }, 'frozen' => {}, 'reach' => {} };
            next if $Goal{$c1} and $Goal{$c2};
            next if @{ (regions($v))[1] } > 1;
            next if side_by_side_on_a_wall($c1, $c2);
            next if pattern_dead($v, $c1, 0) or pattern_dead($v, $c2, 0);
            $v->{'reach'} = { map {$_ => 1} grep {$_ != $c1 and $_ != $c2} keys %Floor };
            next if can_be_packed($v, 100);
            $Mpdb{$c1}{$c2} = $Mpdb{$c2}{$c1} = 1;
        }
    }
    @Envelope = @rules;
    return {%Mpdb};
} ## end sub forbidden_pairs

# Are these boxes stuck for a PULL search -- can they not all be pulled free?
# 1 = stuck, and that is a proof; 0 = they can; 2 = gave up.
#
# "Free" is decided box by box, and generously: a box that can be pulled along
# its row AND along its column, with the player able to step onto the cell it
# left, is as free as a box gets -- nothing about it can be part of a deadlock
# -- so it is simply taken off the board (a kill move, and then the only move
# the position has).  What the search is left to find out is whether the
# boxes that are NOT free can be pulled until they are, or until each stands
# on a cell a box starts on.  It follows the move that leaves the fewest boxes,
# then the fewest pieces of floor, then the most boxes on goals.
#
# was: is_xy_deadlock (Festival_Parser.pm:5412) over xy_search_actual (5366),
# get_best_xy_move (5347), reduce_moves_in_xy_search (5325) and
# mark_hv_indices (5300)
#
# ONE APPROXIMATION.  The original gives up when the untried moves lead to
# "more than 500 different positions", which it estimates by hashing every
# move's outcome into 1024 buckets and counting the buckets in use.  How many
# buckets N different positions take up depends on their md5 values; on
# average more than 500 are in use from N = 687 on, and that is the number used
# here.  It can only matter to a search that is about to give up anyway.
sub stuck_for_pulling ($start) {
    my $home = sub ($view) {!grep {!$Start{$_}} keys %{ $view->{'box'} }};
    return 0 if $home->($start);
    my $result = small_search(
        {
            'start'    => $start,
            'max'      => 500,
            'solved'   => $home,
            'finished' => sub ($view) {$view->{'reach'}{$Sok0} and $home->($view)},
            'better'   => sub ($son, $best) {
                return $son->{'boxes'} < $best->{'boxes'}     if $son->{'boxes'} != $best->{'boxes'};
                return $son->{'regions'} < $best->{'regions'} if $son->{'regions'} != $best->{'regions'};
                return $son->{'packed'} > $best->{'packed'};
            },
            'look' => sub ($open) {
                my %outcome = map {$_->{'key'} => 1} map {@{ $_->{'sons'} }} @$open;
                return keys %outcome >= 687 ? 'unknown' : '';
            },
            'moves' => sub ($view) {
                my ($moves) = possible_moves($view, 1, {});
                my %by_box;
                push @{ $by_box{ $_->{'from'} } }, $_ foreach @$moves;
                foreach my $from (sort {$a <=> $b} keys %by_box) {
                    my ($along_row, $along_column) = (0, 0);
                    foreach my $m (@{ $by_box{$from} }) {
                        next if !apply($view, $m)->{'reach'}{$from};
                        $along_column = 1 if int($m->{'to'} / $Width) != int($from / $Width);
                        $along_row    = 1 if $m->{'to'} % $Width != $from % $Width;
                    }
                    next if !$along_row or !$along_column;
                    return [{ 'from' => $from, 'to' => $from, 'man' => $from, 'pull' => 1, 'kill' => 1 }];
                }
                return $moves;
            },
        }
    );
    return { 'solved' => 0, 'dead' => 1, 'unknown' => 2 }->{$result};
} ## end sub stuck_for_pulling

# The forbidden pairs of a pull search: two cells such that boxes on both can
# never both be pulled free.  Only pairs that could plausibly be one are tried:
# in one row or one column, two to nine cells apart, with a clear walk between
# them, and not both standing so much in the open that each could be pulled two
# cells in all four directions.  (That last test is a shortcut and nothing
# more: with it taken out the search says the same of every such pair, only
# later -- measured on 60 games.)
#
# was: build_pull_mpdb2 (Festival_Parser.pm:4697) and very_pullable (4686)
sub forbidden_pull_pairs () {
    %Pull_mpdb = ();
    return {} if keys %Start == 1;
    my @cells = sort {$a <=> $b} grep {!$Impossible{$_} and !$Tunnel_pull{$_}} keys %Floor;
    foreach my $i (0 .. $#cells - 1) {
        my $c1 = $cells[$i];
        foreach my $c2 (@cells[$i + 1 .. $#cells]) {
            my ($dy, $dx) = (abs(int($c1 / $Width) - int($c2 / $Width)), abs($c1 % $Width - $c2 % $Width));
            next if $dy and $dx;
            my $apart = $dy + $dx;
            next if $apart == 1 or $apart >= 10 or ($Walk{$c1}{$c2} // -1) != $apart;
            my $v = { 'box' => { $c1 => 1, $c2 => 1 }, 'frozen' => {}, 'reach' => {} };
            next if in_the_open($v, $c1) and in_the_open($v, $c2);
            next if $Start{$c1}          and $Start{$c2};
            next if @{ (regions($v))[1] } > 1;
            $v->{'reach'} = { map {$_ => 1} grep {$_ != $c1 and $_ != $c2} keys %Floor };
            next if stuck_for_pulling($v) != 1;
            $Pull_mpdb{$c1}{$c2} = $Pull_mpdb{$c2}{$c1} = 1;
        }
    } ## end foreach my $i (0 .. $#cells...)
    return {%Pull_mpdb};
} ## end sub forbidden_pull_pairs

# Two free cells in a row beyond the box, in all four directions?
sub in_the_open ($v, $p) {
    my $box = $v->{'box'};
    foreach my $d (0 .. 3) {
        my $near = $N{$p}[$d];
        return 0 if $Wall{$near} or $box->{$near};
        my $far = $N{$near}[$d];
        return 0 if $Wall{$far} or $box->{$far};
    }
    return 1;
}

# The envelope rules (see freeze_envelopes for what one is and how it is used).
#
# Take the level as it looks when it is solved, a box on every goal.  Those
# boxes may cut pieces of floor off from the rest.  For each such piece -- a
# small one: at most half the floor -- take the goals that line it: the ones
# right beside it always, the ones that only touch it at a corner in every
# combination, fewest first.  Put boxes on those goals and nothing else on the
# board, the player anywhere OUTSIDE the piece, and ask can_be_packed whether
# he can do anything at all with them that ends with every box on a goal
# again.  If, from every region outside, that is PROVED impossible, the ring
# can never be touched from out there: it becomes a rule -- these cells taken,
# the player confined to where he was put -- and freeze_envelopes will freeze
# the boxes of the ring whenever a position matches.
#
# A ring that an earlier, smaller rule already covers is not tried again, and
# one that would use every box of the level is not a rule about part of it.
# The rules found so far are in force while the later ones are being searched
# for, as in the original -- which, measured on 60 games, changes none of them.
#
# Fills @Envelope and returns it.
#
# was: init_envelope_patterns (Festival_Parser.pm:2517), analyse_envelope
# (2498), get_envelope_boxes (2409), can_solve_from_any_zone (2473) and the
# three board builders round them
sub envelope_rules () {
    @Envelope = ();
    my $solved = { 'box' => {%Goal}, 'frozen' => {} };
    my (undef, $pieces) = regions($solved);
    return [] if @$pieces < 2;
    my $nfloor = keys %Floor;
    foreach my $piece (@$pieces) {
        my %inside = map {$_ => 1} @$piece;
        my (@beside, @corner, %taken);
        foreach my $p (@$piece) {
            push @beside, grep {$Goal{$_} and !$taken{$_}++} @{ $N{$p} };
        }
        foreach my $p (@$piece) {
            push @corner, grep {$Goal{$_} and !$taken{$_}++} @{ $N8{$p} };
        }
        next if @$piece > $nfloor / 2 or @corner >= 8;
        foreach my $count (0 .. @corner) {
            foreach my $choice (0 .. 2**@corner - 1) {
                my @chosen = grep {$choice >> $_ & 1} 0 .. $#corner;
                next if @chosen != $count;
                my %box = map {$_ => 1} @beside, @corner[@chosen];
                next if keys %box == keys %Start;
                my %outside = map {$_ => 1} grep {!$inside{$_} and !$box{$_}} keys %Floor;
                my $covered = 0;
                foreach my $rule (@Envelope) {
                    next if grep {!$box{$_}} @{ $rule->{'box'} };
                    next if grep {!$rule->{'allowed'}{$_}} keys %outside;
                    $covered = 1;
                    last;
                }
                next if $covered;

                # from every region outside the piece
                my $v = { 'box' => \%box, 'frozen' => {} };
                my ($region, $cells_of) = regions($v);
                my $within = $region->{ $piece->[-1] };
                my $can    = 0;
                foreach my $id (grep {$_ != $within} 0 .. $#$cells_of) {
                    my %there = map {$_ => 1} @{ $cells_of->[$id] };
                    next if !can_be_packed({ %$v, 'reach' => \%there }, 100);    # 0 is the only "no"
                    $can = 1;
                    last;
                }
                next if $can;
                push @Envelope, { 'box' => [sort {$a <=> $b} keys %box], 'allowed' => \%outside };
            } ## end foreach my $choice (0 .. 2**...)
        } ## end foreach my $count (0 .. @corner)
    } ## end foreach my $piece (@$pieces)
    return [@Envelope];
} ## end sub envelope_rules

# Everything above, in the order the original runs it: the pairs with no rules
# in force, the pull pairs, then the envelope rules with the pairs to help.
# Returns what goes into the level's analysis beside geometry()'s result.
#
# was: the tail of preprocess_level (Festival_Parser.pm) -- build_mpdb2,
# build_pull_mpdb2, init_envelope_patterns
sub search_analysis () {
    @Envelope = ();
    my $pairs = forbidden_pairs();
    my $pull  = forbidden_pull_pairs();
    my $rules = envelope_rules();
    return { 'mpdb' => $pairs, 'pull_mpdb' => $pull, 'envelope' => $rules, 'snail' => snail_analysis() };
}

# Do the two boxes share a 2x2 block whose other two cells are walls?  That is
# the everyday frozen pair, which the freeze test finds on the spot; it does
# not need an entry in a table.
#
# was: two_near_wall (Festival_Parser.pm:4619), a sweep over every 2x2 anchor
# of the rectangle for a board known to hold exactly two boxes
sub side_by_side_on_a_wall ($c1, $c2) {
    my $ring = $N8{$c1};
    foreach my $k (1, 3, 5, 7) {
        my @rest = @$ring[$k - 1, $k, ($k + 1) & 7];
        next     if 1 != grep {$_ == $c2} @rest;
        return 1 if 2 == grep {$Wall{$_}} @rest;
    }
    return 0;
}

# ---------------------------------------------------------------------------
# What the modes need of the level
# ---------------------------------------------------------------------------
# goals_away{p} = the pushes from p to EVERY goal, added up (a goal out of
# reach adds nothing) -- how far a box on p is from the goals all together.
# The backward searches of BASE, of the HF family and of REV score a position
# by it, and want it LARGE: they are running away from the goals.
#
# was: init_scored_distance (Festival.pm:3356), the pull half; the modes used
# to work it out at every run (goals_away in Fest.pm)
sub goals_away () {
    my %away;
    foreach my $p (keys %Floor) {
        $away{$p} = 0;
        $away{$p} += $D{$p}{$_} // 0 foreach keys %Goal;
    }
    return \%away;
}

# How many pulls a box is from the goals, every cell, on the empty level: the
# spread from all the goals at once, pulling -- the same table the BASE
# forward score uses (plan_context's goal_far), and by the reversal of every
# pull into a push, the push distance to the nearest goal.  The original works
# it out at the start of a push search; it is a fact about the level, so here
# it is worked out once per level.  A cell that is missing cannot be reached.
# was: init_scored_distance (Festival.pm:3356), the push half, over
# get_distance_from_targets (2689)
sub goals_near () {
    return box_spread({ 'box' => {}, 'frozen' => {} }, [keys %Goal], 1);
}

# What the value is normalised by: the pulls from the goals, cell by cell;
# 0.95 to every power up to the number of boxes; one over the boxes; one over
# the boxes times the farthest cell.
# was: init_girl_variables (Festival_Parser.pm:7645) with init_girl_distance
# and init_gamma_table
sub girl_context () {
    my $near = goals_near();
    my $n    = keys %Start;
    my $far  = List::Util::max(0, values %$near);
    return {
        'near'  => $near,
        'n'     => $n,
        'gamma' => [map {0.95**$_} 0 .. $n],
        'inv'   => 1 / $n,
        'norm'  => 1 / ($n * ($far || 1)),
    };
}

# The level's chain analysis: {kind => 'snail' | 'netlock' | '', target,
# depth => the target's layers, dist => {chain cell => pulls from the
# target along the chain}, len => the chain's length + 1, grid => {cells in
# step with the target}}.  A goal a box starts on is never the target.  With
# no goal in question the target is cell 0, as in the original.
# was: detect_snail_level (Festival_Parser.pm:3718) with analyze_chain (3673)
# and set_netlock_grid (3559)
sub snail_analysis () {
    my %home = map {$_ => 1} grep {$Start{$_}} keys %Goal;
    my ($target, $hardest) = (undef, -1);
    foreach my $goal (sort {$a <=> $b} keys %Goal) {
        next if $Start{$goal};
        my $depth = peel_order({ %home, $goal => 1 })->{$goal};
        ($target, $hardest) = ($goal, $depth) if $depth > $hardest;
    }
    my $t = $target // 0;
    my ($ty, $tx) = (int($t / $Width), $t % $Width);
    my %grid = map {$_ => 1} grep {((int($_ / $Width) ^ $ty) & 1) == 0 and ((($_ % $Width) ^ $tx) & 1) == 0} keys %Floor;
    my $kind = $hardest >= 20 ? 'snail' : $hardest >= 10 ? 'netlock' : '';
    my (%dist, $len);
    if ($kind eq 'snail') {

        # the chain: the goals joined to the target goal by goal; the far end
        # is the goal farthest along it (the lowest-numbered at a tie), and
        # the distance kept is the one from the target, so that the target
        # is 0 and the far end the chain's length
        my $bfs = sub ($from) {
            my %d  = ($from => 0);
            my @q  = ($from);
            my $bh = 0;
            while ($bh < @q) {
                my $p = $q[$bh++];
                foreach my $q (@{ $N{$p} }) {
                    next if !$Goal{$q} or exists $d{$q};
                    $d{$q} = $d{$p} + 1;
                    push @q, $q;
                }
            }
            return \%d;
        };
        my $from_target = $bfs->($target);
        my ($far) = sort {$from_target->{$b} <=> $from_target->{$a} or $a <=> $b} keys %$from_target;
        $len = $from_target->{$far};
        my $from_far = $bfs->($far);
        %dist = map {$_ => $len - $from_far->{$_}} keys %$from_far;
        $len++;
    } ## end if ($kind eq 'snail')
    return { 'kind' => $kind, 'target' => $t, 'depth' => $hardest, 'dist' => \%dist, 'len' => $len // 0, 'grid' => \%grid };
} ## end sub snail_analysis

# ---------------------------------------------------------------------------
# The level, handed over
# ---------------------------------------------------------------------------
# INSTALL A LEVEL: this module's variables filled from the Parser's hash and
# from $g -- geometry()'s result, without the products of the analysis, which
# search_analysis() finds next (prepare).
#
# Then WHAT THE MODES NEED OF THE LEVEL: the facts single modes used to work
# out for themselves at every run, now once, from what is now installed.  None
# of them depends on the products of the analysis, so they come out the same
# whichever way those came.
sub install ($gm, $g) {

    # from %Game
    %Cg    = %{ $gm->{'cg'} };
    %Cm    = %{ $gm->{'cm'}   // {} };
    %Blok  = %{ $gm->{'blok'} // {} };
    %Floor = map {$_ => 1} keys %Cg;
    %Goal  = map {$_ => 1} @{ $gm->{'goal'} };
    %Start = map {$_ => 1} @{ $gm->{'baggage'} };
    $Sok0  = $gm->{'player'};
    $Width = $gm->{'w'};        # for "same row / same column", and for the one test that looks past a run's last cell

    # from the level record
    %Cp          = %{ $g->{'cp'}         // {} };
    %D           = %{ $g->{'d'}          // {} };
    %Goal_hole   = %{ $g->{'goal_hole'}  // {} };
    %Impossible  = %{ $g->{'impossible'} // {} };
    %Mpdb        = %{ $g->{'mpdb'}       // {} };
    %N           = %{ $g->{'n'} };
    %N8          = %{ $g->{'n8'} };
    %Pattern     = %{ $g->{'pattern'}    // {} };
    %Pattern_at  = %{ $g->{'pattern_at'} // {} };
    %Pull_mpdb   = %{ $g->{'pull_mpdb'}  // {} };
    %Room        = %{ $g->{'room'}       // {} };
    @Room_area   = @{ $g->{'room_area'}  // [] };
    $Snail       = $g->{'snail'};       # the chain analysis (snail_analysis), or nothing
    %Side        = %{ $g->{'side'} };
    %Tunnel_pull = %{ $g->{'tunnel_pull'} // {} };
    %Tunnel_push = %{ $g->{'tunnel_push'} // {} };
    %Walk        = %{ $g->{'walk'}        // {} };
    %Wall        = %{ $g->{'wall'} };
    @Envelope    = @{ $g->{'envelope'} // [] };

    # the caches of the copies below
    %Base_landing = ();
    %Dead_cache   = ();
    %Far_pulls    = ();
    @Stuck        = ();

    # what the modes need of the level
    %Blocks       = %{ (blocking())[0] };
    %Goals_away   = %{ goals_away() };
    %Goals_near   = %{ goals_near() };
    $Girl_context = girl_context();
    $Room_links0  = room_links({ 'box' => {}, 'frozen' => {} });
    return;
} ## end sub install

# THE RECORD of the level now installed: every variable above under its own
# name in lower case, and the stamp.  Everything the engine reads, and nothing
# else -- analysis_record packs it, and Fest::take_level takes it in that
# form.  Each table is copied at the top, so that the record stays what it is
# when the next level is installed here.
sub record () {
    return {
        'stamp'        => $ANALYSIS_STAMP,
        'blok'         => {%Blok},
        'cg'           => {%Cg},
        'cm'           => {%Cm},
        'floor'        => {%Floor},
        'goal'         => {%Goal},
        'start'        => {%Start},
        'sok0'         => $Sok0,
        'width'        => $Width,
        'cp'           => {%Cp},
        'd'            => {%D},
        'goal_hole'    => {%Goal_hole},
        'impossible'   => {%Impossible},
        'n'            => {%N},
        'n8'           => {%N8},
        'pattern'      => {%Pattern},
        'pattern_at'   => {%Pattern_at},
        'room'         => {%Room},
        'room_area'    => [@Room_area],
        'side'         => {%Side},
        'tunnel_pull'  => {%Tunnel_pull},
        'tunnel_push'  => {%Tunnel_push},
        'walk'         => {%Walk},
        'wall'         => {%Wall},
        'mpdb'         => {%Mpdb},
        'pull_mpdb'    => {%Pull_mpdb},
        'envelope'     => [@Envelope],
        'snail'        => $Snail,
        'blocks'       => {%Blocks},
        'goals_away'   => {%Goals_away},
        'goals_near'   => {%Goals_near},
        'girl_context' => $Girl_context,
        'room_links0'  => $Room_links0,
    };
} ## end sub record

# PREPARE A LEVEL, ALL OF IT, and hand back its record: the geometry,
# installed, then what only a search can find -- which needs the geometry
# installed, since it searches with the engine's own move generator.
# (search_analysis fills %Mpdb, %Pull_mpdb and @Envelope itself; the chain
# verdict it only returns.)
sub prepare ($gm) {
    install($gm, geometry($gm));
    $Snail = search_analysis()->{'snail'};
    return record();
}
1;
__END__

=head1 NAME

Games::Sokoban::Solver::Fest::Analysis - the level, prepared for the Fest engine as one record

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Fest::Analysis ();

    my $record = Games::Sokoban::Solver::Fest::Analysis::prepare(\%game);           # the Parser's analysis hash
    my $blob   = Games::Sokoban::Solver::Fest::Analysis::analysis_record($record);  # what Fest::solve takes

=head1 DESCRIPTION

Everything L<Games::Sokoban::Solver::Fest> needs to know about a level before
any search starts, worked out of the analysis of
L<Games::Sokoban::Solver::Parser> and packed into one self-contained record:
the maps read off the shape, the forbidden pairs, pull pairs and envelope
rules that only a search can find, the chain verdict, and the per-level
tables the modes used to compute at every run. The engine reads nothing but
the record and does not load this module.

This is Games::Sokoban::FestDev 1.00 of the Sokoban project; about five
seconds on a large level, without a budget.

=head1 FUNCTIONS

=head2 prepare

    my $record = prepare(\%game);

The record as a hash. Dies on a level with floor on the rim of its rectangle
(L<Games::Sokoban::Solver::Level> rings such a level first).

=head2 analysis_record

    my $blob = analysis_record($record);

C<compress(nfreeze(...))>, stamped with C<$ANALYSIS_STAMP>; the engine
refuses a record with another stamp.

=head1 SEE ALSO

L<Games::Sokoban::Solver::Fest>, L<Games::Sokoban::Solver>.

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
