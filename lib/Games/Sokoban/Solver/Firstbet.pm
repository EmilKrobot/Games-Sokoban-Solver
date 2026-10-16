package Games::Sokoban::Solver::Firstbet;

# ===== THE FIRST-SOLUTION ENGINE =====
# A 10-mode portfolio over one engine. This file carries ONLY promoted, fully
# proven machinery -- no experiment knobs, no diagnostics, no tracing. It is
# Games::Sokoban::Firstbet 3.8 of the Sokoban project, where the experiments
# live in a permanent slot beside it and a promotion ADDS a proven feature and
# bumps the version; here only the modules it leans on are rewired.
#
# solve($gameid, $gm, $limit, $mode = 'PUSH_SCORE') returns ($reason, $path,
# $doba, $nseen). $gameid is any integer the caller names the level by (it is
# printed in the progress lines). $limit is seconds; 0 = NO time limit (the
# search then ends only on
# SOLVED, MEMCAP, IGNORE or GIVEUP/NOCP). $reason is 'SOLVED' or 'TIMEOUT'/'UNSOLVABLE', plus
# 'GIVEUP' (ORDER/CONVEYOR exhausted its RESTRICTED tree -- not the full
# state space, hence not UNSOLVABLE), 'NOCP' (CONVEYOR only: the game has no
# forced conveyor, the mode is INAPPLICABLE -- it never searched, which is
# why it must not read as GIVEUP), and the run-control reasons 'IGNORE'
# (race lost) / 'MEMCAP' (RAM ceiling). $nseen = positions seen (forward) /
# configs generated (BACKWARD).
#
# The portfolio: PUSH_SCORE (default; quadratized push distance), MOVE_SCORE
# (quadratized move distance), PUSH_ASSIGN (Hungarian assignment on raw push
# distances), MOVE_SUM (additive raw move distances), ROUTE (route-edge
# bands), FLOW (route-dominant with a coarse gradient), ORDER (macro-level
# DFS over the goal-fill ladder), BACKWARD (guided pull search from solved
# to Start), CONVEYOR (forced-common-path macro delivery), FEATURE (the
# feature-space search: positions are FILED by four counts, expansion goes
# round the coordinate cells, poradci make advised pushes free; since 3.4
# the PUSH_SCORE distance runs beside the counts as ADVICE -- a sixth
# poradce and the in-cell tie-break -- never as the primary order).
#
# Baked-in machinery (each measured and promoted in its day; git has the
# numbers): player-equivalence CLASS keys + the known-class skip in the
# forward searches; the cross-run Tahy cache; the cp package (the
# ride-and-deliver conveyor macro; its score bonuses -- sledge, flat, and
# the PUSH_ASSIGN tie-break -- were removed in 3.3, measured inert by
# ablation, 2026-08-28); the route-delivery macro; the
# hole/corridor fill macros; the deadlock battery (blok bit vectors, wall,
# corridor, hole, is_frozen, matching feasibility) and the wallified
# matching over fix_diagonals board degeneration.
#
# This module stores nothing: the caller hands solve() the analysis of
# Games::Sokoban::Solver::Parser as $gm (its blob() form) and owns the result.
our $VERSION = '0.01';
use v5.42;                                          # strict + warnings + the :5.42 feature bundle (signatures, say, ...)
use experimental 'refaliasing', 'declared_refs';    # enables the features AND silences their experimental warnings
use warnings FATAL => 'uninitialized';
no warnings 'recursion';                            # odfs recurses deeply
use Carp        ('confess');
use Time::HiRes ('tv_interval', 'gettimeofday');
use Storable    ('thaw', 'dclone');
use List::Util  ('max');
use Compress::Zlib;
use Term::ANSIColor;
use Games::Sokoban::Solver::Console ('backline', 'backlinen', 'podil');
use Games::Sokoban::Solver::Data    ();
use Games::Sokoban::Solver::Heap    ();
use Games::Sokoban::Solver::Memory  ();
use Games::Sokoban::Solver::Munkres ();             # assign() called fully-qualified (avoids name clash)
use Games::Sokoban::Solver::Path    ();             # rebuilt(): the finished path written again from its pushes

# The per-game and per-search state, ALL LEXICAL since 2026-08-24 (USER). It
# used to be `our`, and the reason given was that the ai/ gates alias it into
# their own packages with typeglobs -- but a gate of mine is not a reason for a
# production module to hand out its insides. `ai/module_surface.pl` put numbers
# on it: of 23 `our` names, six were reached from app/ or lib/, twelve only from
# the five deadlock-comparison gates, and five from nowhere at all. Those gates
# drive Games::Sokoban::Firstbet01 now -- the slot carries the same names, and
# what they measure is unchanged because the slot's instrumentation is inert.
# What is left `our` further down IS the contract: $VERSION, $QUIET,
# $RACE_FLAG, $RACE_GID, $MAX_GB -- five names ($MEMORY went on 2026-09-04,
# $CORRAL on 2026-09-09; the reason is the same both times, a switch with one
# used value).
my (%Game,       @Goal, @Target, %Cm, %Cmk, @Baggage, @Maze, $W);
my (%Parent,     $Start);     # seen-set/path chain + start position
my ($PaintId,    @Vis);       # paint() epoch + reach marks
my ($PaintId_fr, @Vis_fr);    # paint_fr/is_frozen twin of the pair above
my @Buf;                      # paint()'s own wavefront, its working buffer only:
                              # the region's LENGTH used to be kept beside it in
                              # $PaintSize, which nothing ever read
my $BIG = 1_000_000;          # sentinel for Inf/unreachable entries in $DistRaw

# ONE SHAPE FOR EVERY RESULT LINE, here and in Festival.pm, which prints the same
# string. A driver interleaves the two engines' lines (tandem_matrix prints all
# eighteen), so a column that moves between modes is a column nobody can read
# down. The head is what every search knows; the tail is five slots, and a mode
# that has nothing for a slot leaves it BLANK rather than shifting the rest:
#
#   1 box moves/s   2 positions/s   3 queue peak   4 queue left   5 positions seen
#
# Slot 5 is the seen count in every mode of both engines, so the last column can
# be read straight down. Slot 4 is the one that carries whatever else a mode has
# -- ORDER puts its macro count there, Festival its plan length -- because it is
# the only slot whose meaning was never the same twice anyway.
my $ENDING = '%-12s %5d %3d %4d %-10s %6d %6d %12.4f %8s %8s %8s %8s %9s';
my (@Cg, %Pis, @Priority, $Has_hole, $Has_wall, $Has_corridor, $Hole, $Wall, $Corridor, $Blok, $Gameid);
my $BlokVec;                 # blok patterns as trimmed bit vectors, parallel to $Blok -- the hot vec test in is_bad
my ($Nbox,       %Sols, $Distance, $MaxP, $MaxVal, $corridors, $holes);
my ($DistRaw,    $Value);    # raw distance table + the mode's scorer code-ref
my ($Route,      $RouteBonus, $Has_cp, %CPath);
my (%CPathIdx,   @CPathArr,   %ToGoal);        # conveyor {src}{tgt}=>index map / ordered edges / endpoint deliveries
my ($RouteMoves, $RouteMust,  $Has_routes);    # per-(box,goal) route moves / must_empty + presence flag
my $Macro_step = 0;                            # set while scoring a route-macro INTERMEDIATE: no route advantage
my ($Pex, %Tahy, $Bestbet, $pu);
my @Blk;                                       # paint()'s box marks
my @Buf_fr;                                    # paint_fr's own wavefront (boxes marked in @Vis_fr, no separate @Blk_fr)
my @IsWall;                                    # cell-indexed "this cell is a wall" (fix_diagonals hot tests)

# Player-equivalence position classes: every key in the FORWARD search carries
# the SMALLEST cell of the player's reachable region instead of the player's
# cell, so one key names the whole class "same boxes, player anywhere in this
# region". %CanonMap memoizes raw key -> canonical key (one flood per raw key
# ever born, a hash hit for every repeat). The canonicalization painter has its
# own epoch/arrays because @Vis belongs to the candidate loop and @Vis_fr to
# the macros/frozen check, and a child is canonicalized in the middle of both.
# %SolsC = the P1 park terminals collapsed per (layout, region): canonical key
# -> [tail start cell, tail]. ORDER/CONVEYOR/BACKWARD keep raw keys.
my (%CanonMap, @Vis_c, @Buf_c, $PaintId_c, %SolsC, $SolvedLay, $ManOff);

# FEATURE mode state. $Feat_mode is set per game in initvars_common; it gates
# every FEATURE-only build (plan, rooms, explorer index) and the per-cell
# extra pass in canon_key, so the other nine modes never pay for any of it.
my $Feat_mode = 0;
my (%FCellQ, @FCellKey, $FCellPtr);    # coordinate key -> queue / wheel order / wheel hand
my %ExplMark;                          # child key -> the explorer poradce points at it (set in tahy)
my %RegCells;                          # canonical key -> cells beyond the parent's region at first birth
my %StanceIdx;                         # stance cell -> [[box, target], ...], the %Cm inversion, once per game
my (@RoomOf, @DoorAt);                 # cell -> room id / doorway cell -> the door chain
my $NRooms;
my @PlanNeed;                             # goal cell -> [cells its journey still needs] (out_of_plan)
my (@PlanPair, @PlanInit, @PlanWaves);    # build_plan results (documented at the Plan section;
                                          # @PlanUnpaired stood here too -- built at the end of
                                          # build_plan, read by nothing)
my $Plan_waves = 0;
my (@Vis_ci, @FloorCells);                # island counter's own paint + floor list
my $PaintId_ci = 0;

# Matching-deadlock filter (Festival check_matching_deadlock analog). Hungarian
# feasibility over box->goal reachability: if the boxes cannot be assigned 1:1
# to goals each individually push-reachable, no solution exists -> deadlock.
# SOUND necessary condition over the FULL boxes x all-goals matrix: never
# rejects a solvable position. Two SOUND gates keep it nearly free where it
# cannot pay:
#   * per-game ($Match_active): a matching deadlock can only exist if the game
#     has a NON-GOAL selective cell -- if every selective cell is a goal, each
#     box either sits on a goal (self-edge) or reaches all goals, so Hall's
#     condition never fails. Decided once in initvars_score.
#   * per-position ($Selective{$t} guard at the hook): a push onto a cell
#     reaching ALL goals cannot introduce a new Hall violation.
my (%ReachG, %Selective);    # per-game: cell->{reachable goals}, selective-cell flag
my (%Rev,    %ReachW);       # per-game: reverse push graph; per wall-set: goal->{cells that still reach it}
my $Walled_on    = 0;        # per-game: the wallified-matching filter can run at all
my $Match_active = 0;        # per-game: a non-goal selective cell exists

# MOVE_SUM is EXCLUDED from the cp package (set per mode in initvars_score):
# measured, the cp machinery breaks a game the baseline MOVE_SUM solves,
# while its cp wins are covered by the other modes anyway -- portfolio
# diversity keeps one coarse scorer cp-blind. (The package's score bonuses
# are gone since 3.3; this flag now gates only the ride-and-deliver macro.)
my $CP_mode_ok = 1;

# FLOW scoring constants: route-band weight (route always outranks the
# secondary bucket) and the secondary quantum (LARGER = flatter).
my ($FLOW_W, $FLOW_Q) = (100_000, 4);

# The corridor and hole pattern tables, read once per process from the
# distribution's data directory.
$corridors = Games::Sokoban::Solver::Data::load('corridor_pattern.stor');
$holes     = Games::Sokoban::Solver::Data::load('hole_pattern.stor');

# %Bad and %Tahy live in RAM, private to the process, for the life of one
# solve -- and nowhere else. Until 2026-09-04 a switch ($MEMORY) chose between
# these hashes and per-game files in the shared BerkeleyDB env (bad_<id>.brk +
# ftahy_<id>.brk, kept on TIMEOUT so a retry started warm), and every driver
# set it to RAM: N workers racing the SAME game must not share one .brk file,
# that env is opened without locking, and a file opened inside an ithread
# stays locked until the thread is joined. A switch with one allowed value is
# no switch (USER), so it went, and with it this module's only use of
# Games::Berkeley; the warm-start role belongs to FirstbetBerk, whose store is
# on disk by construction. The tahy_* accessors keep the FirstbetBerk seam
# contract: tahy_get may return a fresh arrayref -- never mutate in place,
# always write back.
my %MemBad;

# What the solve prints, in three levels (USER 2026-09-28, the same in every
# engine that has $QUIET):
#   0  everything;
#   1  no TRANSIENT progress lines (backline) -- the durable ones (backlinen:
#      the end-of-search line in barva(), NOCP) stay; what a threaded driver
#      sets, since N workers' progress on one STDERR is noise;
#   2  nothing: neither the transient nor the durable lines.
# The transient ones are gated `$QUIET or backline(...)` at their call sites,
# the durable ones by `$QUIET > 1`.
our $QUIET = 0;

# THE THREE RUN CONTROLS HAVE THREE PERIODS, and until 2026-09-11 they had one
# (USER). All of them used to hang off the PROGRESS interval, because that is
# where they were added one at a time as the code grew -- so the time limit and
# the race signal were only as prompt as the screen, and a 15 s run ended at 21.
# The periods now match what each one costs and how promptly it must act:
#
#   * the LIMIT on the cheap counter gate, every 100-200 iterations. Reading the
#     clock is 0.09 us, and a budget that overruns by up to 6 s is a budget that
#     does not mean what it says -- 40 % on a short gate run.
#   * the RACE FLAG once a second. A loser burning a core for another six
#     seconds is not a disaster, but a shared-hash read is cheap enough that
#     there is no reason to wait.
#   * MEMORY on the PROGRESS interval, where it already was, and no more often
#     (USER 2026-09-11). It is the expensive one -- 4.3 us measured against
#     0.09 for the clock -- and, more to the point, when the engine works
#     correctly memory grows slowly: the ceiling is a brake against a BUG, not
#     a regulator, and a brake does not need a short period. (The impression
#     that the probe is dear comes from before 2026-08-27, when the same call
#     went through LibreHardwareMonitor's JSON at ~211 ms.)
#
# $SCREEN is the progress interval itself, and it is not arbitrary either: the
# USER's own threshold is that when nothing moves on screen for about eight
# seconds, a long run starts to look broken.
my $SCREEN = 6;

# 'race' cooperative cancellation (threaded winner-takes-all drivers). ithreads
# cannot be force-killed, so: when one thread's solve() returns a feasible
# SOLVED, the driver sets $RACE_FLAG->{gid}=1 in a threads::shared hash; the
# OTHER threads still solving that game notice it within a second and bail out
# with $reason='IGNORE' (not a real result). Non-race
# callers set neither, so race_lost() is a cheap short-circuit.
our ($RACE_FLAG, $RACE_GID);
sub race_lost() {$RACE_FLAG && $RACE_GID && $RACE_FLAG->{$RACE_GID}}

# RAM ceiling (GiB); 0 = off. Memory::used_gb() reads TOTAL system RAM used
# (one kernel call), so this caps the WHOLE
# machine -- the right signal in a threaded run where many solves grow at
# once. Checked at the ~7s progress checkpoints; over the cap ends
# $reason='MEMCAP' (callers treat it like TIMEOUT).
our $MAX_GB = 0;
sub mem_over() {$MAX_GB && Games::Sokoban::Solver::Memory::used_gb() > $MAX_GB}

# tv_interval() can return a NEGATIVE elapsed time on Windows (system-clock
# jitter). Floor every solve()-returned $doba at a tiny positive epsilon --
# also guards the rate divisions against a zero elapsed.
sub clamp_doba($doba) {$doba < 0.000001 ? 0.000001 : $doba}

# The end-of-search line, coloured by outcome. Green solved it, yellow spent its
# whole budget, white was told not to bother -- and RED is everything else, which
# is the point: a mode that walked away early (GIVEUP, NOCP, FAILED, MEMCAP,
# UNSOLVABLE) is not a mode whose clock ran out, and until 2026-08-31 the two
# looked identical here. Goes through backlinen -- this is the DURABLE line, the
# one that must survive in the scrollback.
sub barva($reason, $ending) {
    return if $QUIET > 1;
    state $colour = { 'SOLVED', 'bright_green', 'TIMEOUT', 'bright_yellow', 'IGNORE', 'white' };
    my $color = $colour->{$reason} // 'bright_red';
    backlinen(Term::ANSIColor::colored($ending, $color));
}

# bad_init/bad_close still take the gameid / the solved flag their callers pass:
# the twin's seam (FirstbetBerk) needs both, and the call sites are shared.
sub bad_init($)      {%MemBad     = (); %Tahy = ()}
sub bad_close($)     {%MemBad     = (); %Tahy = ()}
sub setbad($p)       {$MemBad{$p} = 1}
sub isbad($p)        {exists $MemBad{$p}}
sub tahy_get($p)     {$Tahy{$p}}
sub tahy_set($p, $k) {$Tahy{$p} = $k}
sub tahy_del($p)     {delete $Tahy{$p}}

sub clearvars() {
    $Bestbet      = undef;
    $Blok         = undef;
    $BlokVec      = undef;
    $Corridor     = undef;
    $Distance     = undef;
    $Has_corridor = undef;
    $Has_hole     = undef;
    $Has_wall     = undef;
    $Hole         = undef;
    $MaxP         = undef;
    $MaxVal       = undef;
    $Nbox         = undef;
    $Route        = undef;
    $RouteBonus   = undef;
    $Has_cp       = undef;
    %CPath        = ();
    %CPathIdx     = ();
    @CPathArr     = ();
    %ToGoal       = ();
    $Pex          = undef;
    %FCellQ       = ();
    @FCellKey     = ();
    $FCellPtr     = 0;
    %ExplMark     = ();
    %RegCells     = ();
    %StanceIdx    = ();
    $W            = undef;
    $Wall         = undef;
    $PaintId      = undef;
    $PaintId_fr   = undef;
    $Start        = undef;
    @Vis          = ();
    @Blk          = ();
    @Vis_fr       = ();
    @Vis_c        = ();
    @Buf_c        = ();
    %CanonMap     = ();
    %SolsC        = ();
    $PaintId_c    = undef;
    $SolvedLay    = undef;
    @Baggage      = ();
    @Buf          = ();
    @Buf_fr       = ();
    @Goal         = ();
    @Maze         = ();
    @IsWall       = ();
    @Cg           = ();
    %Cm           = ();
    %Cmk          = ();
    %Game         = ();
    @Priority     = ();
    %Parent       = ();
    %Pis          = ();
    %Sols         = ();
    %Tahy         = ();
    @Target       = ();
} ## end sub clearvars

sub cesta($m, $target, $baggage) {
    my ($bh, $bt, $x, $p, $d, @buf, %path);
    %path     = ($m, '');
    $path{$_} = undef foreach (@{ $baggage; });
    $buf[0]   = $m;
    ($bh, $bt) = (0, 1);
    while ($bh != $bt) {
        $x = $buf[$bh++];
        $p = $path{$x};
        foreach my $t (@{ $Cg[$x]; }) {
            if (not exists $path{$t}) {
                $path{$t} = $p . $Pis{ $t - $x };
                return $path{$t} if $t == $target;
                $buf[$bt++] = $t;
            }
        }
    }
    die 'NO PATH';
} ## end sub cesta

# THE ENGINE REPLAYS WHAT IT RETURNS (USER 2026-10-07: a solution that does not
# replay is inadmissible). Every search here rebuilds its path from links it
# trusts -- %Parent, the pull records, a stored tail -- and each of them is
# argued to be one legal move. This does not argue: it plays the finished
# string on the level, from the start position, by the rules the database's own
# check uses (Zapis::validate_path: a wall or a filler cell stops the player, a
# box is pushed when the cell behind it is free floor, and at the end every goal
# holds a box), and dies naming the step if it cannot. So whatever a later
# change does to a macro, a link or a tail, SOLVED never leaves this file with a
# path that fails -- the worst case is a death that says where.
# Called once per solved game, at each of the four endings; a few hundred steps.
sub replay_check($path) {
    my %step = ('l', -1, 'r', 1, 'u', -$W, 'd', $W);
    my %box  = map(($_, 1), @Baggage);
    my $cell = $Game{'player'};
    my $i    = -1;
    foreach my $ch (split //, $path) {
        ++$i;
        my $d  = $step{ lc $ch } // confess("the solution does not replay: step $i is '$ch'");
        my $to = $cell + $d;
        confess("the solution does not replay: step $i '$ch' walks into a wall")
            if $to < 0
            or $to > $#Maze
            or $Maze[$to] eq '9'
            or $Maze[$to] eq '1';
        if (exists $box{$to}) {
            my $beyond = $to + $d;
            confess("the solution does not replay: step $i '$ch' pushes the box on cell $to against a wall or another box")
                if $beyond < 0
                or $beyond > $#Maze
                or $Maze[$beyond] eq '9'
                or $Maze[$beyond] eq '1'
                or exists $box{$beyond};
            delete $box{$to};
            $box{$beyond} = 1;
        }
        $cell = $to;
    } ## end foreach my $ch (split //, $path)
    for my $g (@Goal) {
        confess("the solution does not replay: after its last step the goal on cell $g holds no box") unless exists $box{$g};
    }
    return;
} ## end sub replay_check

# THE FINISHED PATH IS WRITTEN AGAIN FROM ITS PUSHES (3.8, USER 2026-10-12): a
# solution is a row of elementary pushes -- the player walks to a box and
# pushes it one cell, and the push says where he had to stand -- whatever a
# search calls a position and however far one of its moves carries a box. So
# every engine of the project passes its path through one procedure while the
# level is still in memory (Games::Sokoban::Path): the path is read as its
# pushes, up to the one after which every goal is under a box; pushes that only
# take the boxes away and bring them back are left out where that makes the
# path shorter; and the rest is played from the start with a shortest walk to
# each. What it changes HERE, on the 34 322 solved paths of matrix fm-1:
#   * the seven forward modes: where the finishing moves of a P1 park terminal
#     are attached, the player was walked to the cell those stored moves start
#     from and they begin with a walk of their own -- two shortest walks that
#     meet in a cell nobody needed (135 paths, the walk before the last push
#     every time);
#   * ORDER and CONVEYOR: their positions carry the player's CELL, not his part
#     of the floor, ORDER notes only the END of a macro as seen, and the branch
#     of its depth-first walk is the solution -- so a box nudged away and
#     nudged back stays in it (211 of 1 484 paths of ORDER, 4 of CONVEYOR);
#   * BACKWARD: nothing (4 590 paths come back letter for letter).
# No search is touched. Called at each of the four endings, before
# replay_check(), which then plays what is going to be returned.
sub rebuilt_path($path) {
    return Games::Sokoban::Solver::Path::rebuilt(
        'path'   => $path,
        'width'  => $W,
        'floor'  => [grep {$Maze[$_] ne '9' and $Maze[$_] ne '1'} 0 .. $#Maze],
        'goals'  => \@Goal,
        'boxes'  => \@Baggage,
        'player' => $Game{'player'},
    );
}

sub steps($best) {
    my $p      = $best;
    my @postup = $p;
    my %vidi   = ($p, 1);
    while (($p = $Parent{$p})) {
        confess 'INFINITE CYCLE!' if $vidi{$p}++;
        unshift @postup, $p;
    }
    confess 'NOT A START' unless $Start eq $postup[0];
    return @postup;
}

# Path reconstruction from the %Parent chain. The player's TRUE cell is
# derived, not read from the keys: after a push (source -> target) the player
# stands on $source, the cell the box left, so consecutive box layouts alone
# determine where the walk to the next push stance starts. The chain root
# ($Start) is the only key whose man is read -- it IS the true start cell
# (never canonicalized). On canonical chains this is what keeps the replayed
# path feasible, since a canonical key carries the region's smallest cell,
# not the cell the player stands on.
sub get_path($best) {
    my @postup = steps($best);
    my ($father, @sb, @fb, $source, $target, %fh, %sh, $path, $move, $man, $cell);
    $father = shift @postup;
    ($cell, @fb) = unpack($pu, $father);
    $path = '';
    foreach my $son (@postup) {
        (undef, @sb) = unpack($pu, $son);
        %fh = map(($_, 1), @fb);
        %sh = map(($_, 1), @sb);

        # ONE box leaves and ONE arrives, or this is not a path. The lists are
        # counted, not just read at their first element: a link across two
        # pushes used to pass here whenever its first pair of cells happened
        # to be a legal push, and the other push was silently lost (game 5469).
        # And the one move is an edge of the push graph: $man is asked BEFORE
        # the letter is looked up, so a link that is not one cell dies with
        # its two cells named and not on an undefined hash key.
        my @gone = grep((!$sh{$_}), @fb);
        my @new  = grep((!$fh{$_}), @sb);
        confess("a link of the solution is not one push: boxes (@fb) -> (@sb)") unless @gone == 1 && @new == 1;
        ($source, $target) = ($gone[0], $new[0]);
        $man = $Cm{$source}{$target};
        confess("a link of the solution is not one push: $source -> $target") unless defined $man;
        $move = uc $Pis{ $target - $source };

        if ($cell == $man) {
            $path .= $move;
        }
        else {
            $path .= cesta($cell, $man, \@fb) . $move;
        }
        $cell   = $source;    # the player ends where the box was
        @fb     = @sb;
        $father = $son;
    } ## end foreach my $son (@postup)
    return $path;
} ## end sub get_path

# Mode-agnostic setup: the maze, the push/walk graphs, the deadlock structures,
# the goal-fill order, the pack template + Start position, and the reset search
# state. Every mode calls this.
sub initvars_common($gameid, $gm, $mode) {
    clearvars();
    bad_init($gameid);
    $Gameid    = $gameid;
    $Feat_mode = $mode eq 'FEATURE' ? 1 : 0;
    %Game      = %{ thaw(uncompress($gm)); };
    my $maze = $Game{'code'};
    $maze =~ tr/,//d;
    $maze =~ tr/45678/00233/;
    @Maze         = split(//a, $maze, 0);
    $Game{'maze'} = &dclone(\@Maze);
    @IsWall       = map {$_ eq '9' ? 1 : 0} @Maze;                          # fix_diagonals' hot occupancy test
    @Goal         = @{ $Game{'goal'}; };
    @Target       = ();
    $Target[$_]   = 1 foreach @Goal;                                        # cell-indexed goal flag
    %Cm           = %{ $Game{'cm'};  };
    %Cmk          = %{ $Game{'cmk'}; };
    @Cg           = ();
    $Cg[$_]       = $Game{'cg'}{$_} foreach keys %{ $Game{'cg'} };          # cell-indexed walk graph
    @Baggage      = @{ $Game{'baggage'}; };
    $W            = $Game{'w'};
    %Pis          = (-1, 'l', 1, 'r', $W, 'd', -$W, 'u');
    $Nbox         = scalar @Baggage;
    @Priority     = ();
    $Priority[$_] = $Game{'order'}{$_} foreach keys %{ $Game{'order'} };    # cell-indexed order rank
    ($Has_hole, $Has_wall, $Has_corridor) = @Game{ 'has_hole', 'has_wall', 'has_corridor' };
    ($Blok, $BlokVec)                     = _blok_both($Game{'blok'});      # arrays (cold callers) + vecs (tahy hot path)
    $Hole     = &dclone($Game{'hole'})     if $Has_hole;
    $Wall     = &dclone($Game{'walls'})    if $Has_wall;
    $Corridor = &dclone($Game{'corridor'}) if $Has_corridor;
    _corral_geom();
    $Pex       = 'Games::Sokoban::Solver::Heap'->new;
    %ExplMark  = ();
    %RegCells  = ();
    %StanceIdx = ();

    if ($Feat_mode) {    # invert %Cm once per game: which pushes does this stance serve?
        for my $b (keys %Cm) {
            my $tb = $Cm{$b};
            push @{ $StanceIdx{ $tb->{$_} } }, [$b, $_] for keys %$tb;
        }
        build_rooms();
    }
    else {
        @RoomOf = @DoorAt = ();
        $NRooms = 0;
    }
    %Parent     = ();
    %Tahy       = ();
    $Bestbet    = undef;
    %Sols       = %{ $Game{'sols'} };
    $PaintId    = 0;
    $PaintId_fr = 0;
    @Blk        = (0) x scalar @Maze;
    @Vis        = (0) x scalar @Maze;
    @Vis_fr     = (0) x scalar @Maze;

    # Parser already chose the pack template ('C*' or 'n*') and packed %Sols
    # with it -- just reuse it, no re-packing needed.
    $pu    = $Game{'vzp'};
    $Start = pack($pu, $Game{'player'}, @{ $Game{'baggage'} });

    # Class-key state (forward search only): the canonicalization painter, the
    # layout-only real-terminal test, and the P1 park terminals collapsed per
    # (layout, region). $SolvedLay = the boxes-only tail of a solved position's
    # key (defined when #goals == #boxes, i.e. the solved layout is unique);
    # $ManOff = byte length of the man element, so substr($key, $ManOff) IS the
    # layout. %SolsC keeps, per class, the tail whose letters are fewest.
    %CanonMap  = ();
    %SolsC     = ();
    @Vis_c     = (0) x scalar @Maze;
    $PaintId_c = 0;
    $ManOff    = length pack($pu, 0);
    $SolvedLay = (@Goal == $Nbox) ? pack($pu, sort {$a <=> $b} @Goal) : undef;
    foreach my $k (keys %Sols) {
        my $t = $Sols{$k};
        next unless defined $t && $t =~ /[A-Za-z]/;    # P1 park terminal (real ones have tail '')
        my ($m, @bb) = unpack($pu, $k);
        my $ck = canon_key($m, \@bb);
        $SolsC{$ck} = [$m, $t] if !exists $SolsC{$ck} || length($t) < length($SolsC{$ck}[1]);
    }
} ## end sub initvars_common

# blok loader: the blob carries TRIMMED BIT VECTORS (tools/update_block.pl
# converted the whole DB 2026-08-06). Build both runtime forms once at load:
# vecs for is_bad's hot tahy() gear, arrays for the cold callers that do not
# maintain a box vector. An array pattern dies LOUDLY -- it can only mean a
# pre-conversion blob (an old backup), which would otherwise compute garbage
# silently.
sub _blok_both ($src) {
    my (%arr, %vec);
    foreach my $bx (keys %{ $src // {} }) {
        my $row = $src->{$bx};
        foreach my $t (keys %$row) {
            my (@as, @vs);
            foreach my $p (@{ $row->{$t} }) {
                die "array blok pattern -- the Parser writes bit vectors" if ref $p;
                push @as, [grep {vec($p, $_, 1)} 0 .. 8 * length($p) - 1];
                push @vs, $p;
            }
            $arr{$bx}{$t} = \@as;
            $vec{$bx}{$t} = \@vs;
        }
    }
    return (\%arr, \%vec);
} ## end sub _blok_both
##############################################################################
# ===== Engine ===============================
##############################################################################
# The move generator and everything it needs: the reachability flood (paint),
# the frozen-cluster check, the scorers, the deadlock battery, the fill/route
# macros and tahy() itself. This is the hot core -- every search in the file
# runs through tahy().
# The canonicalization flood: paint the region of $man with @$bag as walls,
# tracking its smallest cell -- the class representative. paint_fr shape
# (boxes marked visited), min maintained inline: one compare per visited cell.
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
    my $key = pack($pu, $min, @$bag);

    # FEATURE only: the explorer poradce wants the cells of this region lying
    # OUTSIDE the parent's region (@Vis is still the parent's live paint when
    # children are born) -- the new ground this push opened. A second pass over
    # the flood's own buffer, so the nine other modes pay nothing per cell.
    if ($Feat_mode) {
        my @new = grep {$Vis[$_] != $PaintId} @Buf_c[0 .. $bt - 1];
        $RegCells{$key} = \@new if @new;
    }
    return $key;
} ## end sub canon_key

# Memoized canonical key of a child position: one flood per DISTINCT raw key,
# a single hash hit for every repeated birth of the same raw position. (The
# candidate loop in tahy() inlines this expression; the macro chains call it.)
sub _ck($man, $bag) {
    return $CanonMap{ pack($pu, $man, @$bag) } //= canon_key($man, $bag);
}

# Fallback terminal test for the rare #goals != #boxes game (no unique solved
# layout string): every goal covered by a box.
sub _lay_solved($child) {
    my (undef, @nb) = unpack($pu, $child);
    my %nb = map(($_, 1), @nb);
    return !grep {!exists $nb{$_}} @Goal;
}

sub paint($man, @baggage) {
    ++$PaintId;
    $Blk[$_]   = $PaintId for @baggage;
    $Vis[$man] = $PaintId;
    $Buf[0]    = $man;
    my $bt = 1;
    for (my $bh = 0; $bh < $bt; ++$bh) {
        my $x = $Buf[$bh];
        foreach my $t (@{ $Cg[$x] }) {

            # Vis first: in a BFS "already visited" is far commoner than "is a
            # box", so testing it first short-circuits the majority of neighbours
            # and skips the @Blk index. Same boolean, operands side-effect-free.
            next if $Vis[$t] == $PaintId || $Blk[$t] == $PaintId;
            $Vis[$t] = $PaintId;
            $Buf[$bt++] = $t;
        }
    }
} ## end sub paint

# Reachability-only painter for is_frozen() / goal-corral check / the macros,
# with its own globals so it never disturbs @Vis/@Blk/$PaintId used by
# paint()/tahy().
sub paint_fr($man, @baggage) {
    ++$PaintId_fr;

    # Boxes act as walls: mark them SEEN in @Vis_fr (not a separate @Blk_fr) so
    # they are never enqueued/expanded, and the inner test collapses to a single
    # compare. Safe because every reader of @Vis_fr queries a FLOOR cell --
    # is_frozen()/_macro_fill() re-check a box-occupied stance explicitly.
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

# Detect a frozen (permanently immovable) box cluster among @nomove -- boxes
# that already had no legal push in tahy()'s main loop. Boxes in the cluster
# may unfreeze each other's neighbours as the man's reachable area changes
# with them as walls, so iterate to a fixed point.
# Returns ('frozen', ()) if any frozen box is off-goal (true deadlock);
# ('', @frozen) if all frozen boxes sit on goals (caller still checks whether
# the frozen wall encloses an open goal -- goal-corral);
# ('', ()) if nothing stays frozen.
sub is_frozen($man, @nomove) {
    my %frozen = map(($_, 1), @nomove);
    while (1) {
        my @still_frozen = ();
        paint_fr($man, keys %frozen);
        foreach my $bx (keys %frozen) {
            my $movable = 0;
            foreach my $t (@{ $Cmk{$bx} }) {
                next if exists $frozen{$t};
                my $stance = $Cm{$bx}{$t};
                next
                    if exists $frozen{$stance}
                    ; # frozen box ON the stance blocks the push: paint_fr marks boxes in @Vis_fr, so a Vis-hit alone no longer distinguishes floor from a frozen-box cell -- re-check here
                next unless $Vis_fr[$stance] == $PaintId_fr;
                $movable = 1;
                last;
            }
            push @still_frozen, $bx unless $movable;
        }
        last if scalar @still_frozen == scalar %frozen;
        %frozen = map(($_, 1), @still_frozen);
    } ## end while (1)
    return ('', ()) unless %frozen;
    for (keys %frozen) {return ('frozen', ()) unless $Target[$_]}
    return ('', keys %frozen);
} ## end sub is_frozen

# --- FEATURE coordinates -----------------------------------------------------
# Free-floor island count (Festival's connectivity): flood every floor cell
# not under a box, own paint arrays -- @Vis/@Vis_fr/@Vis_c stay untouched.
sub conn_islands($t_bag) {
    ++$PaintId_ci;
    my $n = 0;
    for my $c (@FloorCells) {
        next if $Vis_ci[$c] == $PaintId_ci || exists $t_bag->{$c};
        ++$n;
        $Vis_ci[$c] = $PaintId_ci;
        my @st = ($c);
        while (@st) {
            my $x = pop @st;
            for my $t (@{ $Cg[$x] }) {
                next if $Vis_ci[$t] == $PaintId_ci || exists $t_bag->{$t};
                $Vis_ci[$t] = $PaintId_ci;
                push @st, $t;
            }
        }
    }
    return $n;
} ## end sub conn_islands

# --- room decomposition, built once per FEATURE game -------------------------
# Doorways = articulation cells of the walk graph: a cell whose removal raises
# the number of components. Found by one depth-first scan keeping, per cell,
# the earliest cell its subtree can climb back to (the standard low-point
# rule); the recursion is written as an explicit stack because a corridor
# board can be thousands of cells deep. Rooms are then the components of the
# floor with the doorways taken out, and every doorway remembers which rooms
# it joins.
sub build_rooms() {
    @RoomOf = ();
    @DoorAt = ();
    $NRooms = 0;
    my @floor = grep {defined $Cg[$_]} 0 .. $#Cg;
    return unless @floor;
    my (@num, @low, @par, %door);
    my $counter = 0;
    for my $root (@floor) {
        next if $num[$root];
        my @stack = ([$root, 0]);
        $num[$root] = $low[$root] = ++$counter;
        $par[$root] = -1;
        my $rootkids = 0;
        while (@stack) {
            my $top = $stack[-1];
            my ($x, $i) = @$top;
            my $nb = $Cg[$x] // [];
            if ($i < @$nb) {
                ++$top->[1];
                my $y = $nb->[$i];
                next if $y == $par[$x];
                if ($num[$y]) {$low[$x] = $num[$y] if $num[$y] < $low[$x]}
                else {
                    $par[$y] = $x;
                    $num[$y] = $low[$y] = ++$counter;
                    ++$rootkids if $x == $root;
                    push @stack, [$y, 0];
                }
            }
            else {
                pop @stack;
                my $p = $par[$x];
                if ($p >= 0) {
                    $low[$p]  = $low[$x] if $low[$x] < $low[$p];
                    $door{$p} = 1        if $p != $root && $low[$x] >= $num[$p];
                }
            }
        } ## end while (@stack)
        $door{$root} = 1 if $rootkids > 1;
    } ## end for my $root (@floor)

    # rooms = components of the floor minus the doorways
    for my $c (@floor) {
        next if $door{$c} || $RoomOf[$c];
        my $id = ++$NRooms;
        my @q  = ($c);
        $RoomOf[$c] = $id;
        while (@q) {
            my $x = pop @q;
            for my $y (@{ $Cg[$x] // [] }) {
                next if $door{$y} || $RoomOf[$y];
                $RoomOf[$y] = $id;
                push @q, $y;
            }
        }
    }

    # Adjacent doorways are ONE door, not several. A corridor is a whole chain
    # of articulation cells, and taken one at a time each would only ever see
    # other doorways as neighbours -- the rooms at the two ends would never be
    # joined. So group the doorways into connected chains and let each chain
    # remember its cells and the rooms it touches.
    $RoomOf[$_] = 0 for keys %door;    # a doorway belongs to no room
    my %chain;
    for my $d (keys %door) {
        next if $chain{$d};
        my @cells = ($d);
        $chain{$d} = 1;
        my @q = ($d);
        while (@q) {
            my $x = pop @q;
            for my $y (@{ $Cg[$x] // [] }) {
                next unless $door{$y} && !$chain{$y};
                $chain{$y} = 1;
                push @cells, $y;
                push @q,     $y;
            }
        }
        my %rooms;
        for my $c (@cells) {
            $rooms{ $RoomOf[$_] } = 1 for grep {$RoomOf[$_]} @{ $Cg[$c] // [] };
        }
        next if keys(%rooms) < 2;          # a chain that joins nothing is not a door
        my $door = [[@cells], [keys %rooms]];
        $DoorAt[$_] = $door for @cells;    # every cell of the chain names the chain
    } ## end for my $d (keys %door)
    return;
} ## end sub build_rooms

# How many groups do the rooms fall into once every box-blocked doorway is
# shut? Union-find over a handful of rooms. A box inside a room is invisible
# here BY DESIGN -- that is the whole difference from counting islands.
sub room_groups($t_bag) {
    return 1 unless $NRooms;
    my @up = (0 .. $NRooms);
    my $n  = $NRooms;
    my %done;
    for my $d (0 .. $#DoorAt) {
        my $door = $DoorAt[$d] or next;
        next if $done{$door}++;                        # the chain is one door, visited once
        my ($cells, $ids) = @$door;
        next if grep {exists $t_bag->{$_}} @$cells;    # a box anywhere in it shuts it
        my $a = $ids->[0];                             # find roots inline (a closure here cost a sub call per lookup)
        $a = $up[$a] while $up[$a] != $a;
        for my $i (1 .. $#$ids) {
            my $b = $ids->[$i];
            $b = $up[$b] while $up[$b] != $b;
            next if $a == $b;
            $up[$b] = $a;
            --$n;
        }
    } ## end for my $d (0 .. $#DoorAt)
    return $n;
} ## end sub room_groups

# --- out-of-plan: the plan's own journeys ------------------------------------
# Per goal, the cells its journey still needs. Built once per FEATURE game
# from the plan; empty when there is no plan, which makes the feature a
# constant 0 rather than an error.
sub build_planneed() {
    @PlanNeed = ();
    for my $p (@PlanPair) {
        my ($goal, undef, undef, $pulls) = @$p;
        my %c;
        for my $step (@$pulls) {$c{ $step->[0] } = 1; $c{ $step->[1] } = 1}
        delete $c{$goal};
        $PlanNeed[$goal] = [keys %c] if %c;
    }
    return;
}

# Boxes standing on cells a journey still to come needs. A pair counts as done
# once its goal is occupied, so only the unfinished journeys are asked about.
sub out_of_plan($t_bag) {
    return 0 unless @PlanNeed;
    my %hit;
    for my $goal (0 .. $#PlanNeed) {
        my $need = $PlanNeed[$goal] or next;
        next if exists $t_bag->{$goal};    # that goal is filled: journey over
        for my $c (@$need) {$hit{$c} = 1 if exists $t_bag->{$c} && !$Target[$c]}
    }
    return scalar keys %hit;
}

# The four counts of one position, and the cell key they name. One unpack for
# all four; the search calls this once per expansion (the parent, to compare
# against) and once per queued child.
sub feat_counts($pozice) {
    my (undef, @bb) = unpack($pu, $pozice);
    my %bag = map(($_, 1), @bb);
    return (plan_odometer(\@bb), conn_islands(\%bag), room_groups(\%bag), out_of_plan(\%bag));
}
sub feat_key($pozice) {join ',', feat_counts($pozice)}

# The lexicographic order the four counts are read in -- Festival's
# is_better_score with the fields we have, same directions and the same "read
# the next one only on a tie" discipline:
#     packed  MORE is better
#     islands FEWER is better
#     rooms   FEWER is better
#     outplan FEWER is better
# A candidate is [child, packed, islands, rooms, outplan, marked, advised].
# ($x/$y, not $a/$b: a signature parameter named $a or $b shadows sort's
# globals for the whole sub -- a documented trap in this project.)
sub feat_better($x, $y) {
    return $x->[1] > $y->[1] if $x->[1] != $y->[1];
    return $x->[2] < $y->[2] if $x->[2] != $y->[2];
    return $x->[3] < $y->[3] if $x->[3] != $y->[3];
    return $x->[4] < $y->[4] if $x->[4] != $y->[4];
    return 0;
}

# Each poradce names ONE child, the way Festival's choose_advisor does: of the
# candidates that strictly improve ITS OWN count, keep the best by the full
# order above -- not by its own criterion. All poradci rank equally afterwards,
# so a child named by one is exactly as free as a child named by four. The one
# thing that IS supreme is the veto on the first line: a move that LOWERS the
# packing count is not recommendable by anybody. Since 3.4 a SIXTH poradce
# stands beside them: the child with the best (lowest) value_score, chosen by
# its OWN criterion -- the score IS its metric, there is no count of it to
# improve -- under the same packing veto; ties fall to the first seen
# (deterministic under a fixed hash seed). So at most six children per
# expansion come out free (four counts + the explorer + the score).
sub feat_advise($kids, $b_odo, $b_isl, $b_room, $b_out) {
    my $n = 0;
    for my $crit (0 .. 4) {
        my $best;
        for my $k (@$kids) {
            next if $k->[1] < $b_odo;    # the packing veto, above every poradce
            my $speaks =
                  $crit == 0 ? $k->[1] > $b_odo
                : $crit == 1 ? $k->[2] < $b_isl
                : $crit == 2 ? $k->[3] < $b_room
                : $crit == 3 ? $k->[4] < $b_out
                :              $k->[5];            # the explorer, marked in tahy()
            next unless $speaks;
            $best = $k if !defined $best || feat_better($k, $best);
        }
        next unless $best;
        ++$n unless $best->[6];
        $best->[6] = 1;
    } ## end for my $crit (0 .. 4)
    my $best;
    for my $k (@$kids) {
        next       if $k->[1] < $b_odo;
        $best = $k if !defined $best || $k->[7] < $best->[7];
    }
    if ($best) {
        ++$n unless $best->[6];
        $best->[6] = 1;
    }
    return $n;
} ## end sub feat_advise

# --- the scorers -------------------------------------------------------------
sub value_score($bx, $t, $t_bag) {
    my (@free, $index, $value);
    @free = grep(!exists $t_bag->{$_}, @Goal);
    return 0 unless @free;
    $index = &max(@Priority[@free]);
    @free  = grep(($Priority[$_] >= $index), @free);
    $value = $MaxVal;
    foreach my $box (keys %$t_bag) {
        my $pb = $Priority[$box];    # fetch once (was read 2-3x per box)
        if (defined $pb and $pb >= $index) {

            # Covers both a real goal and a checkpoint park cell (see
            # Parser.pm::priority()) -- the latter is never in %Target, but
            # staging a box there temporarily is exactly what frees a
            # sibling goal's push-stance, so it earns the same reward.
            $value -= $MaxP * ($pb + 1);
        }
        elsif (exists $Distance->{$box}) {
            my $dist_bx = $Distance->{$box};
            my $best    = 0;
            for my $g (@free) {
                my $d = $dist_bx->{$g} // 0;
                $best = $d if $d > $best;
            }
            $value -= $best if $best;
        }
    } ## end foreach my $box (keys %$t_bag)

    # Flat same-scale route nudge, inlined: ($bx->$t) lies on some start box's
    # optimal route. The only survivor of the 3.3 bonus ablation (gate and cp
    # measured inert, this one carries games -- ablation of 2026-08-28).
    # $Macro_step suppresses it for a route-macro INTERMEDIATE: every push of
    # that macro runs along a route by construction and would collect the bonus
    # automatically, float to the queue front and spread the search's attention
    # over the macro's internal steps. Only the macro's LAST push may be
    # rewarded.
    $value -= $RouteBonus
        if !$Macro_step && exists $Route->{$bx} && exists $Route->{$bx}{$t};
    return $value;
} ## end sub value_score

# PUSH_ASSIGN scorer: optimal (min-cost) assignment of the not-yet-placed
# boxes to the free goals over RAW push distances ($DistRaw, Inf/unreachable
# -> $BIG). The min assignment cost IS the score -- lower is better. The
# matrix is square (#boxes-off-goal == #free-goals in a consistent state).
sub value_assign($bx, $t, $t_bag) {
    my @bag = grep {!$Target[$_]} keys %$t_bag;      # boxes not on a goal
    return 0 unless @bag;
    my @free = grep {!exists $t_bag->{$_}} @Goal;    # uncovered goals
    return $DistRaw->{ $bag[0] }{ $free[0] } // $BIG if @bag == 1;
    my @matrix;
    for my $g (@free) {
        push @matrix, [map {$DistRaw->{$_}{$g} // $BIG} @bag];
    }
    return Games::Sokoban::Solver::Munkres::assign(\@matrix);
}

# Turn a raw box->goal distance table (values are counts or the string 'Inf'
# for unreachable) into a numeric table with Inf/undef mapped to $BIG, so the
# assignment arithmetic never meets a non-number.
sub raw_table($src) {
    my %out;
    for my $bx (keys %$src) {
        my $row = $src->{$bx};
        $out{$bx}{$_} = (!defined $row->{$_} || $row->{$_} eq 'Inf') ? $BIG : $row->{$_}
            for keys %$row;
    }
    return \%out;
}

# MOVE_SUM scorer: additive sum of raw MOVE distances (walk+push) over every
# (not-yet-placed box, free goal) pair -- a coarse total-distance heuristic
# that shrinks as boxes near goals. Lower is better. NO cp bonus on purpose --
# see the $CP_mode_ok comment at the top.
sub value_move_sum($bx, $t, $t_bag) {
    my @bag = grep {!$Target[$_]} keys %$t_bag;
    return 0 unless @bag;
    my @free = grep {!exists $t_bag->{$_}} @Goal;
    my $sum  = 0;
    for my $b (@bag) {
        $sum += $DistRaw->{$b}{$_} // $BIG for @free;
    }
    return $sum;
}

# ROUTE scorer: prefer pushes that lie on some start box's optimal route (the
# $Route edge set) and on the forced common path. Coarse (a few discrete
# bands), lower is better -- a route-biased search. $t_bag is unused (scores
# the move itself).
sub value_route($bx, $t, $t_bag) {
    return 0 if $Macro_step;                      # macro intermediate: no route advantage
    my $r = $Route->{$bx};
    my $v = 0;
    $v -= 2 if $r          && $r->{$t};           # (bx -> t) on an optimal box route
    $v -= 1 if $CPath{$bx} && $CPath{$bx}{$t};    # ... and/or on the forced common path
    return $v;
}

# FLOW scorer: route-DOMINANT with a coarse secondary gradient. PRIMARY =
# ROUTE's ideal-path membership; it rewards moves ALONG the ideal path even
# when they push a box AWAY from a goal, which is what lets boxes transit
# through unoccupied goals. Scaled by $FLOW_W so it always outranks the
# secondary. SECONDARY = a coarsely BUCKETED remaining raw push-distance sum
# over the not-yet-placed boxes (each to its nearest still-free goal): a
# gentle gradient that does not recreate value_score's deep box-on-goal ridge.
sub value_flow($bx, $t, $t_bag) {
    my $r     = $Route->{$bx};
    my $route = 0;
    unless ($Macro_step) {    # macro intermediate: no route advantage
        $route -= 2 if $r          && $r->{$t};
        $route -= 1 if $CPath{$bx} && $CPath{$bx}{$t};
    }
    my $sum = 0;
    for my $b (keys %$t_bag) {
        next if $Target[$b];    # a box already on a goal: no term
        my $row  = $DistRaw->{$b} or next;
        my $best = $BIG;
        for my $g (@Goal) {
            next if exists $t_bag->{$g};    # nearest STILL-FREE goal only
            my $v = $row->{$g};
            $best = $v if defined $v && $v < $best;
        }
        $sum += $best if $best != $BIG;
    }
    return $route * $FLOW_W + int($sum / $FLOW_Q);
} ## end sub value_flow

# --- the deadlock battery ----------------------------------------------------
sub is_bad($bx, $t, $t_bag, $vb = undef) {

    # blok check, two gears: the hot tahy() path maintains the child box BIT
    # VECTOR $vb incrementally and pays one string AND + eq per pattern
    # (measured ~2x the hash loop; ':5.42' enables 'bitwise', so string AND is
    # the DOTTED &. operator; a trimmed pattern vec works on BOTH sides of the
    # length mismatch, because &. truncates to the shorter operand). Cold
    # callers (Order/Conveyor/route chains) pass no $vb and keep the
    # early-exit array loop over $Blok.
    if (defined $vb) {
        my $bvs = $BlokVec->{$bx} && $BlokVec->{$bx}{$t};
        if ($bvs) {
            foreach my $pv (@$bvs) {
                return 'blok' if ($vb &. $pv) eq $pv;
            }
        }
    }
    else {
        my $blok = $Blok->{$bx} && $Blok->{$bx}{$t};
        if ($blok) {

            # Plain labeled loop, not CORE::all -- benchmarked ~12-14% faster
            # on realistic pattern sizes since it avoids a per-element
            # block/closure call.
        BLK: foreach my $bl (@$blok) {
                foreach (@$bl) {
                    next BLK unless exists $t_bag->{$_};
                }
                return 'blok';
            }
        }
    } ## end else [ if (defined $vb) ]
    if ($Has_wall) {
        if (defined(my $wall = $Wall->{$t})) {
            foreach my $w (@$wall) {
                my $n = 0;
                foreach my $s (@{ $w->[1] }) {
                    ++$n if exists $t_bag->{$s};
                }
                return 'wall' if $n > $w->[0];
            }
        }
    }
    if ($Has_corridor) {
        if (defined(my $cor = $Corridor->{$bx} && $Corridor->{$bx}{$t})) {
            if ($cor->[2] =~ /^0+$/a) {
                my $n = 0;
                foreach my $s (@{ $cor->[0]; }) {
                    ++$n if exists $t_bag->{$s};
                }
                return 'corridor' if $n > 1;
            }
            else {
                $Maze[$_] =~ tr/03/47/ foreach keys %$t_bag;
                my $str = join('', @Maze[@{ $cor->[0]; }]);
                $Maze[$_] =~ tr/47/03/ foreach keys %$t_bag;
                confess("UNKNOWN Coridor pattern $$cor[2]") unless (exists $corridors->{ $cor->[2] });
                return 'corridor'                           unless ($corridors->{ $cor->[2] }{ $cor->[1] } // {})->{$str};
            }
        } ## end if (defined(my $cor = ...))
    } ## end if ($Has_corridor)
    if ($Has_hole) {
        if (defined(my $hole = $Hole->{$bx} && $Hole->{$bx}{$t})) {
            $Maze[$_] =~ tr/03/47/ foreach keys %$t_bag;
            my $str = join('', @Maze[@{ $hole->[0]; }]);
            $Maze[$_] =~ tr/47/03/ foreach keys %$t_bag;
            confess("UNKONWN Hole pattern $$hole[1]") unless exists $holes->{ $hole->[1] };
            return 'hole'                             unless $holes->{ $hole->[1] }{$str};
        }
    }
    return '';
} ## end sub is_bad

sub set_bad($pozice) {
    return if isbad $pozice;
    setbad $pozice;
    my @bads;

    # The cascade bookkeeping goes through the same tahy_* seam as the store
    # itself, in FirstbetBerk's write-back style -- tahy_get may return a
    # fresh arrayref, so never mutate the list in place.
    if (my $cached = tahy_get($pozice)) {
        tahy_del($pozice);
        @bads = @$cached;
    }
    if (my $father = delete $Parent{$pozice}) {
        if (my $list = tahy_get($father)) {
            my @kept = grep($_ ne $pozice, @$list);
            unless (@kept) {
                tahy_del($father);
                unshift @bads, $father;
            }
            else {tahy_set($father, \@kept);}
        }
    }
    set_bad($_) foreach @bads;
} ## end sub set_bad

# Matching-deadlock test. @boxes = the child's box cells (sorted). Returns 1
# if the position is matching-infeasible (=> deadlock), else 0. SOUND:
# single-box optimistic reachability over the FULL boxes x all-goals matrix
# means a zero-cost perfect matching is a NECESSARY condition for solvability,
# so its absence proves the position dead and can never reject a solvable one.
# Gated at the call site by $Match_active + $Selective{$t} + !exists
# $Parent{$child} (all lossless), so it runs at most once per new node.
sub matching_deadlock(@boxes) {

    # Fast path: if no box sits on a selective cell, every box reaches every
    # goal -> a perfect matching trivially exists -> not dead. O(n).
    my $any_sel = 0;
    for my $b (@boxes) {$any_sel = 1, last if $Selective{$b}}
    return 0 unless $any_sel;

    # Cheap Hall pre-check: if the goals reachable by the UNION of all boxes
    # number fewer than the boxes, no perfect matching can exist (skip the
    # Hungarian).
    my %union;
    for my $b (@boxes) {
        my $rg = $ReachG{$b} or return 0;    # missing data: never prune
        $union{$_} = 1 for keys %$rg;
    }
    return 1 if keys %union < @boxes;

    # Full Hungarian: square 0/$BIG cost matrix, boxes x @Goal. An optimal
    # cost >= $BIG means at least one box was forced onto an unreachable goal.
    my @matrix;
    for my $b (@boxes) {
        my $rg = $ReachG{$b};
        push @matrix, [map {$rg->{$_} ? 0 : $BIG} @Goal];
    }
    return Games::Sokoban::Solver::Munkres::assign(\@matrix) >= $BIG ? 1 : 0;
} ## end sub matching_deadlock

# Festival's fix_diagonals, ported and proved box for box against his own
# implementation. The rule looks at the HOLES, not the boxes: an empty cell
# whose four orthogonal neighbours are all occupied is a sealed pocket -- the
# player can never stand in it. A diagonal chain of such pockets, anchored at
# both ends and carrying no goal, has its flanks (which are occupied by
# construction, and are the boxes standing corner to corner) turned into
# walls. The claim is "this box never moves again" -- its evidence: 400
# replayed stored solutions, 34,063 tahu, none of the 159 boxes it declared
# fixed ever moved.
#
# Occupancy is tested INLINE ("occupied" = wall / already-walled / box;
# "walled" = wall / already-walled): the port wrapped these in two closures
# built per call and invoked hundreds of times per expansion, and the two sub
# calls cost more than the tests they wrapped. @IsWall is the per-game
# cell-indexed wall flag.
sub fix_diagonals ($bag, $wall) {
    my %w     = %$wall;
    my $h     = int(@Maze / $W);
    my $ncell = scalar @Maze;

    # CANDIDATES, not the whole board. A sealed pocket needs all four
    # orthogonal neighbours occupied, and "occupied" is a wall or a BOX (the
    # wall set holds boxes only -- the closing `delete` below guarantees it).
    # A pocket sealed by walls ALONE cannot exist in our games: it would be an
    # isolated cell, and Code.pm's dummy() bricks every player-unreachable
    # cell up (pipeline leak check 0 of 32,236 games). So every pocket touches
    # a box: the candidates are nbox x 4 cells instead of the whole board.
    my %cand;
    for my $b (keys %$bag) {
        $cand{ $b - $W } = 1;
        $cand{ $b + $W } = 1;
        $cand{ $b - 1 }  = 1;
        $cand{ $b + 1 }  = 1;
    }
    my (@inner, @pocket);
    for my $p (keys %cand) {
        next if $p < 0 || $p >= $ncell;                     # before the arrays: a negative index reads from the END
        my $i = int($p / $W);
        my $j = $p % $W;
        next if $i < 1 || $i > $h - 2 || $j < 1 || $j > $W - 2;
        next if $IsWall[$p] || $w{$p} || $bag->{$p};
        next if $Vis[$p] == $PaintId;                       # the player's own region
        my $n = $p - $W;
        next unless $IsWall[$n] || $w{$n} || $bag->{$n};    # p interior: neighbours in bounds
        $n = $p + $W;
        next unless $IsWall[$n] || $w{$n} || $bag->{$n};
        $n = $p + 1;
        next unless $IsWall[$n] || $w{$n} || $bag->{$n};
        $n = $p - 1;
        next unless $IsWall[$n] || $w{$n} || $bag->{$n};
        $inner[$p] = 1;
        push @pocket, $p;
    } ## end for my $p (keys %cand)
    my (@dr, @dl, @chain);
    for my $p (@pocket) {    # order-free: this scan only READS %w
        my $i = int($p / $W);
        my $j = $p % $W;
        for my $dir (1, -1) {
            my $up = $dir == 1 ? $p - $W - 1 : $p - $W + 1;
            my $sd = $dir == 1 ? $p - 1      : $p + 1;
            next
                unless ($IsWall[$up] || $w{$up} || $bag->{$up})
                || (($IsWall[$p - $W] || $w{ $p - $W }) && ($IsWall[$sd] || $w{$sd}));
            my $k = 1;
            ++$k while $inner[($i + $k) * $W + $j + $dir * $k];
            my $ep = ($i + $k) * $W + $j + $dir * $k;
            my $ed = $dir == 1 ? $ep - 1 : $ep + 1;
            next
                unless ($IsWall[$ep] || $w{$ep} || $bag->{$ep})
                || (($IsWall[$ep - $W] || $w{ $ep - $W }) && ($IsWall[$ed] || $w{$ed}));
            if   ($dir == 1) {$dr[$p] = $k}
            else             {$dl[$p] = $k}
        } ## end for my $dir (1, -1)
        push @chain, $p if $dr[$p] || $dl[$p];
    } ## end for my $p (@pocket)

    # Walls go down as the scan proceeds, exactly as the original does: both
    # the goal test and the wallification read the board being mutated. So
    # this one is NOT order-free -- and ascending cell index IS the original
    # row-major order, because a cell index is i * W + j.
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
            $w{$td} = 1 if $IsWall[$td] || $w{$td} || $bag->{$td};
            $w{$t}  = 1;
            my $e = ($i + $k) * $W + $j + $dir * $k;
            $w{$e} = 1 if $IsWall[$e] || $w{$e} || $bag->{$e};
            $w{ $e - $dir } = 1;
        } ## end for my $set ([$dr[$p], ...])
    } ## end for my $p (sort {$a <=>...})
    delete $w{$_} foreach grep {!$bag->{$_}} keys %w;    # report boxes only
    return \%w;
} ## end sub fix_diagonals

# Which cells can still reach goal $g once %$wall are walls? Backward BFS over
# the reverse push graph: an edge c -> t survives only if neither endpoint nor
# the player's stance for that push, $Cm{$c}{$t}, has become a wall. Memoized
# on the wall set, which changes rarely as a branch descends -- so this is
# paid once per distinct degenerated board, not once per position.
sub walled_reach ($wall, $key) {
    return $ReachW{$key} if exists $ReachW{$key};
    my %by_goal;
    for my $g (@Goal) {
        next if $wall->{$g};
        my %seen = ($g => 1);
        my @q    = ($g);
        while (@q) {
            my $t = shift @q;
            for my $c (@{ $Rev{$t} // [] }) {
                next if $seen{$c} || $wall->{$c};
                my $s = $Cm{$c}{$t};
                next if !defined $s || $wall->{$s};
                $seen{$c} = 1;
                push @q, $c;
            }
        }
        $by_goal{$g} = \%seen;
    } ## end for my $g (@Goal)
    return $ReachW{$key} = \%by_goal;
} ## end sub walled_reach

# matching_deadlock's question, asked on the DEGENERATED board. %ReachG is
# built once per game from the static steps table, so it never tightens and
# Hall's condition never starts failing however stuck the position gets; this
# rebuilds the edge set from the boxes that have frozen into walls. The edge
# set becomes the INTERSECTION of two over-approximations -- static
# player-aware %ReachG, and the backward BFS above which ignores the player
# but knows the new walls -- so it still contains every edge the truth
# contains, and an infeasible matching still PROVES the position dead. A box
# frozen on a goal leaves the problem altogether, taking its goal with it.
sub matching_dead_walled ($boxes, $wall) {
    return 0 unless $Walled_on;
    my $key = join(',', sort {$a <=> $b} keys %$wall);
    return 0 unless length $key;    # nothing frozen: the matrix cannot tighten
    my $wr = walled_reach($wall, $key);
    my @b  = grep {!$wall->{$_}} @$boxes;
    return 0 unless @b;
    my @g = grep {!$wall->{$_}} @Goal;
    return 1 if @b > @g;
    my (@matrix, %union);

    for my $b (@b) {
        my $rg = $ReachG{$b} or return 0;    # missing data: never prune
        my @row;
        for my $goal (@g) {
            my $ok = ($rg->{$goal} && $wr->{$goal} && $wr->{$goal}{$b}) ? 1 : 0;
            $union{$goal} = 1 if $ok;
            push @row, $ok ? 0 : $BIG;
        }
        push @matrix, \@row;
    }
    return 1 if keys %union < @b;    # Hall pre-check, skips the Hungarian
    return Games::Sokoban::Solver::Munkres::assign(\@matrix) >= $BIG ? 1 : 0;
} ## end sub matching_dead_walled

# --- the macros --------------------------------------------------------------
# Dead-end fill macro, shared by the hole and the 'one'-corridor cases. A
# 'one' corridor is, for filling, just a hole: once a box is pushed onto the
# entry it can only go deeper, so the goals fill deepest-first in a forced
# order. Called after the trigger push $bx->$t has landed a box on the entry
# ($t == cells[0]). $cells_ref = ordered cells (cells[0] == entry); $levels =
# the precomputed fill levels (deepest goal first), undef when the structure
# is not macro-eligible; $perm = permanent floor boxes stuck in the dead end
# (0 for a hole, $cor->[4] for a corridor). @$nb_ref is the box set AFTER the
# trigger push; $man_start = $bx (player behind it).
#
# $k = boxes already deeper in the dead end (minus $perm) -> which level
# (target goal) this box fills. Returns an @tahy-compatible list of
# (position, score) pairs: undef score marks a chain intermediate (link only,
# do not queue); the final fill push carries a real score. Empty list if the
# macro cannot fire. Reachability is checked with paint_fr()/@Vis_fr so the
# internal paints never disturb tahy()'s @Vis/$PaintId.
sub _macro_fill($cells_ref, $levels, $perm, $nb_ref, $man_start) {
    return () unless defined $levels;
    my @cells   = @$cells_ref;
    my %cur_bag = map(($_, 1), @$nb_ref);
    my $k       = (grep {exists $cur_bag{$_}} @cells[1 .. $#cells]) - $perm;
    return () if $k < 0 || $k >= @$levels;
    my $level  = $levels->[$k];
    my $target = $level->{'target'};
    my $pushes = $level->{'pushes'};
    return () if exists $cur_bag{$target};
    return () if grep {exists $cur_bag{$_}} @{ $level->{'free_path'} };
    my @chain;
    my @cur_nb = @$nb_ref;

    for my $pi (0 .. $#$pushes) {
        my ($from, $to, $push_pos) = @{ $pushes->[$pi] };
        my $cur_man = $pi == 0 ? $man_start : $pushes->[$pi - 1][0];
        paint_fr($cur_man, @cur_nb);

        # push_pos must be reachable FLOOR. paint_fr marks boxes in @Vis_fr
        # (as walls), so a Vis-hit on a box cell would falsely read as
        # reachable -- exclude a box-occupied stance.
        unless ($Vis_fr[$push_pos] == $PaintId_fr && !grep {$_ == $push_pos} @cur_nb) {

            # Player cannot reach this push stance -- stop the macro here and
            # turn the last (so-far intermediate) position into a real queued
            # one by giving it a score.
            if (@chain && !defined $chain[-1]) {
                my ($pf, $pt) = @{ $pushes->[$pi - 1] }[0, 1];
                $chain[-1] = $Value->($pf, $pt, { map(($_, 1), @cur_nb) });
            }
            last;
        }
        @cur_nb = grep($_ != $from, @cur_nb);
        my $j = 0;
        ++$j while $j < @cur_nb && $cur_nb[$j] < $to;
        splice(@cur_nb, $j, 0, $to);
        my $mc = _ck($from, \@cur_nb);    # class key
        push @chain, $mc, ($to == $target ? $Value->($from, $to, { map(($_, 1), @cur_nb) }) : undef);
    } ## end for my $pi (0 .. $#$pushes)
    return @chain;
} ## end sub _macro_fill

# Route-delivery macro: box $bx is pushed all the way onto the still-open goal
# $g along its precomputed optimal single-box route ($moves = box-cell
# sequence, $me = must_empty {cell=>1}). The CALLER has already applied the
# cheap O(1) gates (route exists, >=2 pushes, first target free, first push
# stance reachable now). $me (box path + player walks + push stances, computed
# on an empty field) captures exactly what must be box-free, so "no OTHER box
# in $me" is a SUFFICIENT idealized feasibility test: the sequence replays as
# single pushes with no per-step reachability check.
#
# EVERY step is QUEUED, and every step but the last is wrapped as [score] --
# "queue this AND stay the parent of the next chain step". An intermediate
# must NOT get the undef "chain intermediate" form the fill macro uses: %Parent
# membership IS the seen-set, so an undef step would be marked seen yet never
# expanded, and every continuation OTHER than the rest of this route would be
# lost for good -- the search then exhausts early and returns UNSOLVABLE on a
# solvable game. _macro_fill can do it because its intermediates sit inside a
# DEAD END where pushing on is the only continuation; a route's intermediate
# is an ordinary position with many.
#
# $Macro_step strips the route/gate/cp advantage from the intermediates: they
# run along a route by construction and would ALL collect the route bonus,
# crowding the queue front. The reward belongs to the LAST push alone -- the
# one that parks the box on the goal.
sub _route_deliver($baggage, $bx, $moves, $me) {
    for my $b (@$baggage) {
        return () if $b != $bx && $me->{$b};    # a foreign box sits on the idealized route -> infeasible
    }

    # Dedup early-out: the delivered endpoint (box on the goal $moves[-1],
    # player on the last vacated cell $moves[-2]) is what this whole macro
    # exists to reach. If it is already in %Parent it has a path -- rebuilding
    # the chain (is_bad+pack per step) would only be discarded.
    my $g     = $moves->[-1];
    my @fnb   = sort {$a <=> $b} map {$_ == $bx ? $g : $_} @$baggage;
    my $final = _ck($moves->[-2], \@fnb);
    return () if exists $Parent{$final};
    my @cur  = @$baggage;
    my $prev = $bx;
    my @chain;

    for my $i (0 .. $#$moves) {
        my $next = $moves->[$i];
        my @nb   = grep {$_ != $prev} @cur;
        my $j    = 0;
        ++$j while $j < @nb && $nb[$j] < $next;
        splice(@nb, $j, 0, $next);
        my %nbag = map(($_, 1), @nb);
        return () if is_bad($prev, $next, \%nbag);
        my $child = _ck($prev, \@nb);
        return () if isbad($child);
        my $last = $i == $#$moves;
        $Macro_step = !$last;
        my $sc = $Value->($prev, $next, \%nbag);
        $Macro_step = 0;
        push @chain, $child, ($last ? $sc : [$sc]);
        @cur  = @nb;
        $prev = $next;
    } ## end for my $i (0 .. $#$moves)
    return @chain;
} ## end sub _route_deliver

# Conveyor-delivery macro (cp package): from the conveyor edge at $start_idx
# (whose push the CALLER has verified: box on source, target free, stance
# reachable on @Vis) ride the box down the REST of the conveyor, then deliver
# it from the endpoint to a deepest-rank free goal along the precomputed
# $Game{to_goal} route. EVERY step is queued as [score] (chain-start form --
# the %Parent-is-seen trap above), and no $Macro_step suppression: every
# conveyor push earns the full sledge bonus, which is exactly what pulls the
# whole ride to the queue front. Per-step reachability uses paint_fr/@Vis_fr
# (own arrays), so tahy()'s @Vis flood stays valid.
# Failure semantics: a skipped or refused ride edge keeps the steps queued so
# far but forfeits the delivery; a step already in %Parent aborts as pure
# dedup (that child offered this same continuation when IT was generated); a
# failed goal delivery re-roots the chain at the endpoint (by re-emitting it)
# and tries the next goal.
sub _cp_deliver($baggage, $start_idx) {
    my @cur = @$baggage;
    my %bag = map(($_, 1), @cur);
    my (@chain, $man, $missed, $last_child, $last_sc);
    for my $i ($start_idx .. $#CPathArr) {
        my ($s, $t) = @{ $CPathArr[$i] };
        unless (exists $bag{$s} && !exists $bag{$t}) {$missed = 1; next;}
        my $stance = $Cm{$s}{$t};
        unless (defined $stance) {$missed = 1; next;}
        if     (defined $man) {                         # first ride step's stance was checked by the caller on @Vis
            paint_fr($man, @cur);
            unless ($Vis_fr[$stance] == $PaintId_fr && !grep {$_ == $stance} @cur) {
                $missed = 1;
                next;
            }
        }
        my @nb = grep {$_ != $s} @cur;
        my $j  = 0;
        ++$j while $j < @nb && $nb[$j] < $t;
        splice(@nb, $j, 0, $t);
        my %nbag  = map(($_, 1), @nb);
        my $child = _ck($s, \@nb);
        if (exists $Parent{$child}) {$missed = 1; last;}                    # dedup: its generator already offered the rest
        if (is_bad($s, $t, \%nbag)) {set_bad($child); $missed = 1; last;}
        if (isbad($child))          {$missed = 1; last;}
        my $sc = $Value->($s, $t, \%nbag);
        push @chain, $child, [$sc];
        ($last_child, $last_sc) = ($child, $sc);
        @cur = @nb;
        %bag = %nbag;
        $man = $s;
    } ## end for my $i ($start_idx .....)
    return @chain if $missed || !defined $last_child || !%ToGoal;

    # complete ride: the box sits on the conveyor endpoint -- deliver it
    my @free = grep {!exists $bag{$_}} @Goal;
    return @chain unless @free;
    my $index = &max(map {$Priority[$_] // 0} @free);
    @free = grep {($Priority[$_] // 0) == $index} @free;
    my $first_attempt = 1;
GOAL: foreach my $g (@free) {
        my $tg = $ToGoal{$g} or next GOAL;
        push @chain, $last_child, [$last_sc] unless $first_attempt;    # re-root the thread at the endpoint
        $first_attempt = 0;
        my @dcur = @cur;
        my %dbag = %bag;
        my $dman = $man;
        my $ok   = 1;
        foreach my $mv (@$tg) {
            my ($s, $t) = @$mv;
            unless (exists $dbag{$s} && !exists $dbag{$t}) {$ok = 0; last;}
            my $stance = $Cm{$s}{$t};
            unless (defined $stance) {$ok = 0; last;}
            paint_fr($dman, @dcur);
            unless ($Vis_fr[$stance] == $PaintId_fr && !grep {$_ == $stance} @dcur) {
                $ok = 0;
                last;
            }
            my @nb = grep {$_ != $s} @dcur;
            my $j  = 0;
            ++$j while $j < @nb && $nb[$j] < $t;
            splice(@nb, $j, 0, $t);
            my %nbag  = map(($_, 1), @nb);
            my $child = _ck($s, \@nb);
            if (exists $Parent{$child}) {$ok = 0; last;}
            if (is_bad($s, $t, \%nbag)) {set_bad($child); $ok = 0; last;}
            if (isbad($child))          {$ok = 0; last;}
            my $sc = $Value->($s, $t, \%nbag);
            push @chain, $child, [$sc];
            @dcur = @nb;
            %dbag = %nbag;
            $dman = $s;
        } ## end foreach my $mv (@$tg)
        last GOAL if $ok;    # full delivery threaded
    } ## end GOAL: foreach my $g (@free)
    return @chain;
} ## end sub _cp_deliver

# --- PI-corral restriction (always on since 2026-09-09) ----------------------
# Treat the boxes as walls and the free cells fall into areas. The player is in
# one of them; any other is one he cannot reach now. Such an area is a PI-corral
# when no box on its boundary can be pushed AWAY from it (every push on the
# boundary goes inward) and every one of those inward pushes is available to him
# THIS INSTANT. Then nothing done elsewhere improves the situation and nothing is
# gained by waiting -- pushing a boundary box inward only ENLARGES his region, so
# whatever a solution did outside first can still be done afterwards. The search
# may therefore generate ONLY the pushes on that boundary. It is a proof, not a
# heuristic, which is why it may cut as hard as it does: measured over stored
# solutions, a corral stands on 45 % of a solution's positions and cuts the move
# list there from 6.7 candidates to 2.0.
#
# IT KEPT A SWITCH FOR A FORTNIGHT, AND THE SWITCH IS GONE (2026-09-09, USER).
# The promotion in 3.1 left $CORRAL behind because of what 80 games said: as a
# REPLACEMENT the corral was worth -3 games (66 solved by both arms, 3 only with
# it, 6 only without), and as an alternating ARM +3, since those six stay
# solvable by the same engine with the corral off. The losses are not a property
# of the board -- the losing boards are indistinguishable from the rest in size,
# box density, how often the corral fires and how hard it cuts, and on the one
# traced in full (game 7) nothing was killed, the search simply went elsewhere
# and did not come back. The restriction does not shrink the tree, it RESHUFFLES
# it, and the reshuffle sometimes lands badly.
#
# What removed the switch was not a new measurement but the campaign record. The
# off arm ran on 2026-08-25, the day of that A/B (683 rows), and once more on
# 08-29 -- and never again; every campaign since has been corral on. Exactly ONE
# game in the whole database was solved by an off-arm run and by nothing else.
# So the arm was not being alternated, and a switch with one used value is not a
# switch. The -3 also belongs to engine 3.1: 3.2 through 3.5 have since changed
# the memory teardown, the score bonuses, FEATURE's advice and BACKWARD's store.
# Behaviour here is unchanged by the removal -- the default was ON and every
# driver set it ON -- which is why $VERSION does not move.
#
# Two things are deliberate. The candidate test asks the PUSH GRAPH, not
# geometry, so an area no legal push reaches is never even looked at -- the
# geometric seeding Festival uses was tried and dropped (it made sealed areas
# visible, but blok and the frozen check already killed 99.2 % of what those
# condemned, and it tripped the closed-corral-on-a-solution invariant once).
# And the whole thing rides on paint(): @Vis IS the player's region and @Blk the
# box set, both stamped $PaintId, so the flood is not paid twice.
my (@CComp, @CFloor, @CInC, @CorralCells, @CStamp, @CTouch, @Nb4, @Nb8);
my ($CGen, $CTag, $CTouchGen) = (0, 0, 0);

sub _corral_geom() {
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

    # the corral's boundary boxes are the 8-neighbourhood of its cells, the
    # straddling test the 4-; the column compare rejects a flat index's row wrap
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
    return;
} ## end sub _corral_geom

# The boxes on the corral's boundary -- the 8-neighbourhood of its cells -- left
# stamped in @CTouch with the returned generation. That stamp is the OCCUPANCY
# rule for everything below, and it is the whole soundness of this block:
#
# a cell counts as blocked only when a BOUNDARY box stands on it. Every other
# box on the board is treated as ABSENT. Festival does this by clearing all the
# boxes off a scratch board and re-marking only the boundary ones, and it is not
# an optimisation -- it is what makes the corral STATIC. A boundary box that
# could be pushed clear of the corral once some other box gets out of the way is
# an escape, so the area is not sealed and the restriction must not apply. Let
# any box block that escape and the test starts accepting corrals that other
# moves can open, the search cuts the branch that would have opened one, and a
# solvable game comes back UNSOLVABLE. (It did: game 16442, 2026-08-24.)
sub _corral_boxes($pid, $ccells) {
    my $t = ++$CTouchGen;
    my @b;
    for my $p (@$ccells) {
        foreach my $q (@{ $Nb8[$p] }) {
            next if $Blk[$q] != $pid or $CTouch[$q] == $t;
            $CTouch[$q] = $t;
            push @b, $q;
        }
    }
    return \@b;
}

sub _corral_try($g, $pid, $c0, $nc) {
    my $tag  = ++$CTag;
    my @used = (0) x ($nc + 1);
    $used[$c0] = 1;
    my @ccells = @{ $CorralCells[$c0] };
    $CInC[$_] = $tag foreach @ccells;
    my $cboxes = _corral_boxes($pid, \@ccells);
    my $btag   = $CTouchGen;                      # only a box stamped with this blocks anything

    # work left inside: an uncovered goal in the corral, or a boundary box
    # off-goal. Without either there is nothing to be gained by restricting.
    my $active = 0;
    for my $p (@ccells) {$active = 1, last if $Target[$p]}
    if (!$active) {for my $b (@$cboxes) {$active = 1, last unless $Target[$b]}}
    return undef unless $active;

    # a boundary box whose push reaches a further area he cannot enter either:
    # swallow that area and ask again
EXPAND: while (1) {
        my $add;
    BOX: for my $b (@$cboxes) {
            my ($in, $out) = (0, 0);
            foreach my $q (@{ $Nb4[$b] }) {
                if    ($CInC[$q] == $tag)    {$in  = 1}
                elsif ($CTouch[$q] != $btag) {$out = 1}
            }
            next unless $in and $out;
            foreach my $t (@{ $Cmk{$b} }) {
                next if $CTouch[$t] == $btag;
                my $st = $Cm{$b}{$t};
                next unless defined $st;
                next if $CTouch[$st] == $btag;
                if ($CInC[$t] == $tag and $CInC[$st] != $tag) {
                    my $c = $CStamp[$st] == $g ? $CComp[$st] : 0;
                    if ($c and !$used[$c]) {$add = $c; last BOX}
                }
                elsif ($CInC[$t] != $tag and $CInC[$st] != $tag) {
                    my $c = $CStamp[$t] == $g ? $CComp[$t] : 0;
                    if ($c and !$used[$c]) {$add = $c; last BOX}
                }
            }
        } ## end BOX: for my $b (@$cboxes)
        last EXPAND unless defined $add;
        $used[$add] = 1;
        push @ccells, @{ $CorralCells[$add] };
        $CInC[$_] = $tag foreach @{ $CorralCells[$add] };
        $cboxes   = _corral_boxes($pid, \@ccells);
        $btag     = $CTouchGen;
    } ## end EXPAND: while (1)

    # Sealed? A push with BOTH stance and landing outside breaks the argument.
    # Blocked ONLY by walls and boundary boxes -- an escape another box merely
    # stands in the way of is still an escape, because that box can move.
    for my $b (@$cboxes) {
        foreach my $t (@{ $Cmk{$b} }) {
            next if $CTouch[$t] == $btag or $CInC[$t] == $tag;
            my $st = $Cm{$b}{$t};
            next unless defined $st;
            next if $CTouch[$st] == $btag or $CInC[$st] == $tag;
            return undef;
        }
    }

    # and every push INTO it must be his to make right now
    for my $b (@$cboxes) {
        foreach my $t (@{ $Cmk{$b} }) {
            next if $CTouch[$t] == $btag or $CInC[$t] != $tag;
            my $st = $Cm{$b}{$t};
            next unless defined $st;
            next if $CTouch[$st] == $btag or $CInC[$st] == $tag;
            return undef unless $Vis[$st] == $pid;
        }
    }
    my %allowed;
    for my $b (@$cboxes) {
        foreach my $t (@{ $Cmk{$b} }) {
            next if $CTouch[$t] == $btag or $CInC[$t] != $tag;
            my $st = $Cm{$b}{$t};
            next unless defined $st;
            next             if $CTouch[$st] == $btag or $CInC[$st] == $tag;
            $allowed{$b} = 1 if $Vis[$st] == $pid;
        }
    }
    return %allowed ? \%allowed : undef;
} ## end sub _corral_try

# Returns the set of boxes the search may still touch, or undef when no corral
# holds. Call ONLY after paint($man, @baggage).
sub corral_allowed($bag) {
    my $g   = ++$CGen;
    my $pid = $PaintId;
    my $nc  = 0;
    @CorralCells = (undef);
    for my $p (@CFloor) {
        next if $Vis[$p] == $pid or $Blk[$p] == $pid or $CStamp[$p] == $g;
        my $c = ++$nc;
        my @s = ($p);
        $CStamp[$p] = $g;
        $CComp[$p]  = $c;
        for (my $i = 0; $i < @s; ++$i) {
            foreach my $t (@{ $Cg[$s[$i]] }) {
                next if $CStamp[$t] == $g or $Vis[$t] == $pid or $Blk[$t] == $pid;
                $CStamp[$t] = $g;
                $CComp[$t]  = $c;
                push @s, $t;
            }
        }
        $CorralCells[$c] = \@s;
    } ## end for my $p (@CFloor)
    return undef unless $nc;
    my @cand = (0) x ($nc + 1);
    foreach my $bx (@$bag) {
        foreach my $t (@{ $Cmk{$bx} }) {
            next if $Blk[$t] == $pid;
            my $st = $Cm{$bx}{$t};
            next unless defined $st       and $Vis[$st] == $pid;
            next unless $CStamp[$t] == $g and $CComp[$t];
            $cand[$CComp[$t]] = 1;
        }
    }
    for my $c (1 .. $nc) {
        next unless $cand[$c];
        my $allowed = _corral_try($g, $pid, $c, $nc);
        return $allowed if defined $allowed;
    }
    return undef;
} ## end sub corral_allowed

# --- the move generator ------------------------------------------------------
sub tahy($pozice) {
    my ($man, @baggage) = unpack($pu, $pozice);
    my ($s, $child, @tahy, @nomove, @children, %bags);
    my $skipped = 0;    # known-class skips at THIS position (drives the not-dead branch in _tahy_macros)
    %bags = map(($_, 1), @baggage);
    paint($man, @baggage);
    @tahy = ();

    # Cross-run move cache: a position expanded in a PREVIOUS run of this game
    # already knows its surviving children -- candidate enumeration, stance
    # reachability, the whole is_bad battery, matching and the frozen check
    # are all DETERMINISTIC per position, so on a cache hit none of them needs
    # to run again. What must be redone: isbad() per child (the Bad cache may
    # have grown since), the score (children lists are mode-independent,
    # scores are not) and the hole/corridor macro offers (their chains queue
    # NEW positions each run); the route/cp macros are position-level and run
    # for both paths. Within a single run this never fires (a position is
    # expanded at most once -- %Parent is the seen-set); it fires on a RETRY
    # or a later WAVE in FirstbetBerk, where the store persists.
    # paint() above is still needed: the macro gates test @Vis reachability.
    #
    # INVARIANT (do not break): a cache hit must return exactly what a COLD
    # expansion of this position would return TODAY. That holds because every
    # skipped test depends on NOTHING but the position itself; the two
    # stateful inputs -- the Bad cache (grows monotonically, possibly by OTHER
    # modes' runs) and the current mode -- are re-applied on every hit (isbad
    # filter, re-score). If you ever add a check to the is_bad battery /
    # matching / frozen that reads anything beyond the position, it MUST run
    # on the cache-hit path too, or the cache will lie.
    if (defined(my $cached = $Tahy{$pozice})) {
        foreach my $ch (@$cached) {
            next if exists $MemBad{$ch};
            my (undef, @nb) = unpack($pu, $ch);              # man is the CLASS cell, not the vacated one
            my %nbag = map(($_, 1), @nb);
            my ($t)  = grep {!exists $bags{$_}} @nb;         # the pushed box's new cell
            my ($bx) = grep {!exists $nbag{$_}} @baggage;    # the cell it left == player after the push
            my $sc   = $Value->($bx, $t, \%nbag);
            my @chain;
            if ($Has_hole) {
                if (defined(my $hole = $Hole->{$bx} && $Hole->{$bx}{$t})) {
                    @chain = _macro_fill($hole->[0], $hole->[2], 0, \@nb, $bx);
                }
            }
            if (!@chain && $Has_corridor) {
                if (defined(my $cor = $Corridor->{$bx} && $Corridor->{$bx}{$t})) {
                    @chain = _macro_fill($cor->[0], $cor->[3], $cor->[4] // 0, \@nb, $bx);
                }
            }
            if (@chain) {push @tahy, $ch, [$sc], @chain;}
            else        {push @tahy, $ch, $sc;}
            push @children, $ch;
        } ## end foreach my $ch (@$cached)
        if    (!@children)            {tahy_del($pozice)}                 # all dead now: the tail set_bads $pozice
        elsif (@children != @$cached) {tahy_set($pozice, [@children])}    # re-store pruned of the now-bad
        return _tahy_macros($pozice, $man, \@baggage, \%bags, \@tahy);
    } ## end if (defined(my $cached...))

    # $vb = the box set as a bit vector, mutated in LOCKSTEP with %bags below,
    # so is_bad's hot blok test is one string AND per pattern. Built once per
    # position, amortized over all its candidates.
    my $vb = '';
    vec($vb, $_, 1) = 1 foreach @baggage;

    # The corral restriction, asked once per position and only on a COLD
    # expansion -- a cache hit already holds the restricted list. It suppresses
    # child GENERATION only, never the $movable scan below: @nomove feeds
    # is_frozen, and a box withheld by the corral is not an immovable box.
    my $callow = corral_allowed(\@baggage);
    foreach my $bx (@baggage) {
        my $movable = 0;
        my $cskip   = $callow && !$callow->{$bx};

        # %bags is reused AS the child box-set ($t_bag) by mutation instead of
        # allocating a fresh hash per candidate: lift $bx off here, drop each
        # target $t in below (and remove it again), then restore $bx after the
        # inner loop -- so %bags holds exactly the post-push set during
        # is_bad()/value() and is intact (== @baggage) for the frozen check.
        delete $bags{$bx};
        vec($vb, $bx, 1) = 0;
        foreach my $t (@{ $Cmk{$bx}; }) {
            next if exists $bags{$t};
            $s = $Cm{$bx}{$t};
            next unless $Vis[$s] == $PaintId;
            ++$movable;
            next if $cskip;    # the corral says this box is irrelevant right now
            my @nb = grep($_ != $bx, @baggage);
            my $i  = 0;
            ++$i while $i < @nb && $nb[$i] < $t;
            splice(@nb, $i, 0, $t);

            # class key: region-min for the player at $bx; one flood per
            # DISTINCT raw key ever born, a hash hit for every repeat
            $child = $CanonMap{ pack($pu, $bx, @nb) } //= canon_key($bx, \@nb);
            if (exists $MemBad{$child}) {
                next;
            }

            # Known-class skip: a candidate whose class is already alive in
            # %Parent paid the whole battery, matching, score and macro build
            # at its first birth, and the search loop would drop it as SEEN
            # anyway -- so drop it HERE and skip all that work. The child must
            # STILL enter the cached children list -- the set_bad cascade's
            # bookkeeping (down-kill set, up-exhaustion test) must see the
            # same list as without the filter; and $skipped must reach
            # _tahy_macros, where an empty @tahy with skips means "nothing
            # NEW", never "dead". (Forfeited on purpose: is_bad is indexed by
            # the MOVE, so a repeat birth under the second push direction
            # loses that direction's rare extra kill -- weaker pruning only.)
            if (exists $Parent{$child}) {
                ++$skipped;
                push @children, $child;
                next;
            }
            $bags{$t} = 1;    # %bags now == child box-set
            vec($vb, $t, 1) = 1;
            my $bad = is_bad($bx, $t, \%bags, $vb);
            if ($bad) {
                set_bad $child;
            }
            elsif ($Match_active && $Selective{$t} && matching_deadlock(@nb)) {

                # Matching-infeasible child: boxes can no longer be assigned
                # 1:1 to reachable goals -> dead. Prune exactly like is_bad.
                set_bad $child;
            }
            else {
                # FEATURE's explorer poradce: this push is reversible and it
                # lets the player reach a square from which some OTHER box can
                # now be pushed. %bags is the child's box set here, and the
                # pushed box now stands on $t.
                if ($Feat_mode && exists $Cm{$t}{$bx} && $RegCells{$child}) {
                CELL: for my $c (@{ $RegCells{$child} }) {
                        for my $pair (@{ $StanceIdx{$c} // [] }) {
                            my ($ob, $ot) = @$pair;
                            next if $ob == $t;                # not the box we just moved
                            next unless exists $bags{$ob};    # a box must actually stand there
                            next if exists $bags{$ot};        # and its target must be free
                            $ExplMark{$child} = 1;
                            last CELL;
                        }
                    }
                }
                my $sc = $Value->($bx, $t, \%bags);
                my @chain;

                # Dead-end fill macro: this push lands the box on a hole or
                # 'one'-corridor entry ($t = cells[0]). Entering does NOT
                # force the box all the way in -- the search may do other
                # moves and fill later. So SOFTEN the commitment: queue the
                # entry push $child as an ordinary move (real score, a real
                # child) AND additionally offer the fill as a shortcut chain.
                # The trigger's score is wrapped as [$sc] -- "queue this AND
                # start the chain" -- so the fill positions are parented
                # $child -> ... -> final while $child itself stays a normal,
                # independently-expandable frontier node. A cell is at most
                # one entry; the corridor is tried only if no hole fired.
                if ($Has_hole) {
                    if (defined(my $hole = $Hole->{$bx} && $Hole->{$bx}{$t})) {
                        @chain = _macro_fill($hole->[0], $hole->[2], 0, \@nb, $bx);
                    }
                }
                if (!@chain && $Has_corridor) {
                    if (defined(my $cor = $Corridor->{$bx} && $Corridor->{$bx}{$t})) {
                        @chain = _macro_fill($cor->[0], $cor->[3], $cor->[4] // 0, \@nb, $bx);
                    }
                }
                if (@chain) {
                    push @tahy,     $child, [$sc];
                    push @tahy,     @chain;
                    push @children, $child;
                }
                else {
                    push @tahy, $child, $sc;
                    push @children, $child;
                }
            } ## end else [ if ($bad) ]
            delete $bags{$t};    # undo the mutation before the next candidate
            vec($vb, $t, 1) = 0;
        } ## end foreach my $t (@{ $Cmk{$bx}...})
        $bags{$bx} = 1;          # box back: %bags intact for the frozen check
        vec($vb, $bx, 1) = 1;
        push @nomove, $bx unless $movable;
    } ## end foreach my $bx (@baggage)
    if (@children) {
        $Tahy{$pozice} = [@children];
    }

    # Frozen-cluster / goal-corral deadlock check -- can reject this position
    # even when @tahy is non-empty, since a permanently stuck subset of boxes
    # dooms the position regardless of what other boxes can still do.
    # (Cache-hit expansions skip it: the position passed this deterministic
    # check when it was first expanded.)
    my @frozen_set;
    if (@nomove) {
        my $frozen_bad;
        ($frozen_bad, @frozen_set) = is_frozen($man, @nomove);
        if ($frozen_bad) {
            set_bad $pozice;    # also clears $Parent/$Tahy for $pozice
            return ();
        }
        if (@frozen_set) {
            my @open = grep {!exists $bags{$_}} @Goal;
            if (@open) {

                # @Vis_fr already reflects paint_fr($man, @frozen_set):
                # is_frozen's LAST paint (its converged fixed point) is
                # exactly that -- same $man, same box-set -- and nothing
                # repaints between its return and here. Reuse it rather than
                # repaint (paint_fr is the module's single hottest cost).
                for my $g (@open) {
                    if ($Vis_fr[$g] != $PaintId_fr) {
                        set_bad $pozice;
                        return ();
                    }
                }
            }
        } ## end if (@frozen_set)
    } ## end if (@nomove)

    # Board degeneration + wallified matching. Deliberately OUTSIDE the
    # @nomove block: on 35362 is_frozen finds nothing at all, yet the diagonal
    # rule walls most of the board, so hanging this off @frozen_set would
    # never let it speak. @Vis still holds this position's flood (nothing
    # since the top of tahy() repaints it) and fix_diagonals needs it.
    #
    # Iterated, because each rule feeds the other: a diagonally fixed box is
    # one more occupied cell, which can seal another pocket.
    if ($Walled_on) {
        my %wall = map(($_, 1), @frozen_set);
        while (1) {
            my $more = fix_diagonals(\%bags, \%wall);
            my $grew = 0;
            for my $c (keys %$more) {$grew = 1 unless $wall{$c}++}
            last unless $grew;
        }
        if (%wall) {

            # A box that can never move again and is not on a goal can never
            # be delivered -- the same conclusion is_frozen draws for its own
            # set, extended to the boxes the diagonal rule fixes.
            for my $b (keys %wall) {
                unless ($Target[$b]) {
                    set_bad $pozice;
                    return ();
                }
            }
            if (matching_dead_walled(\@baggage, \%wall)) {
                set_bad $pozice;
                return ();
            }
        } ## end if (%wall)
    } ## end if ($Walled_on)
    return _tahy_macros($pozice, $man, \@baggage, \%bags, \@tahy, $skipped);
} ## end sub tahy

# The mode-independent position-level macros + the common tail of tahy(),
# shared by the cold path and the cache-hit path. Expects @Vis to still hold
# this position's paint() flood (both callers paint at their top; nothing in
# between touches @Vis).
sub _tahy_macros($pozice, $man, $baggage, $bags, $tahy, $skipped = 0) {
    \my @baggage = $baggage;
    \my %bags    = $bags;
    \my @tahy    = $tahy;

    # Route-delivery macros: for each box, offer a one-shot macro that pushes
    # it straight onto an open goal along its precomputed route whenever that
    # route is clear now. Mode-independent, exactly like the hole/corridor
    # macros in the push loop -- placed here (after the deadlock filters, on a
    # surviving position) so every forward scorer benefits equally. Only fires
    # on blobs that carry $Game{routes} ($Has_routes).
    if ($Has_routes) {
        my @open = grep {!$bags{$_}} @Goal;
        for my $bx (@baggage) {
            my $rb = $RouteMoves->{$bx} or next;
            for my $g (@open) {
                my $moves = $rb->{$g} or next;
                next unless @$moves >= 2;                              # 1-push delivery is just an ordinary move
                my $first = $moves->[0];
                next if $bags{$first};                                 # first box target occupied
                my $st1 = $Cm{$bx}{$first};
                next unless defined $st1 && $Vis[$st1] == $PaintId;    # player reaches the first stance now
                my @chain = _route_deliver(\@baggage, $bx, $moves, $RouteMust->{$bx}{$g}) or next;
                push @tahy, @chain;
            }
        }
    } ## end if ($Has_routes)

    # Conveyor-delivery macro (cp package): a box standing on a conveyor edge
    # source with the target free and the push stance reachable NOW offers the
    # ride-to-end + deliver-to-goal chain. Placed LAST on purpose: _cp_deliver
    # floods @Vis_fr for its per-step reachability, which would otherwise
    # clobber the flood the goal-corral check reuses; tahy()'s own @Vis flood
    # stays untouched throughout.
    if ($Has_cp && $CP_mode_ok) {
        for my $bx (@baggage) {
            my $row = $CPathIdx{$bx} or next;
            for my $t (keys %$row) {
                next if exists $bags{$t};
                my $st = $Cm{$bx}{$t};
                next unless defined $st && $Vis[$st] == $PaintId;

                # THE CHAIN IS CLOSED HERE. _cp_deliver marks every step [score]
                # -- "the next step descends from me" -- its last one included,
                # and with two boxes on conveyor edges one position offers two
                # rides: the first step of the second was then linked to the
                # last step of the first, a position it is not one push from,
                # and get_path() rebuilt a path with a push missing (game 5469
                # ROUTE, found by the matrix on 2026-10-07). The last step gets
                # the plain score, which queues it the same and ends the thread.
                my @ride = _cp_deliver(\@baggage, $row->{$t}) or next;
                $ride[-1] = $ride[-1][0];
                push @tahy, @ride;
            } ## end for my $t (keys %$row)
        } ## end for my $bx (@baggage)
    } ## end if ($Has_cp && $CP_mode_ok)
    if (@tahy) {
        return @tahy;
    }
    elsif ($skipped) {

        # Every candidate was dropped as a KNOWN ALIVE class -- the position
        # offers nothing new, but it is NOT dead. Declaring it dead here was
        # the skip filter's one real bug: the set_bad cascade then killed the
        # living skipped children (they are in the cached list) and orphaned
        # their chain descendants (the NOT A START crash).
        return ();
    }
    else {
        set_bad $pozice;
        return ();
    }
} ## end sub _tahy_macros

# Scoring + deadlock precompute for the FORWARD scorers (incl FLOW), ORDER and
# CONVEYOR. Reads the new Parser blob keys with a fallback to the old names,
# so it works on both blob generations.
sub initvars_score($mode) {

    # Portfolio scoring metric + scorer dispatch. $Value is the code-ref the
    # search calls per node. The score modes share one body (value_score) and
    # differ only in which precomputed quadratized table + scale constants
    # feed it; PUSH_ASSIGN/MOVE_SUM/FLOW run their own bodies over RAW tables.
    # MOVE_SUM keeps its baseline behavior: no cp bonus, no to_end hook.
    $CP_mode_ok = $mode eq 'MOVE_SUM' ? 0 : 1;
    if ($Feat_mode) {

        # Since 3.4 FEATURE scores every queued child after all (the 2.15
        # design left $MaxP unset and the mode distance-free): the PUSH_SCORE
        # quad tables feed value_score, and the score enters the search ONLY
        # as advice -- a sixth poradce names the best-scored child of a
        # litter, and inside a feature cell it breaks the ties of equal
        # weights. The primary order is still the feature cells plus the
        # advisor weights. Measured on paired halves (2026-08-28): +9/-0
        # solve flips on the paired halves, 1.31x fewer positions, at ~15 %
        # per-position cost; games 5 and 20 (Classic Collection) solved for
        # the first time by anything.
        $MaxP     = $Game{'maxp_steps'}   // $Game{'maxp_push'};
        $MaxVal   = $Game{'maxval_steps'} // $Game{'maxval_push'};
        $Distance = &dclone($Game{'steps_quad'} // $Game{'zbytek'});
        $Value    = \&value_score;
    } ## end if ($Feat_mode)
    elsif ($mode eq 'PUSH_ASSIGN') {

        # Hungarian min-cost assignment over raw push distances
        $DistRaw = raw_table($Game{'steps'} // $Game{'zbytek_raw'});    # new // old
        $Value   = \&value_assign;
    }
    elsif ($mode eq 'MOVE_SUM') {

        # additive sum of raw MOVE distances over all (box, free-goal) pairs
        $DistRaw = raw_table($Game{'distance_raw'} // $Game{'distance'});
        $Value   = \&value_move_sum;
    }
    elsif ($mode eq 'ROUTE') {

        # score by route-edge membership (+ common path); $Route/%CPath below
        $Value = \&value_route;
    }
    elsif ($mode eq 'FLOW') {

        # route-dominant flatter scorer; raw push table for the coarse
        # secondary gradient, route/%CPath set below
        $DistRaw = raw_table($Game{'steps'} // $Game{'zbytek_raw'});    # new // old
        $Value   = \&value_flow;
    }
    else {
        if ($mode eq 'MOVE_SCORE') {

            # quadratized total-move steps (walk + push)
            $MaxP     = $Game{'maxp'};
            $MaxVal   = $Game{'maxval'};
            $Distance = &dclone($Game{'distance_quad'} // $Game{'distance'});    # new // old
        }
        else {
            # PUSH_SCORE (default/baseline): quadratized push-count steps
            $MaxP     = $Game{'maxp_steps'}   // $Game{'maxp_push'};             # new // old
            $MaxVal   = $Game{'maxval_steps'} // $Game{'maxval_push'};
            $Distance = &dclone($Game{'steps_quad'} // $Game{'zbytek'});
        }
        $Value = \&value_score;
    } ## end else [ if ($Feat_mode) ]

    # The flat route bonus applies only to value_score; the pure modes leave
    # $MaxP unset and get 0. (value_route builds its own route/cp score.)
    $RouteBonus = defined $MaxP ? int sqrt($MaxP) : 0;
    $Route      = $Game{'route'} // {};

    # Per-(box,goal) routes for the route-delivery macro. New-Parser blobs
    # store them COMPACT ([moves_packed, must_empty_packed], both 'n*' cell
    # strings); older blobs carry the rich {moves,must_empty} records. Unpack
    # ONCE here, split into TWO flat runtime maps (one fewer hash hop in
    # tahy()'s gate loop); the search hot path never touches pack/unpack.
    $RouteMoves = {};
    $RouteMust  = {};
    {
        my $rt = $Game{'routes'} // {};
        foreach my $bx (keys %$rt) {
            my $row = $rt->{$bx};
            foreach my $g (keys %$row) {
                my $r = $row->{$g};
                if (ref $r eq 'ARRAY') {    # packed (new Parser)
                    $RouteMoves->{$bx}{$g} = [unpack 'n*', $r->[0]];
                    $RouteMust->{$bx}{$g}  = { map(($_, 1), unpack 'n*', $r->[1]) };
                }
                else {                      # rich record (older blobs)
                    $RouteMoves->{$bx}{$g} = $r->{'moves'};
                    $RouteMust->{$bx}{$g}  = $r->{'must_empty'};
                }
            }
        }
    }
    $Has_routes = %$RouteMoves ? 1 : 0;

    # Blobs written before the has_common_path -> has_cp rename still carry
    # the old key -- accept both so no re-parse is needed.
    $Has_cp = $Game{'has_cp'} // $Game{'has_common_path'} // 0;
    %CPath  = ();
    if ($Has_cp) {

        # The FULL conveyor edge map incl. edge 0; value_route and value_flow
        # read %CPath as route-edge membership.
        my $cp_arr = $Game{'c_path'};
        for my $j (0 .. $#$cp_arr) {
            my ($bx, $t) = @{ $cp_arr->[$j] };
            $CPath{$bx}{$t} = 1;
        }
    }

    # The full conveyor structures from the blob (c_path endpoint OFF the
    # goals, to_goal all-or-nothing): %CPathIdx {src}{tgt}=>index / @CPathArr
    # ordered edges / %ToGoal endpoint deliveries -- consumed by _cp_deliver.
    %CPathIdx = ();
    @CPathArr = ();
    %ToGoal   = ();
    if ($Has_cp) {
        my $cp_arr = $Game{'c_path'};
        @CPathArr = @$cp_arr;
        for my $j (0 .. $#$cp_arr) {
            my ($bx, $t) = @{ $cp_arr->[$j] };
            $CPathIdx{$bx}{$t} = $j;
        }
        %ToGoal = %{ $Game{'to_goal'} // {} };
    }

    # FEATURE: the island counter's own paint + floor list
    if ($Feat_mode) {
        @FloorCells = grep {defined $Cg[$_]} 0 .. $#Cg;
        @Vis_ci     = (0) x scalar @Maze;
        $PaintId_ci = 0;
    }

    # Matching-deadlock precompute. Per-cell reachable-goal sets from the
    # single-box push-distance table ('Inf'/undef = unreachable), plus the
    # self-edge (a box on goal g reaches g). $Selective marks cells reaching a
    # proper subset of goals; $Match_active gates the whole filter off for a
    # game with no non-goal selective cell, where a matching deadlock provably
    # can never form.
    %ReachG    = ();
    %Selective = ();
    {
        my $zr = $Game{'steps'} // $Game{'zbytek_raw'} // {};    # new // old
        for my $c (keys %$zr) {
            my $row = $zr->{$c};
            for my $g (keys %$row) {
                my $v = $row->{$g};
                $ReachG{$c}{$g} = 1 if defined $v && $v ne 'Inf';
            }
        }
        $ReachG{$_}{$_} = 1 foreach @Goal;                       # self-edge: a box on its goal reaches it
        my $ng         = scalar @Goal;
        my $has_ng_sel = 0;
        for my $c (keys %ReachG) {
            next unless keys %{ $ReachG{$c} } < $ng;
            $Selective{$c} = 1;
            $has_ng_sel = 1 unless $Target[$c];                  # a NON-GOAL selective cell = a real fire driver
        }
        $Match_active = $has_ng_sel;
    }

    # Wallified-matching precompute: the reverse push graph, so reachability
    # can be recomputed BACKWARD from the goals on a board where frozen boxes
    # have become walls. Built once per game -- only which edges survive
    # depends on the wall set.
    %Rev       = ();
    %ReachW    = ();
    $Walled_on = @Goal ? 1 : 0;
    for my $c (keys %Cmk) {
        push @{ $Rev{$_} }, $c foreach @{ $Cmk{$c} };
    }
} ## end sub initvars_score
##############################################################################
# ===== Forward =============================
##############################################################################
# FORWARD: the priority-queue best-first search the scoring portfolio runs on
# (PUSH_SCORE / MOVE_SCORE / PUSH_ASSIGN / MOVE_SUM / ROUTE / FLOW), plus the
# FEATURE wheel. The hottest loop in the project -- it pops a position, asks
# tahy() for its children and threads them into %Parent.
sub solve_forward($limit, $mode) {
    my $gameid = $Gameid;
    my ($pozice, $nopen, $MaxOpen, $counter, $timer, $cas, $tick, $elapsed, $doba, $reason, $path, $plen, $steps, $bc, $ending);
    $Parent{$Start} = '';    # %Parent membership IS the seen-set
    if ($Feat_mode) {
        my $key = feat_key($Start);
        %FCellQ   = ($key => 'Games::Sokoban::Solver::Heap'->new);
        @FCellKey = ($key);
        $FCellPtr = 0;
        $FCellQ{$key}->add($Start, 0);
    }
    else {$Pex->add($Start, 0)}
    $nopen   = 1;
    $MaxOpen = 1;
    $bc      = 0;
    $counter = 0;                   # may stay 0 if a trivial game solves on the first pop
    $reason  = 'UNSOLVABLE';
    $cas     = time();
    $tick    = $cas;                # the one-second gate for the race flag; $cas is the screen's
    $timer   = [&gettimeofday()];
LMAIN: while ($nopen) {
        my $pweight = 0;
        if ($Feat_mode) {

            # Feature-space draw: go ROUND the cells, one position from each,
            # so a coordinate discovered a moment ago is served on the next
            # turn of the wheel. $pweight is the popped position's accumulated
            # weight, read off the heap top before the pop -- its children add
            # to it.
            my $n = @FCellKey;
            my $i = 0;
            ++$i while $i < $n && !$FCellQ{ $FCellKey[($FCellPtr + $i) % $n] }->size;
            confess "\nFEATURE: $nopen positions open but every cell is empty" if $i == $n;
            my $j = ($FCellPtr + $i) % $n;
            $FCellPtr = ($j + 1) % $n;
            my $Q    = $FCellQ{ $FCellKey[$j] };
            my $node = $Q->[0];
            $pweight = $node->[0] if ref $node;
            $pozice  = $Q->next;
        } ## end if ($Feat_mode)
        else {
            $pozice = $Pex->next;
        }
        --$nopen;
        if (exists $MemBad{$pozice}) {
            next;
        }
        confess "\nNO PARENT FOR POSITION!" unless exists $Parent{$pozice};
        my (@tahy) = tahy($pozice);

        # FEATURE: the parent's four counts, once per expansion -- the advisor
        # comparison base for this litter.
        my ($fb_odo, $fb_isl, $fb_room, $fb_out);
        ($fb_odo, $fb_isl, $fb_room, $fb_out) = feat_counts($pozice)
            if $Feat_mode;

        # $chain_parent threads a macro chain. Three score forms:
        #   undef   -> chain intermediate: linked into %Parent (so get_path()
        #              can walk the single pushes) and marked seen but NOT
        #              queued; becomes the parent of the next chain step.
        #   number  -> ordinary queued child, parent $pozice; resets the thread.
        #   [number]-> "chain start": queued AND becomes the parent of the
        #              following chain steps, so the entry node is
        #              independently expandable while the shortcut's fill
        #              positions still descend from it.
        #
        # A LINK IN %Parent IS ONE PUSH, AND THAT IS CHECKED, NOT ASSUMED
        # (USER 2026-10-07, after game 5469). The path is rebuilt from these
        # links alone, so a child hung on a position it is not one push from
        # is a solution that does not replay. Three things hold it:
        #   * a thread ends at a plain score and nowhere else, and every macro
        #     closes its own (see the conveyor ride in _tahy_macros);
        #   * a chain that LOSES a step -- the step is a known deadlock -- has
        #     nothing to hang its next step on: the NEW steps after the lost one
        #     are dropped (not linked, not marked seen, free to be born later
        #     in the ordinary way) until the chain ends or passes through a
        #     position that is already known, from which it goes on -- the step
        #     after a known position is one push from it whatever came before
        #     (that is also how a conveyor ride re-roots at its endpoint);
        #   * a step hung on another step (not on the position, whose children
        #     tahy() made one push at a time) is compared with it box by box:
        #     exactly one box moved, onto a cell it can be pushed to from there,
        #     or the solve dies here and names it.
        # And whatever these three let through, the finished path is replayed
        # before it is returned (replay_check).
        my $chain_parent = $pozice;
        my $broken       = 0;         # the step before this one in its chain was lost
        my @fkids;                    # feature mode: this expansion's queueable children, decided after the loop
        foreach my ($child, $score)(@tahy) {
            ++$bc;
            my $start = ref $score;                                          # [num] chain-start marker
            my $real  = $start                     ? $score->[0] : $score;
            my $ends  = (defined $real && !$start) ? 1           : 0;        # a plain score closes the thread
            if (exists $MemBad{$child}) {
                $broken       = $ends ? 0 : 1;
                $chain_parent = $pozice;
                next;
            }
            if (exists $Parent{$child}) {
                $broken       = 0;
                $chain_parent = $ends ? $pozice : $child;
                next;
            }
            if ($broken) {
                $broken = 0 if $ends;
                next;
            }
            if ($chain_parent ne $pozice) {
                my (undef, @was) = unpack $pu, $chain_parent;
                my (undef, @is)  = unpack $pu, $child;
                my %was  = map(($_, 1), @was);
                my %is   = map(($_, 1), @is);
                my @gone = grep((!$is{$_}),  @was);
                my @new  = grep((!$was{$_}), @is);
                confess("a macro step is not one push from the step before it: boxes (@was) -> (@is)")
                    unless @gone == 1 && @new == 1 && defined $Cm{ $gone[0] }{ $new[0] };
            }
            $Parent{$child} = $chain_parent;

            # terminal: the player-independent layout test (all goals filled --
            # one substr/eq on the key's boxes tail when the solved layout is
            # unique), or a P1 park CLASS (%SolsC)
            if ((defined $SolvedLay ? substr($child, $ManOff) eq $SolvedLay : _lay_solved($child))
                || exists $SolsC{$child})
            {
                $Bestbet = $child;
                last LMAIN;
            }
            if (defined $real) {
                if ($Feat_mode) {

                    # Only COLLECT here. Which children come out free cannot
                    # be decided one at a time: each poradce names the best of
                    # its candidates, and "best" is only known once the whole
                    # litter is in. The enqueue happens after the loop.
                    # [7] = the child's value_score (3.4): the sixth poradce
                    # and the in-cell tie-break both read it there.
                    push @fkids, [$child, feat_counts($child), ($ExplMark{$child} ? 1 : 0), 0, $real];
                    $chain_parent = $start ? $child : $pozice;
                    next;
                }
                $Pex->add($child, $real);
                ++$nopen;
                $MaxOpen      = $nopen if $nopen > $MaxOpen;
                $chain_parent = $start ? $child : $pozice;
            } ## end if (defined $real)
            else {
                $chain_parent = $child;
            }
        } ## end foreach my ($child, $score)...

        # Feature mode's enqueue: let the poradci name their picks over the
        # whole litter, then file every child by its coordinate. An advised
        # step is free, everything else costs one move. Since 3.4 the weight
        # carries a bounded monotone fraction of the child's score below the
        # integer part, so the ties of equal weights inside a cell fall to
        # the better-scored child instead of to queue arrival order;
        # int($pweight) strips the parent's own fraction, so fractions never
        # accumulate across generations.
        if (@fkids) {
            feat_advise(\@fkids, $fb_odo, $fb_isl, $fb_room, $fb_out);
            for my $k (@fkids) {
                my $key = join ',', @$k[1 .. 4];
                my $cq  = $FCellQ{$key};
                unless ($cq) {    # a coordinate nobody has reached before: its own queue, its own turn of the wheel
                    $cq = $FCellQ{$key} = 'Games::Sokoban::Solver::Heap'->new;
                    push @FCellKey, $key;
                }
                my $sc = $k->[7];
                $cq->add($k->[0], int($pweight) + ($k->[6] ? 0 : 1) + 0.5 + $sc / (2 * (abs($sc) + ($MaxVal || 1000))));
                ++$nopen;
                $MaxOpen = $nopen if $nopen > $MaxOpen;
            }
        } ## end if (@fkids)
    } ## end LMAIN: while ($nopen)
    continue {
        unless (++$counter % 100) {
            $doba = tv_interval($timer);
            if ($limit and $doba > $limit) {$reason = 'TIMEOUT'; last LMAIN}    # the budget, promptly
            $elapsed = time();
            if ($elapsed != $tick) {                                            # once a second
                $tick = $elapsed;
                if (race_lost()) {$reason = 'IGNORE'; last LMAIN}               # another mode won this game
                if ($elapsed - $cas >= $SCREEN) {
                    $cas = $elapsed;
                    $QUIET
                        or backline(
                            sprintf '%-11s %8d ... %12d %9d  %s  %12.2f %12.0f %12.0f',
                            $mode, $gameid, $counter, $nopen, podil($nopen, $MaxOpen),
                            $doba,
                            $bc / $doba,
                            $counter / $doba
                        );
                    if (mem_over()) {$reason = 'MEMCAP'; last LMAIN}    # RAM ceiling ($MAX_GB) hit
                }
            } ## end if ($elapsed != $tick)
        } ## end unless (++$counter % 100)
    } ## end continue
    $path  = undef;
    $doba  = clamp_doba(tv_interval($timer));
    $plen  = undef;
    $steps = 0;
    if ($Bestbet) {
        $path = get_path($Bestbet);
        if (my $sc = $SolsC{$Bestbet}) {    # P1 park class: walk to the stored tail's start cell, then the tail
            my ($M, $T) = @$sc;
            my (undef, @bb) = unpack($pu, $Bestbet);
            my %bb   = map(($_, 1), @bb);
            my $par  = $Parent{$Bestbet};
            my $cell = (defined $par && length $par)
                ? (grep {!exists $bb{$_}} (unpack($pu, $par))[1 .. $Nbox])[0]    # the pushed box's old cell == the player
                : $Game{'player'};
            $path .= ($cell == $M ? '' : cesta($cell, $M, \@bb)) . $T;
        }
        $path = rebuilt_path($path);
        replay_check($path);
        $plen   = length($path);
        $steps  = $path =~ tr/UDRL//;
        $reason = 'SOLVED';
    } ## end if ($Bestbet)
    my $qsize = 0;
    if ($Feat_mode) {$qsize += $_->size for values %FCellQ}
    else            {$qsize = $Pex->size}
    $ending = sprintf $ENDING,
        $mode, $gameid, $Game{'nbox'}, $Game{'ncell'}, $reason, $plen // $limit, $steps, $doba,
        sprintf('%.0f', $bc / $doba), sprintf('%.0f', $counter / $doba),
        $MaxOpen,
        $qsize, scalar %Parent;
    barva($reason, $ending);
    bad_close(($reason eq 'SOLVED') ? 1 : 0);
    my $nseen = scalar %Parent;    # TAKEN FIRST: free_memory() empties %Parent
    free_memory();
    return ($reason, $path, $doba, $nseen);
} ## end sub solve_forward
##############################################################################
# ===== Order =================================
##############################################################################
# ORDER: macro-level DFS -- ordered single-box goal-commit macros plus
# unlocking nudges. Motivation: a wide-open box field feeding a separated
# goal chamber. A human solves it one box at a time; the global best-first
# search drowns in the PRODUCT of the per-box move spaces. This mode searches
# the SUM instead: the preferred operator is "commit one box to a free goal
# via a single-box route" (the whole route = one macro, other boxes standing;
# goals tried most-urgent-first by the blob 'order' rank). When no commit
# works, single-push NUDGES relocate a box to unlock a route, and the DFS
# backtracks over both operator kinds; %OSeen keeps the whole search from
# revisiting a position. A box parked on a goal by a commit is never moved
# again. Every push is linked into %Parent, so the final move string comes
# from the ordinary get_path() reconstruction.
my (%OSeen, $OTimer, $ODeadline, $OTimeUp, $ONseen, $ONmacro, $Otick);
my ($ORaceUp, $OMemUp, $ORaceNext, $OMemNext);    # ORDER abort flags: race (another mode won) / memory cap
my $ORDER_NUDGE_CAP = 8;                          # max consecutive nudges without a goal commit

# Liveness probe: is every free goal reachable in the push graph from some
# unlocked box, with ONLY the commit-locked boxes as obstacles (both as push
# targets and as push stances)? Unlocked boxes are transparent -- a nudge can
# always move them -- so a 0 here is permanent: locked boxes never move and
# the subtree can only lose more freedom. One multi-source BFS per node.
sub order_alive($open, $boxes, $locked) {
    my %parked = %$locked;
    my (%vis, @q);
    for my $b (grep {!exists $parked{$_}} @$boxes) {
        push @q, $b unless $vis{$b}++;
    }
    while (defined(my $c = shift @q)) {
        foreach my $t (@{ $Cmk{$c}; }) {
            next if exists $vis{$t} || exists $parked{$t};
            next if exists $parked{ $Cm{$c}{$t} };           # stance blocked for good
            $vis{$t} = 1;
            push @q, $t;
        }
    }
    exists $vis{$_} or return 0 foreach @$open;
    return 1;
} ## end sub order_alive

# Single-box push BFS: box $bx -> $goal with all other boxes standing (they
# act as walls). State = (box cell, player region), the region identified by
# its smallest player-reachable cell after paint(). Returns [[from,to],...]
# push list or undef; the optional $block hashref collects the standing boxes
# the BFS bumped into -- they are the nudge candidates when this BFS fails.
sub order_push_path($man, $bx, $goal, $boxes, $nseen_ref, $block = undef) {
    my @others = grep {$_ != $bx} @$boxes;
    my %obag   = map(($_, 1), @others);
    my (%seenst, %prevst, @queue);
    paint($man, $bx, @others);
    my $rm;
    for my $c (0 .. $#Vis) {if ($Vis[$c] == $PaintId) {$rm = $c; last}}
    confess 'EMPTY PLAYER REGION' unless defined $rm;
    my $key0 = $bx . ',' . $rm;
    $seenst{$key0} = 1;
    push @queue, [$bx, $man, $key0];

    while (my $st = shift @queue) {
        my ($b, $p, $key) = @$st;

        # live progress in the style of the other modes: BFS states seen,
        # DFS positions visited, macros committed, elapsed, states/s
        unless (++$$nseen_ref % 500) {
            if (time() - $Otick > 6) {
                $Otick = time();
                my $doba = tv_interval($OTimer);
                $QUIET
                    or backline(
                        sprintf '%-11s %8d ... %12d %9d %6d %12.2f %12.0f',
                        'ORDER',  $Gameid, $ONseen, scalar %OSeen,
                        $ONmacro, $doba,   $ONseen / $doba
                    );
            }
        }

        # collect pushable targets BEFORE the child paints clobber @Vis;
        # standing boxes that block a push target or a push stance go into
        # $block
        paint($p, $b, @others);
        my @pushable;
        for my $t (@{ $Cmk{$b}; }) {
            if (exists $obag{$t}) {$block->{$t} = 1 if $block; next}
            my $s = $Cm{$b}{$t};
            if ($Vis[$s] != $PaintId) {
                $block->{$s} = 1 if $block && exists $obag{$s};
                next;
            }
            push @pushable, $t;
        }
        for my $t (@pushable) {

            # NO is_bad on intermediates: a macro is atomic, the box never
            # STAYS on a transit cell, so a static "deadlock if it stays"
            # verdict is meaningless here -- and a false positive would also
            # hide the boxes behind that cell from %block. Only nudge
            # landings, where the box does stay, are is_bad-checked (in odfs).
            paint($b, $t, @others);    # player ends on the box's old cell
            my $rm2;
            for my $c (0 .. $#Vis) {if ($Vis[$c] == $PaintId) {$rm2 = $c; last}}
            confess 'EMPTY PLAYER REGION' unless defined $rm2;
            my $k = $t . ',' . $rm2;
            next if $seenst{$k}++;
            $prevst{$k} = [$key, $b, $t];

            if ($t == $goal) {
                my @macro;
                for (my $kk = $k; $kk ne $key0; $kk = $prevst{$kk}[0]) {
                    unshift @macro, [$prevst{$kk}[1], $prevst{$kk}[2]];
                }
                return \@macro;
            }
            push @queue, [$t, $b, $k];
        } ## end for my $t (@pushable)
    } ## end while (my $st = shift @queue)
    return undef;
} ## end sub order_push_path

# One DFS node. $nnudge counts CONSECUTIVE nudges since the last goal commit:
# nudges exist to unlock a route, so when $ORDER_NUDGE_CAP of them in a row
# produced no commit, the branch is aimless shuffling -- cut it. Returns the
# solved final position (propagated up) or undef.
sub odfs($pos, $man, $boxes, $depth, $nnudge, $locked) {
    my %bags = map(($_, 1), @$boxes);
    my @open = grep {!exists $bags{$_}} @Goal;
    return $pos unless @open;
    my $ot = tv_interval($OTimer);
    if ($ODeadline and $ot > $ODeadline) {$OTimeUp = 1; return undef}

    # The deadline above is tested on every call -- odfs is hot, but tv_interval
    # is already computed. These two are not: the race flag once a second, the
    # memory probe on the screen interval even though this search has no screen
    # (it is the expensive one, and a brake against a bug does not need to be
    # tested often). See the periods note at the top of the file.
    if ($ot > $ORaceNext) {
        $ORaceNext = $ot + 1;
        if (race_lost()) {$ORaceUp = 1; $OTimeUp = 1; return undef}    # another mode won this game
    }
    if ($ot > $OMemNext) {
        $OMemNext = $ot + $SCREEN;
        if (mem_over()) {$OMemUp = 1; $OTimeUp = 1; return undef}      # RAM ceiling ($MAX_GB) hit
    }
    return undef if $depth > 5000;

    # liveness gate: LOCKED boxes (parked by a commit of ours) never move
    # again, so if some free goal is push-unreachable even with every other
    # box treated as transparent, this subtree is dead forever -- prune it at
    # the door. (Unlocked boxes must stay transparent here: their blockage is
    # curable by nudges -- and a box that merely STARTS on a goal is NOT
    # locked, it may stand on the wrong goal and have to move.)
    return undef unless order_alive(\@open, $boxes, $locked);
    my $zr      = $Game{'steps'} // $Game{'zbytek_raw'};    # new // old
    my @movable = grep {!exists $locked->{$_}} @$boxes;

    # goal preference: blob 'order' rank first, deeper (farther) goals first
    # inside a tier -- only a preference; backtracking recovers a wrong order
    my %depthg;
    for my $g (@open) {
        my $d = 0;
        for my $bx (@movable) {
            my $v = $zr->{$bx}{$g};
            $d = $v if defined $v && ($d == 0 || $v < $d);
        }
        $depthg{$g} = $d;
    }
    my @goals = sort {($Priority[$b] // 0) <=> ($Priority[$a] // 0) || $depthg{$b} <=> $depthg{$a}} @open;

    # ---- goal-commit macros, TOP open 'order' tier only. The blob ranking
    # encodes the packing order: committing an easier lower-rank goal first is
    # exactly how a chamber gets sealed. %block then holds the boxes that
    # stand in the way of the goal that SHOULD be filled now, so the nudge
    # tiers below work on the right obstacles. Lower-tier commits run only
    # after the nudges, as a last resort (the ranking can be wrong-oriented).
    my %block;
    my $toprank = $Priority[$goals[0]] // 0;
    my @lower   = grep {($Priority[$_] // 0) != $toprank} @goals;
    for my $g (grep {($Priority[$_] // 0) == $toprank} @goals) {
        my @cand = sort {$zr->{$a}{$g} <=> $zr->{$b}{$g}} grep {defined $zr->{$_}{$g}} @movable;
        for my $bx (@cand) {
            my $macro = order_push_path($man, $bx, $g, $boxes, \$ONseen, \%block) or next;
            my $r     = order_commit($pos, $boxes, $macro, $depth, 0, $locked, $g);
            return $r    if defined $r;
            return undef if $OTimeUp;
        }
    }
    goto LOWER if $nnudge >= $ORDER_NUDGE_CAP;    # aimless-shuffle cutoff

    # ---- nudges: single pushes of unparked boxes, score-ordered in three
    # tiers. Boxes the route BFS actually bumped into (%block) go FIRST --
    # moving them is what can unlock a route. Their is_bad-flagged retreats
    # go SECOND: a nudge is transient, so a "deadlock" verdict that assumes
    # the box stays put can be a false positive. Unrelated clean pushes last.
    paint($man, @$boxes);
    my (@bcand, @rcand, @ocand);
    for my $bx (@movable) {
        foreach my $t (@{ $Cmk{$bx}; }) {
            next if exists $bags{$t};
            my $s = $Cm{$bx}{$t};
            next unless $Vis[$s] == $PaintId;
            my %t_bag = map(($_, 1), $t, grep {$_ != $bx} @$boxes);
            my $cand  = [$Value->($bx, $t, \%t_bag), $bx, $t];
            my $bad   = is_bad($bx, $t, \%t_bag);
            if ($bad) {
                push @rcand, $cand if exists $block{$bx};
                next;
            }
            exists $block{$bx} ? push @bcand, $cand : push @ocand, $cand;
        }
    } ## end for my $bx (@movable)

    # ---- unlock probe: a blocker nudge that makes a TOP-tier goal routable
    # right now is almost certainly the move the position is waiting for.
    # Simulate each blocker push and re-run the route BFS; openers jump the
    # queue.
    my @top = grep {($Priority[$_] // 0) == $toprank} @goals;
    my (@ucand, @rest);
    for my $c (sort({$a->[0] <=> $b->[0]} @bcand), sort({$a->[0] <=> $b->[0]} @rcand)) {
        my (undef, $bx, $t) = @$c;
        my @sim   = ($t, grep {$_ != $bx} @$boxes);
        my $opens = 0;
    UPROBE: for my $g (@top) {
            for my $b2 (grep {defined $zr->{$_}{$g} && !exists $locked->{$_}} @sim) {
                if (order_push_path($bx, $b2, $g, \@sim, \$ONseen)) {$opens = 1; last UPROBE}
            }
        }
        $opens ? push @ucand, $c : push @rest, $c;
    }
    for my $c (@ucand, @rest, sort({$a->[0] <=> $b->[0]} @ocand)) {
        my (undef, $bx, $t) = @$c;
        my $r = order_commit($pos, $boxes, [[$bx, $t]], $depth, $nnudge + 1, $locked, undef);
        return $r    if defined $r;
        return undef if $OTimeUp;
    }

    # ---- last resort: commits to the lower 'order' tiers ----
LOWER: for my $g (@lower) {
        for my $bx (
            sort {$zr->{$a}{$g} <=> $zr->{$b}{$g}}
            grep {defined $zr->{$_}{$g}} @movable
            )
        {
            my $macro = order_push_path($man, $bx, $g, $boxes, \$ONseen) or next;
            my $r     = order_commit($pos, $boxes, $macro, $depth, 0, $locked, $g);
            return $r    if defined $r;
            return undef if $OTimeUp;
        }
    }
    return undef;
} ## end sub odfs

# Try one child (goal macro or nudge): skip if the resulting position was
# already visited anywhere in the search, else link every push into %Parent
# and recurse. A goal commit passes its target as $lockcell: the child branch
# sees that box as locked forever (copy-on-lock, so backtracking unlocks).
sub order_commit($pos, $boxes, $macro, $depth, $nnudge, $locked, $lockcell) {
    my $moved = $macro->[0][0];             # box's original cell
    my ($from, $to) = @{ $macro->[-1] };    # last push: player ends on $from
    my @nb = grep {$_ != $moved} @$boxes;
    my $i  = 0;
    ++$i while $i < @nb && $nb[$i] < $to;
    splice(@nb, $i, 0, $to);
    my $cpos = pack($pu, $from, @nb);
    return undef if $OSeen{$cpos}++;
    ++$ONmacro   if @$macro > 1;
    my @cur = @$boxes;

    for my $step (@$macro) {
        my ($f, $t) = @$step;
        my @nx = grep {$_ != $f} @cur;
        my $j  = 0;
        ++$j while $j < @nx && $nx[$j] < $t;
        splice(@nx, $j, 0, $t);
        my $child = pack($pu, $f, @nx);

        # WRITE-ONCE: keep the FIRST parent threaded for a position. %OSeen
        # dedups only a macro's FINAL cell, so a multi-step commit can
        # re-enter an earlier nudge's intermediate cell; overwriting %Parent
        # there would point a node at one of its own descendants -> a cycle
        # steps()/get_path() then loops on. First discovery is always the
        # shallower node, so the map stays an acyclic tree and every edge is
        # still a real one-push transition.
        $Parent{$child} = $pos unless exists $Parent{$child};
        $pos            = $child;
        @cur            = @nx;
    } ## end for my $step (@$macro)
    $locked = { %$locked, $lockcell, 1 } if defined $lockcell;
    return odfs($pos, $from, \@nb, $depth + 1, $nnudge, $locked);
} ## end sub order_commit

sub solve_order($limit) {
    my $timer = [&gettimeofday()];
    ($OTimer, $ODeadline, $OTimeUp)            = ($timer, $limit, 0);
    ($ORaceUp, $OMemUp, $ORaceNext, $OMemNext) = (0, 0, 1, $SCREEN);
    ($ONseen, $ONmacro, $Otick)                = (0, 0, time());
    %OSeen = ($Start, 1);
    $Parent{$Start} = '';
    my ($man, @boxes) = unpack($pu, $Start);

    # locked = boxes ORDER itself parked (starts EMPTY: a box that BEGINS on a
    # goal may stand on the wrong one and must stay movable). GIVEUP, not
    # UNSOLVABLE, when the restricted DFS exhausts its tree: this mode is
    # deliberately incomplete, UNSOLVABLE stays reserved for a true
    # state-space-exhaustion proof.
    my $final  = odfs($Start, $man, \@boxes, 0, 0, {});
    my $reason = defined $final ? 'SOLVED' : $ORaceUp ? 'IGNORE' : $OMemUp ? 'MEMCAP' : $OTimeUp ? 'TIMEOUT' : 'GIVEUP';
    my $doba   = clamp_doba(tv_interval($timer));
    my ($path, $sollen, $steps) = ('', 0, 0);
    if ($reason eq 'SOLVED') {
        $path = get_path($final);
        my $tail = $Sols{$final};    # box-on-P terminal -> P->ga finishing moves ('' / legacy 1 otherwise)
        $path .= $tail if defined $tail && $tail =~ /[A-Za-z]/;
        $path = rebuilt_path($path);
        replay_check($path);
        $sollen = length($path);
        $steps  = $path =~ tr/DLRU//;
    }

    # macro-DFS: no queue and no box-move rate to report, so slots 1-3 stay blank
    # and the macro count takes slot 4.
    my $ending = sprintf $ENDING,
        'ORDER', $Gameid, $Game{'nbox'}, $Game{'ncell'}, $reason, $sollen || $limit,
        $steps, $doba, q{}, q{}, q{}, $ONmacro, $ONseen;
    barva($reason, $ending);
    %OSeen = ();
    bad_close($reason eq 'SOLVED' ? 1 : 0);
    free_memory();    # $ONseen is a counter, not a container -- safe here
    return ($reason, $path, $doba, $ONseen);
} ## end sub solve_order
##############################################################################
# ===== Backward ===========================
##############################################################################
# BACKWARD: a first-solution search that runs ENTIRELY BACKWARD: from the
# solved config (boxes on goals) it PULLS boxes outward, best-first guided
# toward Start, until it reaches the Start box config in a player-compatible
# region -- then the reversed pull path IS the whole solution (no forward
# search). No deadlock checks needed (every pulled config is winnable).
# Driven only by the time $limit; NOT bounded by depth/nodes, so on a hard
# game memory grows with time. %Pull/%PullMan = transpose of %Cm: a push b->c
# (stance cm{b}{c}) reverses to a pull of a box at c back to b, player ending
# at cm{b}{c}. Built once per game.
my (%Pull, %PullMan, $StartBoxKey, %Bseen);
my (@IsStart, @PullTo, $Far);    # the score's tables, see build_pull_to()

sub build_pull() {
    %Pull    = ();
    %PullMan = ();
    for my $b (keys %Cm) {
        my $tb = $Cm{$b};
        for my $c (keys %$tb) {
            push @{ $Pull{$c} }, $b;
            $PullMan{$c}{$b} = $tb->{$c};
        }
    }
}

# THE SCORE OF A PULLED POSITION (3.6, 2026-10-04): every box that is off a
# start cell against every FREE start cell, the pulls between the two added up
# -- smaller is nearer the start, 0 exactly at it. $PullTo[$s][$x] is how many
# pulls bring a box from cell x to the start cell s, that is, how many pushes
# take one from s to x: one walk over the push graph per start cell, the player
# not asked about. $Far stands in for "cannot": the largest number in the table
# and one more.
#
# Until 3.5 the score was the sum, over the boxes, of the steps ON FOOT from a
# box to the nearest start cell -- a measure that knows neither how a box moves
# nor that two boxes cannot share a start cell. The new one came out of the
# module FirstBack, where pulling alone with it solved FOUR games nothing had
# ever solved (34509, 1101, 14757, 42738). Measured against the old score at
# 300 s: 17 solved against 15 on 40 games, none lost (fb-1/fb-4), and 11
# against 9 on another 40 (bs-1: 42738, 20443, 11135 gained, 8592 lost); where
# both solve, the new one is sooner on most games, often by an order of
# magnitude. IT IS A DIFFERENT SEARCH, NOT A BETTER VERSION OF THE SAME ONE: on
# sixty games the old score held, the new one lost eight and gained one
# (fb-7), six of the eight being games the old score had solved inside a
# minute. That is what a change of score is (USER): no way of solving is right
# for every game -- another score is another order of search, and in a space
# of this size every order reaches some games inside the budget and not
# others. Those games keep their stored solutions; the reason for the change
# is the games nothing has solved, where the old score has had its turn. It
# costs (boxes x free start cells) table reads where the old one cost one read
# a box: about two thirds of the positions per second.
sub build_pull_to() {
    @IsStart     = (0) x scalar @Maze;
    $IsStart[$_] = 1 foreach @Baggage;
    @PullTo      = ();
    $Far         = 0;
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
} ## end sub build_pull_to

# One representative player cell per connected free region of the solved
# config (floor minus goal-boxes) -- the player could be in any of them when
# solved.
sub solved_regions() {
    my (%reps, %seen);
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
    return keys %reps;
} ## end sub solved_regions

# ONE STORE FOR THE PULL SEARCH (3.5, 2026-09-05, the USER's wave). Until 3.4
# every generated configuration was written three times: %Bseen{key} = index,
# a @BackNode record [man, parent index, from, to] and a heap entry [h, key] --
# 182 + 292 + ~170 B measured on 1 M entries, ~800 B per node with the
# allocator -- and BACKWARD generates 35 000 nodes a second on a small dense
# board (game 1088: 28 MB/s in ONE worker, 17 GB at 600 s, MEMCAP with three of
# them racing as phase-1 leaders). %Bseen is now the single source: a node's
# VALUE is pack('nn', from, to) -- the push that undoes its pull -- followed by
# its parent's key; a seed's value is the empty string; the man is the first
# cell of the key and is not stored again. The open list is a set of buckets by
# h (an integer, the score build_pull_to() describes), %Q{h} = [keys], with a
# small heap of the live h values naming the cheapest bucket (the Solver 2.0
# shape): a queued key costs one string instead of a two-element array.
# Measured on 1088: 303 B per node against 770, +4 % nodes per second; A/B on
# 14 games at 90 s 7 solved against 6 (+2/-1 -- the order inside a bucket is
# FIFO where the heap's was arbitrary, and BACKWARD is sensitive to it).
#
# Reconstruct the pull-tail (push list, Start-config -> Solved) by walking the
# parent chain stored in %Bseen from the found node back to a seed.
sub build_tail($key) {
    my @tail;
    while (length(my $v = $Bseen{$key})) {
        push @tail, [unpack('nn', $v)];
        $key = substr($v, 4);
    }
    return \@tail;
}

# Replay the pull-tail as pushes from $pos, regenerating the player's walk
# from %Cg (cesta) at every seam -- never splicing a stored walk.
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

sub initvars_backward() {
    $StartBoxKey = pack($pu, sort {$a <=> $b} @Baggage);
    build_pull();
    build_pull_to();
}

# The BACKWARD search: guided pull-BFS from solved toward Start, time-bounded
# by $limit. Returns SOLVED (reached Start), TIMEOUT (out of time), or
# UNSOLVABLE (pull-space exhausted without reaching Start).
sub solve_backward($limit) {
    my $timer = [&gettimeofday()];
    my $cas   = time();
    my $tick  = $cas;                                # the one-second gate for the race flag; $cas is the screen's
    %Bseen = ();
    my @goals = sort {$a <=> $b} @Goal;
    my %Q;                                           # the open list: h -> [keys], FIFO inside a bucket
    my $Hq = 'Games::Sokoban::Solver::Heap'->new;    # the live bucket indices, cheapest on top
    my $found;                                       # the key of the node that reached Start
    my $reason = 'UNSOLVABLE';

    # progress counters: $bc = child candidates, $nopen/$MaxOpen = queue load,
    # $hbest = closest approach of the beam to Start (0 = box config reached)
    my ($bc, $nopen, $MaxOpen, $hbest) = (0, 0, 0, ~0);
    for my $m (solved_regions()) {
        my $pos = pack($pu, $m, @goals);
        next if exists $Bseen{$pos};
        $Bseen{$pos} = '';
        if (pack($pu, @goals) eq $StartBoxKey) {
            paint_fr($m, @goals);
            if ($Vis_fr[$Game{'player'}] == $PaintId_fr) {$found = $pos; last}
        }
        my $h = 0;
        if (my @off = grep {!$IsStart[$_]} @goals) {
            for my $s (grep {!$Target[$_]} @Baggage) {    # the start cells no box stands on
                my $row = $PullTo[$s];
                $h += $row->[$_] // $Far for @off;
            }
        }
        $hbest = $h if $h < $hbest;
        push @{
            $Q{$h} //= do {$Hq->add($h, $h); []}
            },
            $pos;
        ++$nopen;
    } ## end for my $m (solved_regions...)
    $MaxOpen = $nopen;
    my $counter = 0;
    while (!defined $found && $nopen) {
        my $h0     = $Hq->peek;                          # the cheapest non-empty bucket
        my $bucket = $Q{$h0};
        my $pos    = shift @$bucket;
        unless (@$bucket) {delete $Q{$h0}; $Hq->next}    # emptied: retire the bucket
        --$nopen;
        my ($man, @boxes) = unpack($pu, $pos);
        paint($man, @boxes);
        my %bag = map(($_, 1), @boxes);
    GEN: for my $c (@boxes) {
            my $dests = $Pull{$c} or next;
            for my $b (@$dests) {
                ++$bc;
                next if exists $bag{$b};
                next unless $Vis[$b] == $PaintId;
                my $ma = $PullMan{$c}{$b};
                next if exists $bag{$ma};
                my @nb = grep($_ != $c, @boxes);
                my $i  = 0;
                ++$i while $i < @nb && $nb[$i] < $b;
                splice(@nb, $i, 0, $b);
                my $npos = pack($pu, $ma, @nb);
                next if exists $Bseen{$npos};
                $Bseen{$npos} = pack('nn', $b, $c) . $pos;    # the undoing push, then the parent

                if (pack($pu, @nb) eq $StartBoxKey) {
                    paint_fr($ma, @nb);
                    if ($Vis_fr[$Game{'player'}] == $PaintId_fr) {$found = $npos; last GEN}
                }

                # the score, written out here: the child's boxes are the
                # parent's (%bag) with the one on $c now on $b
                my $h = 0;
                if (my @off = grep {!$IsStart[$_]} @nb) {
                    for my $s (@Baggage) {
                        next if $s == $b or $s != $c && exists $bag{$s};
                        my $row = $PullTo[$s];
                        $h += $row->[$_] // $Far for @off;
                    }
                }
                $hbest = $h if $h < $hbest;
                push @{
                    $Q{$h} //= do {$Hq->add($h, $h); []}
                    },
                    $npos;
                ++$nopen;
                $MaxOpen = $nopen if $nopen > $MaxOpen;
            } ## end for my $b (@$dests)
        } ## end GEN: for my $c (@boxes)
        unless (++$counter % 200) {
            my $doba = tv_interval($timer);
            if ($limit and $doba > $limit) {$reason = 'TIMEOUT'; last}    # the budget, promptly
            my $now = time();
            if ($now != $tick) {                                          # once a second
                $tick = $now;
                if (race_lost()) {$reason = 'IGNORE'; last}               # another mode won this game
                if ($now - $cas >= $SCREEN) {
                    $cas = $now;
                    $QUIET
                        or backline(
                            sprintf '%-11s %8d ... %12d %9d  %s  %6d %12.2f %12.0f %12.0f',
                            'BACKWARD', $Gameid, $counter, $nopen, podil($nopen, $MaxOpen),
                            $hbest,     $doba,
                            $bc / $doba,
                            $counter / $doba
                        );
                    if (mem_over()) {$reason = 'MEMCAP'; last}    # RAM ceiling ($MAX_GB) hit
                }
            } ## end if ($now != $tick)
        } ## end unless (++$counter % 200)
    } ## end while (!defined $found &&...)
    my $doba = clamp_doba(tv_interval($timer));
    my ($path, $sollen, $steps) = ('', 0, 0);
    if (defined $found) {
        $path = rebuilt_path(stitch_tail($Start, build_tail($found)));
        replay_check($path);
        $reason = 'SOLVED';
        $sollen = length($path);
        $steps  = $path =~ tr/DLRU//;
    }

    # every slot filled, as in solve_forward; the last three are read
    # backward-specifically: queue peak, queue left, configs generated
    my $rate_div = $doba || 1;        # instant solves can have doba ~ 0
    my $ending   = sprintf $ENDING,
        'BACKWARD', $Gameid, $Game{'nbox'}, $Game{'ncell'}, $reason, $sollen || $limit, $steps, $doba,
        sprintf('%.0f', $bc / $rate_div), sprintf('%.0f', $counter / $rate_div),
        $MaxOpen,
        $nopen, scalar %Bseen;
    barva($reason, $ending);
    bad_close($reason eq 'SOLVED' ? 1 : 0);
    my $nseen = scalar %Bseen;        # TAKEN FIRST: free_memory() empties %Bseen
    free_memory();
    return ($reason, $path, $doba, $nseen);
} ## end sub solve_backward
##############################################################################
# ===== Conveyor ===========================
##############################################################################
# CONVEYOR: for games with a forced common-path "conveyor" -- ride one box
# along it to the endpoint, then deliver boxes to goals along precomputed
# routes. Returns NOCP when the game has no conveyor (inapplicable, not a
# give-up). The conveyor data (common_path / c_path / to_goal) is RECOMPUTED
# here from cm/cmk/cg/order, not read from the blob.
my (%ConvCP, @ConvCR, %ConvTG);    # common_path {player}{box}=>idx / c_path [[s,t]] / to_goal {g}=>[[m,bx]]
sub _conv_boxes($pos) {my (undef, @b) = unpack($pu, $pos); return @b;}

# walk-BFS over @Cg from $man, cells in $wall (hashref) impassable -> {cell=>dist}
sub _conv_walk($man, $wall) {
    my %d = ($man => 0);
    my @q = ($man);
    while (@q) {
        my $x  = shift @q;
        my $nd = $d{$x} + 1;
        for my $t (@{ $Cg[$x] // [] }) {
            next if $wall->{$t} || exists $d{$t};
            $d{$t} = $nd;
            push @q, $t;
        }
    }
    return \%d;
}

# single-box optimal push route $bx -> $goal (Dijkstra, empty field); returns
# (\%states, \@route) with %states{player}{box} counted over the route.
sub _conv_route_cp($bx, $goal) {
    my (@heap, %seen, %parent);
    my ($bestlen, $best) = (1e9, undef);
    for my $t (@{ $Cmk{$bx} // [] }) {
        my $p = pack('n*', $Cm{$bx}{$t}, $bx);
        push @heap, $p;
        $seen{$p}   = 0;
        $parent{$p} = '';
    }
    while (@heap) {
        @heap = sort {$seen{$a} <=> $seen{$b}} @heap;
        my $p = shift @heap;
        my ($man, $bag) = unpack('n*', $p);
        my $cd = $seen{$p};
        next if $cd > $bestlen;
        my $d = _conv_walk($man, { $bag => 1 });
        for my $t (@{ $Cmk{$bag} // [] }) {
            my $s = $Cm{$bag}{$t};
            next unless defined $d->{$s};
            my $sl = $cd + $d->{$s};
            next if $sl > $bestlen;
            my $c = pack('n*', $bag, $t);
            if ($t == $goal) {$bestlen = $sl; $best = $c; $seen{$c} = $sl; $parent{$c} = $p; next;}
            next if exists $seen{$c} && $sl >= $seen{$c};
            $seen{$c}   = $sl;
            $parent{$c} = $p;
            push @heap, $c;
        }
    } ## end while (@heap)
    return ({}, []) unless defined $best;
    my @u = ($best);
    my $p = $best;
    while ($p = $parent{$p}) {unshift @u, $p;}
    my (%st, @route);
    for my $pos (@u) {my ($man, $bag) = unpack('n*', $pos); ++$st{$man}{$bag}; push @route, [$man, $bag];}
    return (\%st, \@route);
} ## end sub _conv_route_cp

# single-box route (man,box) -> goal $g, @$blocked boxes standing; [[src,tgt],...] or ()
sub _conv_route_to_goal($man, $box, $g, $blocked) {
    my %bag   = map {($_, 1)} @$blocked;
    my $start = pack('n*', $man, $box);
    my (%seen, %parent);
    $seen{$start}   = 0;
    $parent{$start} = '';
    my @heap = ($start);
    my ($bestlen, $best) = (1e9, undef);
    while (@heap) {
        my $p = shift @heap;
        my ($m, $bx) = unpack('n*', $p);
        my $sol = $seen{$p};
        my $r   = _conv_walk($m, { %bag, $bx => 1 });
        for my $t (@{ $Cmk{$bx} // [] }) {
            next if $bag{$t};
            my $s = $Cm{$bx}{$t};
            next unless defined $r->{$s};
            my $sl = $sol + $r->{$s};
            next if $sl >= $bestlen;
            my $c = pack('n*', $bx, $t);
            next if exists $seen{$c} && $seen{$c} <= $sl;
            $seen{$c}   = $sl;
            $parent{$c} = $p;
            if ($t == $g) {$bestlen = $sl; $best = $c; next;}
            push @heap, $c;
        }
    } ## end while (@heap)
    return () unless defined $best;
    my @u = ([unpack('n*', $best)]);
    my $p = $best;
    while ($p = $parent{$p}) {unshift @u, [unpack('n*', $p)];}
    shift @u;
    return @u;
} ## end sub _conv_route_to_goal

# Recompute %ConvCP / @ConvCR / %ConvTG from scratch. Leaves @ConvCR empty
# (and %ConvCP/%ConvTG cleared) if there is no usable conveyor.
sub build_conveyor() {
    %ConvCP = ();
    @ConvCR = ();
    %ConvTG = ();

    # $nvalid = the routes actually built, which is what the "common to ALL
    # of them" test has to be measured against. The count is NOT nbox^2: the
    # loop skips a pair whose box already stands on that goal, and a pair
    # with no route at all constrains nothing. (With the old nbox^2 threshold
    # even ONE box starting on a goal made the threshold unreachable and the
    # mode reported NOCP on 55 % of the database -- the 2.16 fix.)
    my (%common, %routes);
    my $nvalid = 0;
    for my $bx (@Baggage) {
        for my $g (@Goal) {
            next if $bx == $g;
            my ($pc, $route) = _conv_route_cp($bx, $g);
            next unless @$route;
            ++$nvalid;
            for my $s (keys %$pc) {for my $t (keys %{ $pc->{$s} }) {$common{$s}{$t} += $pc->{$s}{$t};}}
            $routes{$bx}{$g} = $route;
        }
    }
    my $req = $nvalid;
    my %gh  = map {($_, 1)} @Goal;
    my %cp_count;    # moves appearing in ALL the routes (count == req)
    for my $bx (keys %common) {
        my $th = $common{$bx};
        while (my ($t, $v) = each %$th) {

            # An edge LANDING on a goal is never part of the conveyor -- the
            # endpoint must sit OFF the goals. SKIP that edge (a `last` here
            # would abandon the scan at whatever key order put first).
            next                   if $gh{$t};
            $cp_count{$bx}{$t} = 1 if $v == $req;
        }
    }
    for my $bx (keys %routes) {
        my $th = $routes{$bx};
        while (my ($g, $v) = each %$th) {
            for my $x (@$v) {my ($s, $t) = @$x; push @$x, (exists $cp_count{$s}{$t} ? 1 : 0);}
        }
    }
    %common = ();
    for my $bx (keys %routes) {
        my $tgc = $routes{$bx};
        while (my ($g, $v) = each %$tgc) {
            my $idx;
            for my $s (@$v) {
                next if $s->[2] == 0 && !defined $idx;
                $idx //= 0;
                if ($s->[2] == 1) {
                    $common{ $s->[0] }{ $s->[1] } //= $idx;
                    if ($common{ $s->[0] }{ $s->[1] } != $idx) {%ConvCP = (); return;}    # non-sequential
                    ++$idx;
                }
            }
        }
    } ## end for my $bx (keys %routes)
    unless (%common) {%ConvCP = (); return;}
    for my $bx (keys %common) {while (my ($t, $i) = each %{ $common{$bx} }) {$ConvCR[$i] = [$bx, $t];}}
    unless (@ConvCR && defined $ConvCR[-1]) {%ConvCP = (); @ConvCR = (); return;}
    %ConvCP = %common;    # the index-based structure -> conv_to_end's start_idx = ConvCP{source}{target}
    my ($man, $box) = @{ $ConvCR[-1] };
    my @ng = sort {($Priority[$b] // 0) <=> ($Priority[$a] // 0)} @Goal;
    my $g  = shift @ng;
    my (@blk, %tg);
    my $found = 0;
    my @p     = _conv_route_to_goal($man, $box, $g, \@blk);

    if (@p) {
        $found = 1;
        $tg{$g} = \@p;
        push @blk, $g;
        while (@ng) {
            $g = shift @ng;
            my @p2 = _conv_route_to_goal($man, $box, $g, \@blk);
            next unless @p2;
            ++$found;
            $tg{$g} = \@p2;
            push @blk, $g;
        }
    }
    %ConvTG = ($found == $Nbox) ? %tg : ();
    return;
} ## end sub build_conveyor

# Simple push generator: [source,target] pairs for reachable, non-deadlock pushes.
sub conv_moves($pos) {
    my ($man, @boxes) = unpack($pu, $pos);
    my %bag = map {($_, 1)} @boxes;
    paint($man, @boxes);
    my @moves;
    for my $bx (@boxes) {
        for my $t (@{ $Cmk{$bx} // [] }) {
            next if $bag{$t};
            my $s = $Cm{$bx}{$t};
            next unless $Vis[$s] == $PaintId;
            my %tbag = map {($_, 1)} ($t, grep {$_ != $bx} @boxes);
            next if is_bad($bx, $t, \%tbag);
            push @moves, [$bx, $t];
        }
    }
    return @moves;
} ## end sub conv_moves

# Deliver box (currently at $box) to a goal along $tg = ConvTG{$g}. Threads
# each single push into %Parent; returns 1 on completion (or solve).
sub conv_to_goal($pos, $box, $tg) {
    my ($man, @boxes) = unpack($pu, $pos);
    for my $mv (@$tg) {
        paint($man, @boxes);
        my %bag = map {($_, 1)} @boxes;
        my ($m, $bx) = @$mv;
        my $player = $Cm{$m}{$bx};
        return 0 unless defined $player && $Vis[$player] == $PaintId;
        return 0 if $bag{$bx};
        my @nb    = sort {$a <=> $b} map {$_ == $box ? $bx : $_} @boxes;
        my $child = pack($pu, $box, @nb);
        my %nbag  = map {($_, 1)} @nb;
        if (is_bad($box, $bx, \%nbag)) {set_bad($child); return 0;}
        return 0 if isbad($child);
        return 0 if exists $Parent{$child};
        $Parent{$child} = $pos;
        if (exists $Sols{$child}) {$Bestbet = $child; return 1;}
        $Pex->add($child, value_score($box, $bx, \%nbag));
        $man   = $m;
        $box   = $bx;
        @boxes = @nb;
        $pos   = $child;
    } ## end for my $mv (@$tg)
    return 1;
} ## end sub conv_to_goal

# Ride one box along the common-path conveyor from the ConvCP index of
# (source,target) to the endpoint, then deliver it to a top-tier free goal.
sub conv_to_end($pos, $source, $target) {
    my $start_idx = $ConvCP{$source}{$target};
    return unless defined $start_idx;
    my ($man, @boxes) = unpack($pu, $pos);
    my %bag = map {($_, 1)} @boxes;
    return unless $bag{$source};
    my $parent = $pos;
    my ($last_added, $last_box);
    my %to_add = map {($_, 1)} ($start_idx .. $#ConvCR);

    for my $i ($start_idx .. $#ConvCR) {
        my ($cs, $ct) = @{ $ConvCR[$i] };
        next unless $bag{$cs};
        next if $bag{$ct};
        my $player = $Cm{$cs}{$ct};
        next unless defined $player;
        paint($man, @boxes);
        next unless $Vis[$player] == $PaintId;
        my @nb    = sort {$a <=> $b} map {$_ == $cs ? $ct : $_} @boxes;
        my $child = pack($pu, $cs, @nb);
        my %nbag  = map {($_, 1)} @nb;
        if (is_bad($cs, $ct, \%nbag)) {set_bad($child); last;}
        last if isbad($child);
        last if exists $Parent{$child};
        $Parent{$child} = $parent;
        delete $to_add{$i};
        $last_added = $child;
        $last_box   = $ct;
        $Pex->add($child, value_score($cs, $ct, \%nbag));
        $parent = $child;
        $man    = $cs;
        @boxes  = @nb;
        %bag    = %nbag;
    } ## end for my $i ($start_idx .....)
    return if %to_add;
    return unless defined $last_added;
    ($man, @boxes) = unpack($pu, $last_added);
    %bag = map {($_, 1)} @boxes;
    my @free = grep {!$bag{$_}} @Goal;
    return unless @free;
    my $index = &max(map {$Priority[$_] // 0} @free);
    @free = grep {($Priority[$_] // 0) == $index} @free;

    for my $g (@free) {
        next unless exists $ConvTG{$g};
        last if conv_to_goal($last_added, $last_box, $ConvTG{$g});
    }
    return;
} ## end sub conv_to_end

sub solve_conveyor($limit) {
    my $timer = [&gettimeofday()];
    $Bestbet = undef;
    build_conveyor();

    # NOCP ("no common path"), NOT GIVEUP: this game simply has no forced
    # conveyor, so the mode is INAPPLICABLE here -- it never searched and
    # never abandoned anything. GIVEUP below is the real thing (the conveyor
    # search exhausted its restricted tree), and the drivers' "prior GIVEUP"
    # rules must keep meaning that.
    unless (@ConvCR) {
        my $doba = clamp_doba(tv_interval($timer));

        # the HEAD of $ENDING and nothing after it: this game has no forced
        # conveyor, so there was no search to report. Keep the widths equal to
        # $ENDING's first five fields or the line stops lining up with the rest.
        backlinen(sprintf '%-12s %5d %3d %4d %-10s', 'CONVEYOR', $Gameid, $Game{'nbox'}, $Game{'ncell'}, 'NOCP')
            if $QUIET < 2;
        bad_close(0);
        free_memory();
        return ('NOCP', '', $doba, 0);
    }
    $Parent{$Start} = '';
    $Pex->add($Start, 0);
    my $nseen   = 1;
    my $counter = 0;
    my $reason  = 'GIVEUP';
    my ($CRaceNext, $CMemNext) = (1, $SCREEN);    # the two guard periods, seconds
    while ($Pex->size) {
        my $pozice = $Pex->next;
        next if isbad($pozice);
        unless (++$counter % 200) {

            # The budget on this gate; the other two on their own periods -- see
            # the note at the top of the file. This search had no race check at
            # all until 2026-09-10, so CONVEYOR could not report IGNORE and went
            # on spending its whole budget after another mode had solved the
            # game: an inconsistency between modes rather than a policy.
            my $ot = tv_interval($timer);
            if ($limit and $ot > $limit) {$reason = 'TIMEOUT'; last;}
            if ($ot > $CRaceNext) {
                $CRaceNext = $ot + 1;
                if (race_lost()) {$reason = 'IGNORE'; last;}
            }
            if ($ot > $CMemNext) {
                $CMemNext = $ot + $SCREEN;
                if (mem_over()) {$reason = 'MEMCAP'; last;}
            }
        } ## end unless (++$counter % 200)
        my @boxes = _conv_boxes($pozice);
        for my $mv (conv_moves($pozice)) {
            my ($src, $tgt) = @$mv;
            my @nb    = sort {$a <=> $b} map {$_ == $src ? $tgt : $_} @boxes;
            my $child = pack($pu, $src, @nb);
            next if isbad($child);
            if (exists $Sols{$child}) {
                $Parent{$child} = $pozice unless exists $Parent{$child};
                $Bestbet = $child;
                last;
            }
            next if exists $Parent{$child};
            ++$nseen;
            if (exists $ConvCP{$src}{$tgt}) {
                conv_to_end($pozice, $src, $tgt);
                last if $Bestbet;
            }
            next if isbad($child) || exists $Parent{$child};
            $Parent{$child} = $pozice;
            my %tbag = map {($_, 1)} @nb;
            $Pex->add($child, value_score($src, $tgt, \%tbag));
        } ## end for my $mv (conv_moves(...))
        last if $Bestbet;
    } ## end while ($Pex->size)
    my ($path, $sollen, $steps) = ('', 0, 0);
    if ($Bestbet) {
        $reason = 'SOLVED';
        $path   = get_path($Bestbet);
        my $tail = $Sols{$Bestbet};    # box-on-P terminal -> P->ga finishing moves ('' / legacy 1 otherwise)
        $path .= $tail if defined $tail && $tail =~ /[A-Za-z]/;
        $path = rebuilt_path($path);
        replay_check($path);
        $sollen = length $path;
        $steps  = $path =~ tr/DLRU//;
    }
    my $doba = clamp_doba(tv_interval($timer));

    # the forced-conveyor walk keeps no queue and no rates: only the seen count
    my $ending = sprintf $ENDING,
        'CONVEYOR', $Gameid, $Game{'nbox'}, $Game{'ncell'}, $reason, $sollen || $limit, $steps, $doba,
        q{}, q{}, q{}, q{}, $nseen;
    barva($reason, $ending);
    bad_close($reason eq 'SOLVED' ? 1 : 0);
    free_memory();    # $nseen is already a plain number here -- safe
    return ($reason, $path, $doba, $nseen);
} ## end sub solve_conveyor
################################################################################
# ===== Plan (the packing plan, backward-simulated; FEATURE's first axis) =====
################################################################################
#
# build_plan(): pairing base<->goal + packing order + pull paths, produced by
# a BACKWARD SIMULATION on the real board: start from the SOLVED layout
# (boxes on goals, all of them real obstacles); per wave every box with a
# legal pull is a candidate (the rim of the goal cluster peels first, which
# IS the packing order read backwards); a single-box pull BFS per candidate
# collects every free base it can reach; a Munkres assignment picks who parks
# where (greedy first-found can strand a feasible pairing); the wave's pairs
# then execute serially: goal released, box removed, base consumed. Wave 1 =
# the goal filled LAST in forward play.
#
# The output is PARTIAL BY DESIGN: a complete reachability-valid pairing
# would amount to solving the game, so unpaired goals are a normal result,
# not a failure. Player continuity: after a journey the player stands at its
# last pull's stance; the next journey's first pull must be reachable from
# there. A consumed base is REMOVED (the cell becomes passable), Festival's
# rule.
#
# Results (one plan per FEATURE solve):
#   @PlanPair  = [goal_cell, base_cell, wave, [[from,to]...pulls], player_end]
#                in ELIMINATION order (wave 1 first = forward-latest first)
#   @PlanInit  = wave-0 goal cells (boxes born parked), mandatory: all must
#                be occupied or the odometer is just their occupied count
#   @PlanWaves = the forward parking sequence grouped by WAVE (highest wave
#                first = filled first); the odometer's walk
# (declared with the FEATURE state at the top of the file -- build_planneed
# in the Engine section reads @PlanPair, and a lexical must be declared above
# every sub that uses it)
# The plan odometer (Festival score_parked_boxes analog), WAVE-SOFTENED: a
# strict total order would be an artifact of the simulation's execution
# order. The prefix runs over WAVES: a fully occupied wave counts whole and
# the walk continues; the FIRST incomplete wave contributes its occupied
# count ("occupied" = a box stands on the cell, identity-blind) and ends the
# walk. Mandatory inits first: any missing -> the count of occupied inits is
# the whole value. Scale: 0 .. @PlanInit + total pair count.
sub plan_odometer($boxes) {
    my %has  = map  {($_, 1)} @$boxes;
    my $init = grep {$has{$_}} @PlanInit;
    return $init if $init < @PlanInit;
    my $v = scalar @PlanInit;
    for my $w (@PlanWaves) {
        my $occ = grep {$has{$_}} @$w;
        $v += $occ;
        last if $occ < @$w;    # first incomplete wave ends the prefix
    }
    return $v;
}

# The PUSH-IN existence test: a wave candidate $c is only admissible if, with
# the other still-unfilled goals standing as walls, a box pushed from SOME
# base can reach $c. The pull test verifies the wrong direction for forward
# validity (player on the opposite side); this is the right one. Boxes are
# fungible, so the seed is EVERY base, player anywhere -- an existence
# quantifier, optimistic like the rest of creation. Mirror of _plan_bfs with
# the push maps (%Cmk/%Cm); raw (box, man) states, paint() per expansion,
# early exit on $c.
sub _plan_push_bfs($c, $blk) {
    my (%seen, @q);
    for my $s (@Baggage) {
        next if $blk->{$s};
        for my $t (@{ $Cmk{$s} // [] }) {
            next if $blk->{$t};
            my $stance = $Cm{$s}{$t};
            next     if !defined $stance || $blk->{$stance};
            return 1 if $t == $c;
            my $key = pack('nn', $t, $s);
            next if $seen{$key}++;
            push @q, [$t, $s];
        }
    }
    my $h = 0;
    while ($h < @q) {
        my ($p, $m) = @{ $q[$h++] };
        paint($m, (keys %$blk), $p);
        for my $t (@{ $Cmk{$p} // [] }) {
            next if $blk->{$t};
            my $stance = $Cm{$p}{$t};
            next     if !defined $stance || $blk->{$stance} || $Vis[$stance] != $PaintId;
            return 1 if $t == $c;
            my $key = pack('nn', $t, $p);
            next if $seen{$key}++;
            push @q, [$t, $p];
        }
    }
    return 0;
} ## end sub _plan_push_bfs

# Single-box pull BFS on the simulated board: box starts at $c, $blk =
# blocked cells (other boxes), $cur = player cell for the chain constraint
# (undef = unconstrained, the first journey), $base = free-base pool. Raw
# state keys (box, man): after a pull the player always ends on a stance
# cell, so there are at most 4 states per box cell -- canonicalization would
# buy nothing. Returns ({base => [cost, endkey]}, {key => [parent, from,
# to]}, {key => man}).
sub _plan_bfs($c, $blk, $cur, $base) {
    my (%par, %man, %hit, @q);
    my $reach;
    if (defined $cur) {
        paint($cur, (keys %$blk), $c);
        $reach = $PaintId;
    }
    for my $b (@{ $Pull{$c} // [] }) {
        next if $blk->{$b};
        my $ma = $PullMan{$c}{$b};
        next if $blk->{$ma};
        next if defined $cur && $Vis[$b] != $reach;
        my $key = pack('nn', $b, $ma);
        next if exists $par{$key};
        $par{$key} = [undef, $c, $b];
        $man{$key} = $ma;
        push @q, [$b, $ma, 1, $key];
        $hit{$b} = [1, $key] if $base->{$b} && !exists $hit{$b};
    }
    my $h = 0;
    while ($h < @q) {
        my ($p, $m, $d, $key) = @{ $q[$h++] };
        paint($m, (keys %$blk), $p);
        for my $b (@{ $Pull{$p} // [] }) {
            next if $blk->{$b};
            my $ma = $PullMan{$p}{$b};
            next if $blk->{$ma};
            next if $Vis[$b] != $PaintId;
            my $nkey = pack('nn', $b, $ma);
            next if exists $par{$nkey};
            $par{$nkey} = [$key, $p, $b];
            $man{$nkey} = $ma;
            push @q, [$b, $ma, $d + 1, $nkey];
            $hit{$b} = [$d + 1, $nkey] if $base->{$b} && !exists $hit{$b};
        }
    } ## end while ($h < @q)
    return (\%hit, \%par, \%man);
} ## end sub _plan_bfs

# Pull path of one journey: walk the parent chain back from the base-reaching
# state; returns [[from,to],...] in pull order (goal -> base).
sub _plan_path($key, $par) {
    my @pulls;
    while (defined $key) {
        my ($pk, $from, $to) = @{ $par->{$key} };
        unshift @pulls, [$from, $to];
        $key = $pk;
    }
    return \@pulls;
}

sub build_plan() {
    @PlanPair   = ();
    @PlanInit   = ();
    @PlanWaves  = ();
    $Plan_waves = 0;
    return unless @Goal == $Nbox;         # unique solved layout only
    build_pull();                         # %Pull/%PullMan fresh for THIS game
    my %box  = map(($_, 1), @Goal);       # simulated board: boxes on goals
    my %base = map(($_, 1), @Baggage);    # unconsumed bases
    my $cur;                              # player cell after the last journey

    # zero-length eliminations: a box standing on a goal that IS a free base
    # may simply stay put -- pair it in place (wave 0). Optimistic: the real
    # game might need it to step aside and return; advice-grade like the rest.
    for my $g (sort {$a <=> $b} grep {$base{$_}} keys %box) {
        push @PlanPair, [$g, $g, 0, [], undef];
        delete $box{$g};
        delete $base{$g};
    }
    my $NOEDGE = 100_000_000;    # no edge
    my $DUMMY  = 1_000_000;      # padding: beats no-edge, loses to any real path
    while (%box) {
        ++$Plan_waves;

        # candidates select themselves by the local pull test
        my (@cand, %ptree, %mantab, %hits);
        for my $c (sort {$a <=> $b} keys %box) {
            my $blk = {%box};
            delete $blk->{$c};
            my ($hit, $par, $man) = _plan_bfs($c, $blk, $cur, \%base);
            next unless %$hit;

            # forward push-in must ALSO exist (see _plan_push_bfs)
            next unless _plan_push_bfs($c, $blk);
            push @cand, $c;
            ($hits{$c}, $ptree{$c}, $mantab{$c}) = ($hit, $par, $man);
        }
        last unless @cand;

        # Munkres over (candidate x free base); pad square with DUMMY
        my @bases = sort {$a <=> $b} keys %base;
        my $n     = @cand > @bases ? scalar @cand : scalar @bases;
        my @mx;
        for my $i (0 .. $n - 1) {
            my $c = $cand[$i];
            push @mx, [
                map {
                    my $b = $bases[$_];
                    (defined $c && defined $b) ? ($hits{$c}{$b} ? $hits{$c}{$b}[0] : $NOEDGE) : $DUMMY
                    } 0 .. $n - 1
            ];
        }
        my @out;
        Games::Sokoban::Solver::Munkres::assign(\@mx, \@out);
        my @todo;    # [goal, base, cost, endkey]
        for my $i (0 .. $#cand) {
            my $b = $bases[$out[$i]] // next;
            my $e = $hits{ $cand[$i] }{$b} or next;    # DUMMY/NOEDGE cell = unmatched
            push @todo, [$cand[$i], $b, @$e];
        }

        # execute serially; chain re-checked against the CURRENT player cell
        # (deferred pairs stay boxes -- candidates again next wave)
        my $done = 0;
        while (@todo) {
            my $pick;
            for my $i (0 .. $#todo) {
                my ($c, $b, $cost, $ekey) = @{ $todo[$i] };
                if (defined $cur) {
                    my ($f, $t) = @{ _plan_path($ekey, $ptree{$c})->[0] };
                    paint($cur, (grep {$_ != $c} keys %box), $c);
                    next if $Vis[$t] != $PaintId;
                }
                $pick = $i;
                last;
            }
            last unless defined $pick;
            my ($c, $b, $cost, $ekey) = @{ splice(@todo, $pick, 1) };
            push @PlanPair, [$c, $b, $Plan_waves, _plan_path($ekey, $ptree{$c}), $mantab{$c}{$ekey}];
            $cur = $mantab{$c}{$ekey};
            delete $box{$c};
            delete $base{$b};
            ++$done;
        } ## end while (@todo)
        last unless $done;    # a wave that executes nothing ends the plan
    } ## end while (%box)

    # the odometer's views: wave-0 pairs split off as the mandatory inits;
    # @PlanWaves groups the cells by wave (highest wave = filled first)
    @PlanInit = map {$_->[0]} grep {$_->[2] == 0} @PlanPair;
    my %bywave;
    push @{ $bywave{ $_->[2] } }, $_->[0] for grep {$_->[2] > 0} @PlanPair;
    @PlanWaves = map {$bywave{$_}} sort {$b <=> $a} keys %bywave;
    return;
} ## end sub build_plan
################################################################################
# ===== dispatcher =============================================================
################################################################################
# Thin dispatcher: the mode-agnostic setup, then the part a mode needs.
# BACKWARD is a pure pull-search (no scorer, no is_bad, no matching); every
# other mode -- the FORWARD scorers (incl FLOW and FEATURE), ORDER and
# CONVEYOR (which call $Value + is_bad) -- needs the scoring/deadlock
# precompute in initvars_score(). FEATURE's own prerequisites (the packing
# plan, the room decomposition, the plan's journeys) are built here and in
# initvars_common, gated per game by $Feat_mode -- the other modes never
# build any of it.
sub initvars($gameid, $gm, $mode = 'PUSH_SCORE') {
    initvars_common($gameid, $gm, $mode);
    if ($Feat_mode) {
        build_plan();
        build_planneed();
    }
    else                     {@PlanNeed = ()}
    if ($mode eq 'BACKWARD') {initvars_backward()}
    else                     {initvars_score($mode)}
}

sub solve($gameid, $gm, $limit, $mode = 'PUSH_SCORE') {
    initvars($gameid, $gm, $mode);
    return solve_backward($limit) if $mode eq 'BACKWARD';
    return solve_order($limit)    if $mode eq 'ORDER';
    return solve_conveyor($limit) if $mode eq 'CONVEYOR';
    return solve_forward($limit, $mode);
}
##############################################################################
# ===== free_memory ==========================================================
#
# Hand the search's containers back to Perl's own pool at the END of a search,
# instead of leaving them standing until the next solve() reaches clearvars().
#
# WHY IT IS WORTH ANYTHING AT ALL. Perl never returns memory to the operating
# system, so the only thing any clear can buy is that the NEXT allocation takes
# the old space rather than asking for more -- and it does. Measured on
# 1.5M-entry hashes, rebuilding one costs +0.1 MB after `undef`, +30 MB after
# `%h = ()` (which frees the values but KEEPS the bucket table), +55 MB after
# deleting key by key, and +223 MB with the first hash still alive. So `undef`
# is the clear that pays, and it has to be undef.
#
# WHAT IT DOES NOT DO: lower the peak of one hard game. Nothing is droppable
# while the search still needs it. What it lowers is the per-game GROWTH of a
# process working through a batch -- 8 games sequentially ended at 202 MB
# instead of 306 MB, and after the first big game the growth largely stops.
# Threaded, where all workers are deep at the same moment, the peak moved only
# 4.6 % (2447 -> 2334 MB over 9 workers), so batch size still governs the
# ceiling.
#
# THE SET is exactly what clearvars() covers -- so the next solve()
# re-initialises every one of them before it is read, and this cannot change
# what a search does -- plus the four searches' own seen-sets, each of which
# its own search or builder already clears at entry (%Bseen in
# solve_backward, %Pull/%PullMan in build_pull, %Conv* in build_conveyor,
# %MemBad/%Tahy in bad_init, %OSeen in solve_order).
#
# EVERY CALLER TAKES ITS RETURN VALUES FIRST. solve_forward reports nseen as
# `scalar %Parent` and solve_backward as `scalar %Bseen`; called before
# those are read this would turn both into a silent 0 in every campaign.
#
# ONE VISIBLE SIDE EFFECT, and it is why $VERSION moved. `%h = ()` left the
# next game a bucket table sized for the previous one; Perl's `keys` order
# depends on that size and BACKWARD breaks ties in `keys` order, so a game's
# walk depended on which game the worker did before it. Measured on game 582:
# the old code walked 683 positions alone and 655 after game 76, the new code
# 683 either way. Same solutions, different walk -- BACKWARD only, the other
# eight modes are untouched.
#
# It sits at the END of the file because a lexical must be DECLARED above the
# code that names it, and the backward / order / conveyor containers are
# declared beside their own searches, far below clearvars().
sub free_memory() {
    undef @Baggage;
    undef @Blk;
    undef %Bseen;
    undef @Buf;
    undef @Buf_c;
    undef @Buf_fr;
    undef %CanonMap;
    undef @Cg;
    undef %Cm;
    undef %Cmk;
    undef %ConvCP;
    undef @ConvCR;
    undef %ConvTG;
    undef %CPath;
    undef @CPathArr;
    undef %CPathIdx;
    undef %ExplMark;
    undef @FCellKey;
    undef @IsStart;
    undef @PullTo;
    undef %FCellQ;
    undef %Game;
    undef @Goal;
    undef @IsWall;
    undef @Maze;
    undef %MemBad;
    undef %OSeen;
    undef %Parent;
    undef %Pis;
    undef @Priority;
    undef %Pull;
    undef %PullMan;
    undef %RegCells;
    undef %Sols;
    undef %SolsC;
    undef %StanceIdx;
    undef %Tahy;
    undef @Target;
    undef %ToGoal;
    undef @Vis;
    undef @Vis_c;
    undef @Vis_fr;

    # scalars holding a reference into the blob or a built structure: the
    # container above is only really freed once the last reference to it goes
    $Bestbet = $Blok  = $BlokVec = $Corridor = $Distance = $Hole = undef;
    $Pex     = $Route = $Wall    = undef;
    return;
} ## end sub free_memory
1;
__END__

=head1 NAME

Games::Sokoban::Solver::Firstbet - the first-solution engine: ten search modes over one level analysis

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Firstbet ();

    $Games::Sokoban::Solver::Firstbet::QUIET = 2;
    my ($reason, $path, $seconds, $positions)
        = Games::Sokoban::Solver::Firstbet::solve($label, $game_blob, 60, 'FEATURE');

=head1 DESCRIPTION

A heuristic search for a first solution of a level, in ten modes that share
one move generator, one deadlock battery and one set of macros and differ in
how they order the search. The level comes in as the analysis of
L<Games::Sokoban::Solver::Parser> in its C<blob> form; the result goes back to
the caller, who owns it. Nothing is stored and nothing is printed above
C<$QUIET>.

This is Games::Sokoban::Firstbet 3.8 of the Sokoban project, where the
engine was built and measured over a database of 32 000 levels; only the
modules it leans on were rewired here, the search is untouched. The comments
at the top of the source say what each piece of machinery is and when it was
promoted.

=head2 The modes

    PUSH_SCORE   quadratized push distance of every box to the goals (the default)
    MOVE_SCORE   the same on move distances
    PUSH_ASSIGN  the Hungarian assignment of boxes to goals on raw push distances
    MOVE_SUM     the sum of raw move distances
    ROUTE        bands along the routes boxes take to the goals
    FLOW         route-dominant, with a coarse gradient
    ORDER        a depth-first walk over the ladder in which the goals must be filled, with macros
    BACKWARD     a pull search from the solved level back towards the start
    CONVEYOR     macro delivery along a forced common path (only on levels that have one)
    FEATURE      the feature-space search: positions filed by four counts, advised pushes free

L<Games::Sokoban::Solver::Portfolio> names them in their order of strength.

=head1 INTERFACE

=head2 solve

    my ($reason, $path, $seconds, $positions) = solve($label, $game_blob, $limit, $mode);

C<$label> is any integer the caller names the level by (it is printed in the
progress lines); C<$limit> seconds, 0 = no time limit; C<$mode> one of the
ten, C<PUSH_SCORE> by default. C<$path> is the solution for the reduced level
in the letters C<u r d l> (a step) and C<U R D L> (a push), written again from
its pushes before it is returned; C<$positions> the positions the search saw.

C<$reason>: C<SOLVED>; C<TIMEOUT>; C<UNSOLVABLE> (the whole state space was
searched -- on a level the Parser accepted this is a defect worth reporting);
C<GIVEUP> (ORDER or CONVEYOR exhausted its restricted tree, which is not the
whole state space); C<NOCP> (CONVEYOR on a level without a forced common path:
the mode did not search at all); C<IGNORE> (another mode of a race won the
level); C<MEMCAP> (the memory ceiling).

=head2 Run control

    our $QUIET      0 = every progress line, 1 = no transient lines, 2 = nothing
    our $MAX_GB     stop as MEMCAP when the whole machine uses more than this many GiB; 0 = off
    our $RACE_FLAG  a hash reference, label => true, polled once a second: the level is won elsewhere
    our $RACE_GID   the label this solve is running

These are set by the caller before C<solve>; L<Games::Sokoban::Solver::Race>
sets the last two for every worker.

=head1 CAVEATS

BACKWARD keeps a cache of pull tables between the levels one process solves,
so its path for a level may differ from the path it returns for the same level
alone; every path returned is a solution all the same. The deadlock patterns
of the level come from the analysis, and a table computed under a budget is
smaller than the complete one -- the search then takes another way or fails
where a complete table would not.

=head1 SEE ALSO

L<Games::Sokoban::Solver>, L<Games::Sokoban::Solver::Parser>,
L<Games::Sokoban::Solver::Portfolio>, L<Games::Sokoban::Solver::Firstbet::Berk>
(the same engine with its caches on disk).

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
