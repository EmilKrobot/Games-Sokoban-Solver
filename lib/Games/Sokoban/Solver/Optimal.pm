package Games::Sokoban::Solver::Optimal;
our $VERSION = '0.01';

# THE OPTIMAL SOLVER: the shortest solution in player moves, proved. Three search regimes
# in one file, chosen by $MODE (DIAL, ASTAR, FIFO); solve($gameid, $gm, $seed_path) takes
# the Parser's analysis in its blob() form and a solution to start from (an upper bound;
# undef for none) and returns ($reason, $path, $seconds, $candidates, $pops): SOLVED =
# the path is proved shortest, TIMEOUT = the best path found, not proved, UNSOLVABLE =
# the whole state space was searched and no solution exists, IGNORE = stopped by a race.
# $LastStatus says what stopped a TIMEOUT (TIMEOUT, MEMCAP or IGNORE); $ON_IMPROVED, if
# set, is called with ($path, $seconds) at every improvement; @Track keeps them.
#
# This is Games::Sokoban::Solver 3.3 of the Sokoban project with its storage cut away:
# there every improvement was written to a database table and the search's deadlock and
# move caches could live in BerkeleyDB for runs of days; here the caches are in RAM for
# one solve (the project's BerkeleyDB twin is Games::Sokoban::Solver::Optimal::Berk) and
# the caller owns the result. The search itself is the project's, untouched; the notes
# below are its history, kept because they say WHY the search is shaped as it is.
#
# $BAND_DRY (2026-09-07, USER): a callback run at the one place where "band N is exhausted
#   around this record" is known -- the FIFO heap ran dry under a band that dropped
#   children -- with the band width, the drop count, the record and the elapsed time; a
#   TRUE return stops the solve there as TIMEOUT (the record stands, unproven), undef is
#   inert. It is here in the baseline, not only in the slot, so that the band's PROPERTY
#   GATE ai/band_vs_proof.pl (no claimed proof above a stored optimum -- the gate that
#   found the false proof of 3.1 on game 7265) holds the module campaigns actually run.
#
# v3.3 -- THE OVERRUN (2026-09-17, USER): DIAL and ASTAR may run past $LIMIT, up to twice
#   it, while the level profile says the proof is near. FIFO had always had an easing of
#   its own ("the wave is draining", $N_Open > 0.7 * $MaxOpen), and in proof-3 117 of its
#   131 proofs came after the limit; that condition does not carry over, because without
#   restarts the frontier peak is run-wide and the queue shrinks ~120 moves before the
#   record. What does: a level's price rises and then FALLS toward the record, so the
#   last two levels predict the rest (see overrun_ok). Replayed over the level profiles of
#   proof-1..3 (13 239 runs): at limits >= 60 s DIAL 634 of 1 026 late proofs, ASTAR 784
#   of 914, ~1 s wasted per run. A/B ab-ease-1 (40 games, race of all three modes, 60 s,
#   seed firstbet): games proved 8 -> 17, none lost, wall +10 %; the 15 hopeless games
#   cost 1 s in all; no proof above a stored optimum. Memory project_dial_astar_overrun.
#
# v3.2 -- BAND 2, THEN NOTHING (2026-09-07, USER): when the band-2 heap runs dry the
#   filter is dropped and the same record's surroundings are searched unrestricted,
#   instead of the 3.1 ladder 3, 4, ... $Nbox. Only a heap that dropped nothing proves, so
#   a wider band either drops something too (no proof, and its region is re-crawled by the
#   next width) or drops nothing (the very positions the unrestricted search visits, plus
#   the band test on every child). The ladder could only pay for improvements 3+ boxes off
#   the track, measured at 4 of 344. An improvement found unrestricted puts the band back
#   at $BAND around the new record, so the regime alternates: polish within two boxes
#   until dry, then hunt detours anywhere, then polish again. Measured with
#   ai/band_vs_proof.pl on 22 games paired against 3.1 (12 where band 2 was not the
#   optimum, 10 with the slowest proofs): same optimum on every game, no false proof, and
#   the proof came sooner on every pair (2125 30 s vs 45, 6952 97 vs 138, 13836 71 vs 104).
#
# v3.1 -- THE BAND (2026-09-06, USER): FIFO, the mining mode, searches inside a BAND
#   around the record -- a child more than $BAND boxes off the nearest configuration of
#   the record's box track is not queued. Measured first on where FIFO's wins come from
#   (four games, 344 improvements: 340 lie ENTIRELY within two boxes of the previous
#   record's track, while the wave spent 74-90 % of its positions three or more boxes
#   away), then as an A/B over 20 games with an unproven record, 300 s from the same seed:
#   band 2 shorter on 13, band 0 shorter on NONE, total shortening 2 366 against 1 707;
#   13268 went 490 -> 462 in 1 800 s where the unrestricted FIFO had found nothing in 300 s
#   and SolverBerk needed hours for four moves. The proof stays honest: a heap that ran
#   dry under a band that dropped children is NOT a proof, so solve() widened the band by
#   one box and restarted around the same record until the band was everything (the 3.1
#   ladder, replaced in 3.2 by dropping the band at once -- see above); four of the A/B
#   games were proved that way. $BAND = 0 is the pre-3.1 FIFO (the control arm).
#   $MAX_RESTARTS (the profiling stop) went in the same commit -- a tuning knob for the
#   profiler, not part of a production module (USER). Memory
#   project_fifo_wave_far_from_record.
# v3.0 -- THE PORTFOLIO (2026-09-02, USER): this module stops being ONE search regime and
#   becomes three, selected by $MODE -- which is why the major number moves, exactly as
#   Firstbet's did when it became a production portfolio. The wave that decided it ran
#   three arms over 200 tier-1 games and ended in a DRAW: FIFO (the restored 1.8) proved
#   160, ASTAR 157, DIAL 156, and each of them proved games the other two could not (five
#   only FIFO, one only ASTAR, one only the two bucket modes). The key had been agreed
#   BEFOREHAND -- "more proofs AND no game lost" -- and no arm met it. So there is no
#   winner to promote, and the answer is the USER's: "kazda hra je samostatny ukol."
#   See the $MODE block below for what the three are; ai/eq_solver_modes.pl is the gate,
#   and its shape is the point -- every mode answers to an oracle that already existed.
#   Memory: project_solver_portfolio.
#
# v2.1 -- THE LEVEL PROFILE (2026-09-01, USER's idea, promoted from the slot the same
#   day): record_level() writes one solve_level row per cost level the dial enters. It
#   changes nothing about the search -- one integer compare per pop, one INSERT per level
#   -- and the version bump is here so a solve_stats row says whether its run should have
#   the series at all. Promoted early, against the usual "let it prove itself" rule, for a
#   plain reason: the runs that need it are the multi-day SolverBerk ones, and the slot
#   has no Berk twin to carry it. See record_level() for what the rows are worth.
#
# v2.0 -- DIAL (2026-09-01, USER's design): the open list is a BUCKET QUEUE ordered by
#   position cost, replacing the FIFO + SPFA relaxation + conditional restart of 1.8.
#   @Bucket[$g] holds the positions whose recorded cost is $g; $CurMin walks the buckets
#   upward and never returns (every insert costs at least one move more than the position
#   it came from). What taking the cheapest position first buys, all of it measured:
#   * a popped position's cost is FINAL, so every position is expanded exactly once. The
#     1.8 re-queue verdict and the queued bit are gone; the low bit of %Seen now means
#     EXPANDED. A cheaper route to a waiting node inserts a second copy into the lower
#     bucket and the stale copy is skipped when its bucket comes up.
#   * bublej() survives as a pure relaxation cascade over continuations already on
#     record (the threaded seed path, a warm env's tahy.brk): a shortcut into a known
#     continuation is an improvement certificate the moment it is found. No re-queue
#     verdict (a relaxed waiting node MUST get its lower-bucket copy every time), no
#     unwinding; an expanded node stops the walk by itself. Near-inert on a cold run.
#   * the proof arrives EARLY: the moment $CurMin reaches $Bestlen, everything still
#     queued is provably no better than the record -- SOLVED without draining the tail.
#   * $CurMin is a live LOWER BOUND ("nothing shorter exists"), printed by info() and a
#     durable product even of a run that never finishes -- FIFO order had no such thing.
#   * improvements arrive sorted and late: terminals are generated in cost order, so the
#     first solution found is (nearly) the optimum and the 4-122-step improvement
#     staircases of the FIFO regime collapse to 1-2 per game.
#   * restart() is the SEED THREADER only; want_restart() and the restart loop are gone.
#     A restart's %Seen wipe would forfeit the finality invariant -- and the improvement
#     mining it used to provide (a restart re-threads the best path and FIFO explores its
#     neighbourhood = an accidental local search) belongs to a different tool now.
#   Promotion evidence (ai/smoke_solver01.pl ALL PASS; an A/B over the 9 proven games,
#   firstbet seeds, both arms loaded machine): 9/9 identical optima, total 1906 -> 1678 s
#   (-12 %, best 42929 -32 %), and the expansion count is seed-INVARIANT -- pops from a
#   bestbet seed vs a firstbet seed differ by tens against millions, while 1.8 paid up to
#   2x for the loose seed. Warm-env ratchet on 37654: a re-run reached the first run's
#   655 s frontier in 130 s (tahy.brk covers ~4/5 of the work below the old frontier).
#   Memory: project_solver_dial_experiment.
#
# v1.5 -- blok deadlock check as BIT VECTORS on the hot path (2026-08-06), the Firstbet
#   v2.10 technique applied family-wide on USER order (Solver/SolverBerk/SolverPush too,
#   so no module is left silently array-only after tools/update_block.pl converts the
#   blobs). _blok_both builds both shapes at load (dual-read: arrays or trimmed vecs);
#   tahy() keeps the box-set vector $vb in lockstep with %Bags; is_bad with $vb pays one
#   string (vb &. pv) eq pv per pattern. Gated: ai/smoke_solver01.pl ALL PASS,
#   ai/smoke_solverberk.pl ALL PASS. See memory project_blok_vec_bench.
#
# v1.4 -- is_frozen MEMOIZATION (behaviour-identical, +23% bc/doba, equivalence-gated 15/15):
#   is_frozen() is ~50% of solver CPU (its paint_fr flood). Its branch 0/1 verdict is a pure
#   function of (man's reachable region, sorted @nomove), so cache it keyed on
#   (paint()'s pocket-min, @nomove). pocket-min = the min cell of the man's reachable pocket,
#   tracked for free during the paint() flood tahy() already runs; a cell reachable under
#   all-boxes-walls is reachable under frozen-only-walls too, so it canonically ids the
#   paint_fr component -> sound. Branch 2 (all frozen on goals) is not cached (goal-corral
#   needs a fresh @Vis_fr). Saves 9-90% of is_frozen floods depending on topology.
#   Shared with Firstbet's is_frozen -- portable there for the same win.
#
# v1.3 -- HOT-PATH THROUGHPUT PASS (behaviour-identical, ~+26% bc/doba): ported the proven
#   Firstbet v2.4-2.6 wins that Solver's shared hot path (paint/paint_fr/is_frozen/tahy) had
#   never received. Five byte-identical changes (equivalence-gated 15/15, fixed hash seed):
#   goal-corral reuses is_frozen's last paint_fr; tahy() reuses %Bags (no per-candidate
#   $t_bag); painters test @Vis before @Blk; %Cg/%Target -> cell-indexed arrays; paint_fr
#   merges boxes into @Vis_fr (is_frozen re-checks a frozen box on the stance).
#   See [[project_solver_throughput_campaign]].
#
# Two fixes were promoted on 2026-07-16, both from the same root cause -- the port from
# the archived v3.0 (an old-solver A/B chain, since removed) had quietly changed how the
# search re-expands itself. Game 1, seed 255: TIMEOUT 233 @ 2149s -> SOLVED 229 @ 677s
# (the archive proved the same optimum in 672s = parity, and this module additionally
# runs is_frozen, which the archive lacked and without which it dies on game 12).
# Game 12, seed 613: 503-and-stuck -> 481.
#
# v1.1 -- restart policy. The archive restarts only when the frontier is both large and
#   still mostly unexplored ($RESTART_MIN_OPEN/$RESTART_RATIO, want_restart()); that
#   threshold had not been carried over, so this module restarted on EVERY improvement.
#   A restart is a COMPACTION of an overgrown frontier, not a rebuild of it.
# v1.2 -- bublej() is a pure relaxation again. It used to relax, DISCOVER unseen nodes
#   and push them, so wherever %Seen was sparse (right after a restart wipes it) every
#   node in the %Tahy cache looked unseen and ONE call became a DFS over the whole cache
#   -- outside hledej(), hence uncounted, unbounded by $LIMIT and uninterruptible.
#   Measured on game 12: a single cascade ran 735s while the open list went 70k -> 391k.
#   Now discovery and enqueueing belong to hledej(), and the queued bit/heap_add()
#   provide the SPFA re-push. Since 3.0 that regime is the FIFO mode: see bublej_fifo(),
#   hledej_fifo() and want_restart() for the details that matter.
# v1.6 -- queue membership as the LOW BIT of the %Seen value instead of a %inHeap hash
#   of its own (2026-08-31). See the note at the declaration; measured -57 MB of peak
#   RSS on game 37654 at 240 s, with every search counter identical to the unit.
# v1.8 -- THE RE-QUEUE AFTER A RELAXATION IS ASKED WHETHER IT IS WORTH ANYTHING
#   (2026-08-31, on the USER's reading of what the heap IS).
#
#   THE ARGUMENT FIRST, because it is not about wasted work. Running the heap dry is
#   the ONLY way this search ever ends in a proof: hledej() returns 'SOLVED' precisely
#   when `while ($N_Open)` falls through, and that emptiness is what makes the current
#   $Bestbet provably optimal. So a node queued for nothing is not merely a cheap pop
#   later -- it is one more thing that must be drained before the solver is allowed to
#   say SOLVED at all. Filling the heap with positions that reveal themselves as
#   pointless the moment they are popped works directly against the only exit there is.
#   On game 42929 the queue had to pass 3 283 425 pops over 1 107 368 distinct positions
#   before it could close; now it passes 1 107 374.
#
#   WHAT CHANGED. bublej() used to put EVERY node it relaxed back on the heap. What a
#   pop can do is discover an unseen child or relax a seen one -- and the cascade has
#   just done every relaxation there was, so the only reason left is a child not in
#   %Seen. bublej() now returns that verdict (free: the loop already tests it) and both
#   call sites queue only on it; a terminal is never queued, as restart() has always
#   had it. Measured on all seven games in the database with a proven optimum: of what
#   the line used to queue, 98.2 % was a node whose move list the cascade had settled --
#   2 182 of 985 380 were the never-expanded case the re-queue exists for. Expansions
#   of an already-expanded node: 2 101 492 -> 15 500 (-99.3 %) while FIRST expansions
#   held at 2 297 444 -> 2 301 088, i.e. nothing went unexplored. Per game, positions
#   expanded -1.6 % (37654, still discovering) to -66 % (42929), frontier peak -3 % to
#   -86 %, paired wall time -10 % (41519) and -28 % (27701). Every game returned its
#   known optimum with the queue EMPTY, and on the three that never restarted both arms
#   ended with an identical %Seen -- same positions, same costs. A gate for the property
#   itself ("at termination no explored edge is still relaxable") was written and
#   abandoned: it cannot fail, not even with the fault injected -- CLAUDE.md, "Solver
#   versioning", says why.
# v1.7 -- ONE ENV PER GAME (2026-08-31, USER). Bad + Tahy move out of the shared env
#   into <berk_root>/Sokoban/G<id>, which Solver, SolverPush and SolverBerk open
#   too, so the whole optimal line accumulates into one place and sb_adopt (a one-way
#   MOVE, after which this module could no longer see its own cache) is gone. And
#   $PERSIST becomes three-state: 1/0 force it, undef decides by $LIMIT against
#   $PERSIST_FROM, so a short run on a small game creates no files at all.
use v5.42;
use feature 'keyword_all', 'keyword_any', 'declared_refs', 'refaliasing';
use experimental ('keyword_any', 'keyword_all', 'refaliasing', 'declared_refs');
use warnings FATAL => ('uninitialized');
no warnings('once', 'recursion');
use Carp           ('confess');
use Time::HiRes    ('tv_interval', 'gettimeofday');
use Storable       ('thaw', 'dclone');
use List::Util     ('max');
use Compress::Zlib;
use Term::ANSIColor;
use Games::Sokoban::Solver::Console ('backline', 'backlinen', 'podil');
use Games::Sokoban::Solver::Data    ();
use Games::Sokoban::Solver::Memory  ();

# $MAX_GB (GiB, 0 or undef = off): the memory safety net. Compared against TOTAL system
# RAM in use -- Memory::used_gb() is one kernel call, ~2 us -- because an OOM is about
# the whole machine, not this process. It aborts the search as MEMCAP, which is returned
# as TIMEOUT (the best path found stands, unproven) and named in $LastStatus.
our ($LIMIT, $MAX_GB);

# What stopped the last solve() when it returned TIMEOUT: 'TIMEOUT' (the clock), 'MEMCAP'
# (the memory net) or 'IGNORE' (the race) -- the return value cannot say, as the Sokoban
# project's stats row used to.
our $LastStatus = '';

# A callback for every improvement, called with ($path, $seconds_into_the_run) the moment
# the record is bettered, so a caller can keep or show it before the solve ends; undef =
# nothing is called. @Track keeps the same, one record per improvement.
our $ON_IMPROVED;

# THE RACE SIGNAL: a driver that runs the three modes of one game AT ONCE, one per thread,
# sets $RACE_FLAG (one threads::shared hash, gameid -> true) once per worker and
# $RACE_GID per game -- the same two names Firstbet carries -- and a loser notices at its
# 4096-pop checkpoint and leaves with 'IGNORE': not a result about the game (the record it
# holds is still returned). Both stay undef outside a race.
#
# $QUIET, in three levels (the same in every engine that has it):
#   0  everything;
#   1  no TRANSIENT progress lines (info()'s backline); the durable ones stay --
#      START, the band's lines, the coloured end line in barva();
#   2  none of those either (a threaded driver: the threads would interleave them).
# The red OUT OF MEMORY line is not muted at any level: it says why a run ended.
our ($RACE_FLAG, $RACE_GID);
our $QUIET = 0;
sub race_lost() { $RACE_FLAG && $RACE_GID && $RACE_FLAG->{$RACE_GID} }

# The trajectory: one record per improvement -- seq, cas (seconds into the run), sollen,
# pushes, counter, n_open, nstart, path. Filled by solve(); read it after solve() returns.
# Instrumentation only: nothing here influences the search.
our @Track;

my (
    %Game,   @Goal,    @Target,   %Cm,   %Cmk,      @Cg,       %Pis,
    %InvPis, @Baggage, %Priority, @Maze, $Has_hole, $Has_wall, $Has_corridor,
    $Hole,   $Wall,    $Corridor, $Blok, $BlokVec,  $W
   );
my ($Nbox, %Sols, %SolReal, %Bags, $corridors, $holes, $pu);
my (@Bucket, $CurMin, %Seen, %Parent, %Tahy, $Bestbet, $Bestlen, @Buf, $N_Open, $O_Open, $MaxOpen);

# FIFO's open list, and its "a betterment landed" flag. Only that mode uses them; DIAL and
# ASTAR leave both untouched, as FIFO leaves @Bucket and $CurMin untouched.
my (@Heap, $Improved);

# ASTAR: cell -> shortest push distance from that cell to ANY goal, built once per game in
# initvars and only when the mode asks for it. A cell with no row in `steps`
# (Parser::route walks keys %Cmk, so a cell a box cannot be pushed out of has none --
# game 1's goal at 131 is one) gets 0: an understatement, which keeps the estimate
# admissible, and measured over 1.13 M positions such a cell off a goal never occurred,
# the deadlock battery having taken them all. A GOAL gets 0 for the same reason it must:
# without `$MinSteps[$_] = 0 foreach @Goal` the estimate charges a box that has already
# arrived, stops being a lower bound, and 37928 comes back 78 against a proven 77.
my (@MinSteps);

# What the LAST PRINTED info() line said, so the next one can decide whether that line is
# worth keeping (USER 2026-09-01). $O_Open was always this; the record and the dial's
# level joined it when the separate "FOUND:" line went away -- see info().
my ($O_Bestbet, $O_CurMin);

# The level the dial last entered; hledej() compares $CurMin against it once per pop and
# notes the time when the dial has moved on. See record_level().
my ($Level_at);

# THE OVERRUN (v3.3): the entry time of every level entered, and the last verdict of
# overrun_ok() with the level it was made at -- re-asked only when the dial has moved on.
my (@LevelCas, $Overrun_level, $Overrun_ok);

# DIAL: the open list is @Bucket -- one plain array of positions per integer
# cost, indexed by that cost, walked upward by $CurMin. The v1.6 bit in %Seen is
# repurposed:
#
#     $Seen{$p} = $cost * 2 + $expanded      $cost = $Seen{$p} >> 1
#
# EXPANDED, not queued: with cheapest-first order a popped position's cost is
# final, so the bit records "this one is done, any further copy in a higher
# bucket is stale". A relaxation of a still-waiting node lowers its %Seen cost
# and inserts a SECOND copy into the lower bucket; the old copy is skipped when
# its bucket comes up (its bit is set by then, because the lower copy always
# pops first -- inserts land strictly above $CurMin, so the cheaper copy cannot
# be behind the dearer one). Duplicates cost bucket slots, not correctness.
#
# READ THE LOW BIT AGAINST $MODE. It means EXPANDED in DIAL and ASTAR and QUEUED in
# FIFO -- one variable, two meanings, and the mode decides which. That is safe because
# exactly one search loop ever runs, but it is precisely the kind of thing that gets
# miscopied, so every place that touches the bit says which meaning it is using. In FIFO
# the bit is set by heap_add and CLEARED at the pop (v1.6's queued bit); in the bucket
# modes it is set at the expansion and cleared only by bublej's re-opening under ASTAR.
my (%MemBad);                           # the deadlock cache of one solve
my ($bc,         $counter, $timer, $Probed, $Cas, $Gameid);

# The frontier's effective branching factor, reported by info() as $Pushed/$Expanded --
# how many children of an average parent actually reach a bucket (USER 2026-08-31).
# Neither existing counter answers it: $bc counts CANDIDATES, before the bound and the
# deadlock battery, and $counter counts every pop, including stale duplicates dropped
# without being expanded. So $Expanded counts positions whose child loop really ran, and
# $Pushed counts what bucket_add() actually queued -- restart()'s seed threading puts
# back the value it found, since path nodes are not children of anything.
#
# Read it against 1: above 1 the frontier grows, below 1 it drains. On a 20-box game the
# theoretical ceiling is 4 x 20 = 80, and the measured value is far under it --
# reachability, the bound and the battery take most of it before bucket_add() is called.
my ($Pushed, $Expanded);
my ($PaintId,    @Blk,     @Vis,   @Dist,     $Poradi);
my ($PaintId_fr, @Vis_fr,  @Buf_fr);    # dedicated state for paint_fr/is_frozen (boxes merged into @Vis_fr)
my ($PocketMin,  %FrozenMemo);          # is_frozen memoization: paint()'s pocket-min (canonical region id) + verdict cache

# The corridor and hole pattern tables, read once per process from the distribution's
# data directory.
$corridors = Games::Sokoban::Solver::Data::load('corridor_pattern.stor');
$holes     = Games::Sokoban::Solver::Data::load('hole_pattern.stor');
$LIMIT     = 30;

# THE PORTFOLIO (USER 2026-09-02). Three search regimes in ONE file, exactly as
# Firstbet.pm holds ten modes in one file. The wave of three arms over 200 tier-1 games
# ended in a draw -- FIFO proved 160, ASTAR 157, DIAL 156, and each of them proved games
# the other two did not -- so there is no winner to promote, and the answer is the USER's:
# "kazda hra je samostatny ukol". $MODE names the regime and solve() resolves it ONCE
# into the integer flags below, so the branch sits at the level of whole subs and never
# inside the child loop (USER's rule: op count beats structure).
#
#   'DIAL'   the cost-ordered bucket queue promoted as v2.0. $CurMin walks upward and
#            never returns, a popped cost is FINAL, and the proof lands the moment
#            $CurMin reaches $Bestlen. The cheapest mode per node, and the only one
#            whose solve_level `width` is a level's COMPLETE population.
#   'FIFO'   the 1.8 regime: a FIFO open list, SPFA relaxation with the re-queue verdict,
#            and restart() as a frontier COMPACTION around each new record. It can report
#            no lower bound and its improvements arrive as a staircase -- which is exactly
#            why it is the MINER: the compaction re-threads the best path and the breadth
#            around it is an accidental local search. The only mode that fills nstart.
#   'ASTAR'  DIAL ordered by f = g + h with an ADMISSIBLE h (@MinSteps). Still a proof,
#            and $CurMin -- now the smallest f on the open list -- is a TIGHTER lower
#            bound than g was. What does NOT survive is FINALITY: a popped f is final
#            only while the estimate is consistent, and ours is not, so an expanded node
#            must be RE-OPENED when a cheaper route reaches it (see the guards in bublej
#            and at its call site). Optimality rests on the re-opening, not on finality.
#
# WEIGHTED A* (f = g + w*h, w > 1) IS NOT A MODE and will not become one. It can never
# prove anything -- above w = 1 the frontier-exhausted exit says only "this weighted
# frontier is spent" -- and as a MINER it lost to FIFO on the one game where mining is
# all there is (37654: 845 moves against 465). The ambition of this line is the PROOF
# (memory feedback_optimal_ambition_proof), so a regime that cannot produce one and does
# not mine better than a mode we already have has no role. Same for the assignment form
# of the estimate: measured 45.5 % against the sum's 38.8 % as a cut, which does not pay
# for a Hungarian per node (memory project_munkres_lower_bound_refuted). Both live in the
# slot as experiments, not here.
#
# The estimate is the sum over boxes of that box's shortest PUSH distance to any goal
# (@MinSteps, built once per game from the blob's `steps` table). Two properties earn it
# its place: it is a plain sum, so no assignment problem is solved per node (Munkres is
# not decomposable and measured only a few points better -- memory
# project_munkres_lower_bound_refuted), and `steps` never overshoots, unlike `distance`,
# whose walking cannot be summed across boxes (one player circuit serves several pushes).
#
# WHAT ELSE THE f-ORDER CHANGES, all of it handled in code and none of it obvious:
#   * the bucket index stops being the cost, so solve_level's `width` is no longer a
#     level's complete population -- under the f-order a child can land in the bucket
#     being emptied, which the cost order made impossible;
#   * an insert whose f falls below $CurMin LOWERS THE DIAL ($CurMin = $f) instead of
#     being clamped into the current bucket. The clamp was the pilot's shape and it cost
#     the exit its status as a proof: a node clamped into bucket b has a TRUE f below b,
#     so "$CurMin >= $Bestlen" could hold while a node of f < $Bestlen still waited, and
#     a better solution could run through it. Nothing went wrong in the pilot's 157
#     proofs -- and that is precisely the evidence we refused to ship on at v1.8, where
#     the version whose completeness could be ARGUED won over the one that had merely
#     survived a sample. Letting $CurMin descend costs one compare per insert, and the
#     advance loop rescans upward from wherever the dial now stands, so nothing else has
#     to change. Measured after the change on 29 pilot games: 23 of 23 identical to the
#     recorded arm, and on the proved ones the expansion counts are IDENTICAL -- the
#     clamp had never fired there, so the correction cost nothing at all;
#   * `trim_tail` stays in force: h is admissible, so f >= $Bestlen does imply that no
#     solution through that node can beat the record;
#
# AND ONE THING THAT IS NOT OPTIONAL: THE CASCADE MUST RUN. A relaxation rewires %Parent,
# so the saving reaches the reconstructed path by itself -- but $Bestlen, the trajectory
# and the bestbet write learn of it only through bublej's report. A first version of the
# re-opening bypassed the cascade and 37654 at w=2 came back with a 845-move path against
# its 913 seed while reporting nimp=0, writing nothing, and pruning against 913 for the
# whole 1800 s. An unannounced improvement is worse than none: it is not persisted, and
# the search does not even use it.
#
# THE ESTIMATE'S KNOWN WEAKNESS: g counts PLAYER MOVES and h counts PUSHES. A push needs
# at least one move, so h is admissible -- but structurally slack, which is why the same
# bound cut only 2-3 % of expansions as a PRUNE on 37654. As an ORDER it is worth far
# more than that slackness suggested: on the nine proven games it kept every optimum and
# cut expansions by 30 % overall, and on a ladder of six OPEN boards -- the shape that
# hurts a cost-ordered search, many boxes on a nearly empty floor -- it PROVED two games
# the dial could not prove in 900 s, and was 3.3-3.9x faster on the two both proved.
our $MODE = 'DIAL';

# $MODE resolved, ONCE, in solve(). Everything downstream branches on these two integers
# and never on the string: $Fifo selects the whole 1.8 half of the file (heap_add,
# bublej_fifo, hledej_fifo, restart()'s compaction half and solve()'s restart loop),
# $H_on turns the f-order on inside the bucket half.
# DIAL = (0,0), ASTAR = (0,1), FIFO = (1,0).
#
# They are initialised to DIAL rather than left undef because solve() is not the only
# entry point in practice: ai/t_h_admissible.pl calls initvars() and cesta_na_pozice()
# directly, and a gate that reaches in like that must find the module in a defined state,
# not one that depends on whether a solve happened to run first.
my ($Fifo, $H_on) = (0, 0);

# FIFO's own contract, carried over verbatim from the 1.8 baseline (now SolverOld.pm,
# kept permanently as this mode's oracle). $nStart counts restart() calls and is the only
# writer of solve_stats.nstart -- the bucket modes leave it 0, having no restarts.
#
# The point of a restart is to COMPACT an overgrown frontier, not to rebuild it: only
# when the open list is both large ($RESTART_MIN_OPEN) and still mostly unexplored
# ($RESTART_RATIO of its peak) is throwing it away and re-seeding from the best path
# worth more than it costs. Below that, keeping the open list and simply continuing with
# the tightened $Bestlen is strictly cheaper -- the bound prunes it anyway.
# ($RESTART_MIN_OPEN = 0 means NO compaction restarts at all -- want_restart() is false --
# not "restart on every improvement", as an older comment here claimed.)
our $nStart           = 0;
our $RESTART_MIN_OPEN = 100_000;
our $RESTART_RATIO    = 0.5;

# THE BAND (v3.1, USER 2026-09-05/06; v3.2 2026-09-07; see the header). FIFO only -- the
# MINER, the mode that looks for a shorter path near the one we have.
#
# WHAT IT IS. The record's TRACK is the sequence of box configurations its solution
# passes through, one per push. restart() builds it from the record it threads, each
# configuration a bit string over the cells. A position's DISTANCE from the track is how
# many of its boxes stand off the nearest configuration on it. hledej_fifo() queues a
# newly found (unseen) child only if that distance is at most $Band_cur; a farther child
# is dropped and counted. $BAND is the width asked for (default 2, 0 = no band). The
# USER's old Solver seeded the path AND the siblings of the winning moves; that is band
# width 1 at the start, and this is the same idea for the whole wave.
#
# WHY. Measured before it was built: 340 of 344 FIFO improvements on four games lay within
# two boxes of the previous record's track, while the unrestricted wave spent 74-90 % of
# its positions three or more boxes away.
#
# IT FOLLOWS THE RECORD: rebuilt after every improvement (with the heap kept), not only at
# a restart -- under a band the frontier stays small and want_restart() hardly ever fires.
#
# SOUNDNESS. The heap running dry is FIFO's only proof, and it is one only if nothing was
# dropped. So when the heap runs dry under a band that dropped children, solve() drops the
# band ($Band_cur = 0) and restarts around the same record UNRESTRICTED; only a dry heap
# with nothing dropped is a proof. An improvement found unrestricted brings the band back
# at $BAND around the new record, so the regime alternates: polish within the band until
# it is dry, then hunt anywhere, then polish again. (3.1 widened the band one box at a
# time instead -- the ladder -- which could pay only for improvements 3+ boxes off the
# track, 4 of 344; the jump proves sooner on every one of 22 paired games.) $BAND_DRY is
# called at that exact moment, for a measuring script. The bucket modes never see the
# band: their order IS their proof and a band would break it silently.
#
# The test: every configuration admitted is remembered in %BandMemo with its distance and
# its WITNESS, the index of the track configuration that admitted it (pack 'Cn' -- the
# witness is a 16-bit index: a track has one configuration per push of the record, and
# 2 398 firstbet records carry 255 pushes or more, up to 2 259; a 'C' there wrapped
# modulo 256 with a warning per memo write, USER 2026-09-06). A child
# differs from its parent by one box, so against the parent's witness it is at most one
# box farther -- one string AND and one popcount decide the common case. A child that took
# a box OFF the witness at the band's edge scans all track configurations; an OUT verdict
# is memoized too (as the empty string), up to $BAND_MEMO_MAX entries, because far
# configurations are regenerated from many parents on small boards and hardly ever on
# 20-box ones, where the memo only grew. Measured cost on a fast game (17850, 11 800
# pops/s unrestricted): ~2 600 pops/s -- and the A/B says the band wins in wall time
# despite it, because each pop lands near the record.
our $BAND          = 2;            # boxes off the record's track a queued child may have; 0 = off (the control arm)
our $BAND_MEMO_MAX = 4_000_000;    # cap on memoized OUT verdicts
my ($Band_cur, $Band_dropped, $Band_total, $Cw, $Band_zero, %BandMemo, @BandCfg);

# The deadlock cache (%MemBad) and the move cache (%Tahy) of one solve, in RAM. In the
# Sokoban project these subs were a seam over BerkeleyDB -- the two caches could live in
# the game's own database and survive from one run to the next, which is what let a
# proof take days -- and that twin is Games::Sokoban::Solver::Optimal::Berk; here the
# seam is the RAM half of the same subs, so the search text above and below is the
# project's own.
sub bad_init ($g) { %MemBad = (); %Tahy = () }
sub bad_close ($s) { %MemBad = (); %Tahy = () }
sub setbad ($p) { $MemBad{$p} = 1 }
sub isbad  ($p) { exists $MemBad{$p} }

# Uniform "arrayref or undef", so callers can `my $c = tahy_get(...)`.
sub tahy_get ($p)     { $Tahy{$p} }
sub tahy_set ($p, $k) { $Tahy{$p} = $k }
sub tahy_del ($p)     { delete $Tahy{$p} }

sub clearvars() {
    ($Band_cur, $Band_dropped, $Band_total) = (0, 0, 0);
    %BandMemo          = ();
    @BandCfg           = ();
    $Bestbet           = undef;
    $Bestlen           = undef;
    $bc                = undef;
    $counter           = undef;
    $timer             = undef;
    $Probed            = 0;
    $Pushed            = undef;
    $Expanded          = undef;
    $Cas               = undef;
    $Gameid            = undef;
    $Blok              = undef;
    $BlokVec           = undef;
    $Corridor          = undef;
    $Has_corridor      = undef;
    $Has_hole          = undef;
    $Has_wall          = undef;
    $Hole              = undef;
    $Nbox              = undef;
    $W                 = undef;
    $Wall              = undef;
    $PaintId           = undef;
    $PaintId_fr        = undef;
    $PocketMin         = undef;
    %FrozenMemo        = ();
    $Poradi            = undef;
    @Vis               = ();
    @Blk               = ();
    @Dist              = ();
    @Vis_fr            = ();
    @Bucket            = ();
    @Heap              = ();
    $Improved          = 0;
    $CurMin            = 0;
    @MinSteps          = ();
    %Bags              = ();
    @Cg                = ();
    %Cm                = ();
    %Cmk               = ();
    %Game              = ();
    %Priority          = ();
    %Parent            = ();
    %Pis               = ();
    %InvPis            = ();
    %Seen              = ();
    %Sols              = ();
    %Tahy              = ();
    @Target            = ();
    @Baggage           = ();
    @Buf               = ();
    @Buf_fr            = ();
    @Goal              = ();
    @Maze              = ();
} ## end sub clearvars

sub initvars ($gameid, $gm) {
    clearvars();
    bad_init($gameid);
    %Game = %{ thaw(uncompress($gm)); };
    my $maze = $Game{'code'};
    $maze =~ tr/,//d;
    $maze =~ tr/45678/00233/;
    @Maze         = split(//a, $maze, 0);
    $Game{'maze'} = &dclone(\@Maze);
    @Goal         = @{ $Game{'goal'}; };
    @Target       = ();
    $Target[$_]   = 1 foreach @Goal;                                  # cell-indexed (Firstbet v2.4 #1)
    %Cm           = %{ $Game{'cm'};  };
    %Cmk          = %{ $Game{'cmk'}; };
    @Cg           = ();
    $Cg[$_]       = $Game{'cg'}{$_} foreach keys %{ $Game{'cg'} };    # cell-indexed neighbour lists
    @Baggage      = @{ $Game{'baggage'}; };
    $W            = $Game{'w'};

    # Parser already chose the position pack template ('C*' or 'n*') and packed
    # %Sols with it -- reuse it for every pack/unpack of a (man,@baggage) tuple.
    $pu       = $Game{'vzp'};
    $Cw       = ($pu =~ /^n/) ? 2 : 1;                                     # bytes per cell in a packed position (band keys)
    $Band_zero = "\0" x int(($Game{'w'} * $Game{'h'} + 7) / 8);            # one bit per cell of the board
    %Pis      = (-1, 'l', 1, 'r', $W, 'd', -$W, 'u');
    %InvPis   = reverse %Pis;
    $Nbox     = scalar @Baggage;
    %Priority = %{ $Game{'order'}; };
    ($Has_hole, $Has_wall, $Has_corridor) = @Game{ 'has_hole', 'has_wall', 'has_corridor' };
    ($Blok, $BlokVec)                     = _blok_both($Game{'blok'});    # arrays (cold callers) + vecs (tahy hot path)

    # ASTAR: the per-cell push-distance floor, built only when the mode asks for it.
    # 'Inf' marks an unreachable goal in the blob and must not enter the minimum.
    @MinSteps = ();
    if ($H_on) {
        my $steps = $Game{'steps'};
        for my $cell (keys %{$steps}) {
            my $best;
            for my $g (values %{ $steps->{$cell} }) {
                next if $g eq 'Inf';
                $best = $g if !defined $best or $g < $best;
            }
            $MinSteps[$cell] = $best // 0;
        }

        # A BOX ALREADY HOME NEEDS NO PUSH -- and the table will not say so: `steps` holds
        # no row from a cell to ITSELF, so the minimum over a goal cell's row is the
        # distance to the NEAREST OTHER goal, at least 1. Measured, not assumed: with this
        # line missing the estimate overshot the remaining pushes at 9 positions of
        # 37928's proven optimum, 19 of 41519's, and A* answered 78 against a known 77.
        $MinSteps[$_] = 0 foreach @Goal;
    }
    $Hole     = &dclone($Game{'hole'})     if $Has_hole;
    $Wall     = &dclone($Game{'walls'})    if $Has_wall;
    $Corridor = &dclone($Game{'corridor'}) if $Has_corridor;
    @Bucket   = ();
    $CurMin   = 0;
    %Seen     = ();
    %Parent   = ();
    %Tahy     = ();
    $Bestbet  = undef;
    $Bestlen  = 'Inf';
    %Sols     = %{ $Game{'sols'} };

    # The optimal Solver stops ONLY at a REAL solution: a tailless sols entry (all
    # boxes on the true goals). A checkpoint box-on-P entry carries a move-string
    # tail -- those are NOT terminals here; the standard search pushes the box off P
    # to its goal like any other move and reaches a tailless entry. (A pre-Part-2
    # blob stores the scalar 1, which is tailless -> every entry is a real terminal.)
    %SolReal     = ();
    $SolReal{$_} = 1 foreach grep {$Sols{$_} !~ /[A-Za-z]/} keys %Sols;
    $PaintId     = 0;
    $PaintId_fr  = 0;
    $Poradi      = 0;
    @Blk         = (0) x scalar @Maze;
    @Vis         = (0) x scalar @Maze;
    @Dist        = (0) x scalar @Maze;
    @Vis_fr      = (0) x scalar @Maze;
} ## end sub initvars

# blok loader (dual-read REMOVED 2026-08-06, memory project_blok_vec_bench):
# the blob carries TRIMMED BIT VECTORS (new Parser; tools/update_block.pl
# converted the whole DB). Build both runtime forms once at load: vecs for
# is_bad's hot tahy() gear, arrays for the cold callers that do not maintain
# a box vector. An array pattern now dies LOUDLY -- it can only mean a
# pre-conversion blob (an old backup), which would otherwise compute garbage
# silently.
sub _blok_both ($src) {
    my (%arr, %vec);
    foreach my $bx (keys %{ $src // {} }) {
        my $row = $src->{$bx};
        foreach my $t (keys %$row) {
            my (@as, @vs);
            foreach my $p (@{ $row->{$t} }) {
                die "array blok pattern (pre-2026-08-06 blob? run tools/update_block.pl)" if ref $p;
                push @as, [grep {vec($p, $_, 1)} 0 .. 8 * length($p) - 1];
                push @vs, $p;
            }
            $arr{$bx}{$t} = \@as;
            $vec{$bx}{$t} = \@vs;
        }
    }
    return (\%arr, \%vec);
} ## end sub _blok_both

sub paint($man, @baggage) {
    ++$PaintId;
    $Blk[$_]    = $PaintId for @baggage;
    $Vis[$man]  = $PaintId;
    $Dist[$man] = 1;
    $Buf[0]     = $man;
    my $bt   = 1;
    my $pmin = $man;    # canonical id of man's reachable region -> is_frozen memo key (free during the flood)
    for (my $bh = 0; $bh < $bt; ++$bh) {
        my $x = $Buf[$bh];
        my $d = $Dist[$x] + 1;
        foreach my $t (@{ $Cg[$x] }) {
            next
                if $Vis[$t] == $PaintId
                || $Blk[$t] == $PaintId;    # @Vis first: already-visited is the common case (Firstbet v2.4 #2)
            $Vis[$t]    = $PaintId;
            $Dist[$t]   = $d;
            $Buf[$bt++] = $t;
            $pmin       = $t if $t < $pmin;
        }
    }
    $PocketMin = $pmin;
} ## end sub paint

# Reachability-only painter for is_frozen() / goal-corral check, with its own
# globals so it never disturbs @Vis/@Blk/$PaintId used by paint()/tahy().
# No distance tracking needed -- callers only check reachability.
sub paint_fr($man, @baggage) {
    ++$PaintId_fr;
    $Vis_fr[$_]   = $PaintId_fr for @baggage;    # boxes as Vis-walls: the flood skips them and the
    $Vis_fr[$man] = $PaintId_fr;                 # inner test is one compare (Firstbet v2.5 merge)
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
# ('', @frozen) if all frozen boxes sit on goals (caller should still check
# whether the frozen wall encloses an open goal -- goal-corral);
# ('', ()) if nothing stays frozen.
sub is_frozen ($man, @nomove) {

    # Memoize the branch 0/1 verdict on (pocket-min, sorted nomove). $PocketMin (from
    # paint()'s last flood in tahy) canonically ids the man's reachable region: a cell
    # reachable under all-boxes-walls is reachable under frozen-only-walls too, so
    # (pocket-min, nomove) determines the man's paint_fr component -> the whole verdict.
    # Branch 2 (all frozen on goals) is NOT cached: the caller's goal-corral check needs
    # a FRESH @Vis_fr, so it must re-flood -- fall through and recompute.
    my $key = $PocketMin . '|' . join(',', sort {$a <=> $b} @nomove);
    if (defined(my $v = $FrozenMemo{$key})) {
        return ('frozen', ()) if $v == 1;
        return ('',       ()) if $v == 0;
    }
    my %frozen = map(($_, 1), @nomove);
    while (1) {
        my @still_frozen;
        paint_fr($man, keys %frozen);
        foreach my $bx (keys %frozen) {
            my $movable = 0;
            foreach my $t (@{ $Cmk{$bx} }) {
                next if exists $frozen{$t};
                my $stance = $Cm{$bx}{$t};
                next if exists $frozen{$stance};    # merge: a frozen box on the stance blocks it (was @Blk_fr)
                next unless $Vis_fr[$stance] == $PaintId_fr;
                $movable = 1;
                last;
            }
            push @still_frozen, $bx unless $movable;
        }
        last if @still_frozen == scalar keys %frozen;
        %frozen = map(($_, 1), @still_frozen);
    } ## end while (1)
    unless (%frozen) {$FrozenMemo{$key} = 0; return ('', ())}
    for (keys %frozen) {
        unless ($Target[$_]) {$FrozenMemo{$key} = 1; return ('frozen', ())}
    }
    return ('', keys %frozen);    # branch 2: on-goal, not cached (goal-corral needs @Vis_fr)
} ## end sub is_frozen

sub is_bad ($bx, $t, $t_bag, $vb = undef) {

    # blok check, two gears (synced with Firstbet v2.10): tahy() maintains the
    # child box BIT VECTOR $vb and pays one string AND + eq per pattern
    # (':5.42' enables 'bitwise', so string AND is the DOTTED &. operator; a
    # trimmed pattern vec is safe on both sides of a length mismatch because
    # &. truncates to the shorter operand). Without $vb: the old array scan.
    if (defined $vb) {
        my $bvs = $BlokVec->{$bx} && $BlokVec->{$bx}{$t};
        if ($bvs) {
            foreach my $pv (@$bvs) {
                return 1 if ($vb &. $pv) eq $pv;
            }
        }
    }
    else {
        my $blok = $Blok->{$bx} && $Blok->{$bx}{$t};
        if ($blok) {
            foreach my $bl (@$blok) {
                return 1 if CORE::all {exists $t_bag->{$_};} @$bl;
            }
        }
    }
    if ($Has_wall) {
        if (defined(my $wall = $Wall->{$t})) {
            foreach my $w (@$wall) {
                my $n = 0;
                foreach my $s (@{ $w->[1] }) {
                    ++$n if exists $t_bag->{$s};
                }
                return 1 if $n > $w->[0];
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
                return 1 if $n > 1;
            }
            else {
                $Maze[$_] =~ tr/03/47/ foreach keys %$t_bag;
                my $str = join('', @Maze[@{ $cor->[0]; }]);
                $Maze[$_] =~ tr/47/03/ foreach keys %$t_bag;
                confess("is_bad: a corridor shape the table does not know: '$cor->[2]' ($cor->[1], cells @{ $cor->[0] })")
                    unless exists $corridors->{ $cor->[2] };
                return 1 unless ($corridors->{ $cor->[2] }{ $cor->[1] } // {})->{$str};
            }
        } ## end if (defined(my $cor = ...))
    } ## end if ($Has_corridor)
    if ($Has_hole) {
        if (defined(my $hole = $Hole->{$bx} && $Hole->{$bx}{$t})) {
            $Maze[$_] =~ tr/03/47/ foreach keys %$t_bag;
            my $str = join('', @Maze[@{ $hole->[0]; }]);
            $Maze[$_] =~ tr/47/03/ foreach keys %$t_bag;
            die "UNKONWN Hole pattern $$hole[1]" unless exists $holes->{ $hole->[1] };
            return 1                             unless $holes->{ $hole->[1] }{$str};
        }
    }
    return '';
} ## end sub is_bad

# Marks $pozice bad and propagates that knowledge both ways through the
# already-cached search tree, instead of leaving it as an isolated fact:
#   - downward: if $pozice itself was already expanded (has a %Tahy entry),
#     every one of its cached children is equally unreachable/pointless --
#     nothing reachable from a deadlock can ever be used -- so mark them bad
#     too (recursively, since some of THEM may have been expanded as well).
#   - upward: $pozice was one of $Parent{$pozice}'s cached candidate moves.
#     Remove it from that parent's %Tahy entry. If that empties the parent's
#     move list, the parent has no surviving move left either -- it's bad
#     too, discovered only now, possibly many moves after it was first
#     proposed as a candidate.
sub set_bad ($pozice) {
    return if isbad($pozice);
    setbad $pozice;
    if (my $th = tahy_get($pozice)) {
        foreach my ($child, $step)(@$th) {
            next if isbad($child);
            set_bad($child);
        }
    }
    my $parent = $Parent{$pozice};
    my $th;
    if (defined $parent && length $parent && ($th = tahy_get($parent))) {
        my @kept;
        for (my $i = 0; $i < @$th; $i += 2) {
            push @kept, $th->[$i], $th->[$i + 1] unless $th->[$i] eq $pozice;
        }
        if (@kept < @$th) {

            # Persist the trimmed move list back (a fresh put under Berkeley; an
            # in-place replacement under RAM). Both backings see the change.
            tahy_set($parent, \@kept);
            set_bad($parent) unless @kept;
        }
    }
} ## end sub set_bad

sub tahy ($pozice) {
    if (my $cached = tahy_get($pozice)) {
        return @$cached;
    }
    my ($man, @baggage) = unpack($pu, $pozice);
    my ($step, $value, $s, $child, @tahy, @nomove);
    %Bags = map(($_, 1), @baggage);

    # $vb = the box set as a bit vector, mutated in LOCKSTEP with %Bags below,
    # so is_bad's hot blok test is one string AND per pattern (synced with
    # Firstbet v2.10). Built once per position, amortized over all candidates.
    my $vb = '';
    vec($vb, $_, 1) = 1 foreach @baggage;
    paint($man, @baggage);
    @tahy = ();
    foreach my $bx (@baggage) {
        my $movable = 0;

        # Reuse %Bags as the child box-set instead of building a fresh $t_bag hash per
        # candidate: drop the pushed box now, add the target cell just around is_bad(), and
        # restore both. `exists $Bags{$t}` stays correct (t is never $bx), and %Bags is fully
        # restored after the outer loop for the goal-corral `grep !exists $Bags`. (Firstbet
        # v2.4 #4.)
        delete $Bags{$bx};
        vec($vb, $bx, 1) = 0;
        foreach my $t (@{ $Cmk{$bx}; }) {
            next if exists $Bags{$t};
            $s = $Cm{$bx}{$t};
            next unless $Vis[$s] == $PaintId;
            ++$movable;
            $step = $Dist[$s];
            my @nb = grep($_ != $bx, @baggage);
            my $i  = 0;
            ++$i while $i < @nb && $nb[$i] < $t;
            splice(@nb, $i, 0, $t);
            $child = pack($pu, $bx, @nb);

            if (isbad($child)) {
                next;
            }
            $Bags{$t} = 1;
            vec($vb, $t, 1) = 1;
            if ((is_bad($bx, $t, \%Bags, $vb))) {
                set_bad($child);
            }
            else {
                push @tahy, $child, $step;
            }
            delete $Bags{$t};
            vec($vb, $t, 1) = 0;
        } ## end foreach my $t (@{ $Cmk{$bx}...})
        $Bags{$bx} = 1;
        vec($vb, $bx, 1) = 1;
        push @nomove, $bx unless $movable;
    } ## end foreach my $bx (@baggage)

    # Frozen-cluster / goal-corral deadlock check -- can reject this position
    # even when @tahy is non-empty, since a permanently stuck subset of boxes
    # dooms the position regardless of what other boxes can still do.
    if (@nomove) {
        my ($frozen_bad, @frozen_set) = is_frozen($man, @nomove);
        if ($frozen_bad) {
            set_bad($pozice);
            return ();
        }
        if (@frozen_set) {
            my @open = grep {!exists $Bags{$_}} @Goal;
            if (@open) {

                # NO repaint: is_frozen()'s LAST fixed-point paint_fr($man, keys %frozen) IS
                # exactly paint_fr($man, @frozen_set) (the converged %frozen is the returned
                # set, same $man), and nothing repaints @Vis_fr between its return and here --
                # so @Vis_fr/$PaintId_fr are reused directly. (Firstbet v2.6, +12.3%.)
                for my $g (@open) {
                    if ($Vis_fr[$g] != $PaintId_fr) {
                        set_bad($pozice);
                        return ();
                    }
                }
            }
        } ## end if (@frozen_set)
    } ## end if (@nomove)
    if (@tahy) {
        tahy_set($pozice, [@tahy]);
        return @tahy;
    }
    else {
        set_bad($pozice);
        return ();
    }
} ## end sub tahy

sub cesta ($m, $target, $baggage) {
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

sub get_path (@postup) {
    my ($father, $fm, @sb, $sm, @fb, $source, $target, %fh, %sh, $path, $move, $man);
    $father = shift @postup;
    $path   = '';
    foreach my $son (@postup) {
        ($fm, @fb) = unpack($pu, $father);
        ($sm, @sb) = unpack($pu, $son);
        %fh = map(($_, 1), @fb);
        %sh = map(($_, 1), @sb);
        ($source) = grep((!$sh{$_}), @fb);
        confess("SOURCE @fb  |  @sb") unless defined $source;
        ($target) = grep((!$fh{$_}), @sb);
        confess("TARGET @fb  |  @sb") unless defined $target;
        $move = uc $Pis{ $target - $source };
        $man  = $Cm{$source}{$target};
        confess("$source -> $target") unless defined $man;

        if ($fm == $man) {
            $path .= $move;
        }
        else {
            $path .= cesta($fm, $man, \@fb) . $move;
        }
        $father = $son;
    } ## end foreach my $son (@postup)
    return $path;
} ## end sub get_path

# The end-of-search line, coloured by outcome -- the same scheme Firstbet has carried
# since 2026-08-31 (USER 2026-09-02: the optimal line should read the same way). Green
# proved it, yellow spent its whole budget, and RED is everything else, which is the
# point: MEMCAP tore the run out on memory and UNSOLVABLE is a tripwire that says the
# search exhausted a state space no real game exhausts. Neither is a clock running out,
# and until now both looked exactly like one. Goes through backlinen -- this is the
# DURABLE line, the one that must survive in the scrollback.
sub barva ($reason, $ending) {
    state $colour = {'SOLVED', 'bright_green', 'TIMEOUT', 'bright_yellow'};
    backlinen(colored($ending, $colour->{$reason} // 'bright_red')) if $QUIET < 2;
}

# Periodic progress printout, throttled and callable from anywhere in this
# module (not just hledej()'s own loop) -- specifically so a long bublej()
# cascade (measured up to ~1.85M nodes / 9s for one top-level call, see
# project_bublej_cascade_timing) still shows visible progress instead of
# looking hung for the whole time it has hledej() blocked. $Probed gates the
# (non-free, at this call volume) time() check itself to once every 10000
# calls; only once that passes do we check whether 6 real seconds have
# actually elapsed since the last printout. Purely cosmetic -- info() never
# aborts anything; $LIMIT enforcement lives solely in hledej()'s own loop.
sub info() {
    return if ++$Probed % 10000;
    return unless time() - $Cas > 6;
    my $doba = tv_interval($timer);

    # THE TWO LINES WORTH KEEPING (USER 2026-09-01). backline() overwrites its predecessor,
    # which is right for a progress line and wrong for the two moments that carry a fact:
    #   * a newline BEFORE the print leaves the line that still showed the OLD record
    #     standing -- that is what the separate "FOUND: n" say() used to announce, now said
    #     by the line itself, with its clock and counters beside it;
    #   * a newline AFTER it keeps the FIRST line of a new $CurMin, whose bucket count is
    #     the widest that level will ever show (once the dial stands in a bucket, nothing
    #     can be inserted into it -- every insert lands at least one move above).
    print {*STDERR} "\n" if !$QUIET and $Bestlen != $O_Bestbet;
    if ($QUIET) { }    # no progress line: a threaded caller's workers would only interleave them
    elsif ($Fifo) {

        # FIFO has no ordered frontier, so the last two columns have nothing to say: there
        # is no lower bound to print and no bucket to count. Nine columns, as in 1.8.
        backline(
            sprintf '%10d ... %12d %9d %6d %9s %5.2f %12.2f %12.0f %12.0f %8d',
            $Gameid, $counter, $N_Open, $N_Open - $O_Open, podil($N_Open,$MaxOpen,2),
            ($Expanded ? $Pushed / $Expanded : 0),    # children per parent that reach the heap
            $doba,
            $bc / $doba,
            $counter / $doba, $Bestlen
        );
    }
    else {
        backline(
            sprintf '%10d ... %12d %9d %6d %9s %5.2f %12.2f %12.0f %12.0f %8d %5d %9d',
            $Gameid, $counter, $N_Open, $N_Open - $O_Open, podil($N_Open,$MaxOpen,2),
            ($Expanded ? $Pushed / $Expanded : 0),    # children per parent that reach a bucket
            $doba,
            $bc / $doba,
            $counter / $doba, $Bestlen,
            $CurMin,                                  # live lower bound -- nothing shorter than this exists
            scalar @{ $Bucket[$CurMin] // [] }        # how much is still waiting AT that bound
        );
        print {*STDERR} "\n" if $CurMin != $O_CurMin;
    }
    ($O_Open, $O_Bestbet, $O_CurMin) = ($N_Open, $Bestlen, $CurMin);
    $Cas = time();
} ## end sub info

# Insert $p, whose recorded cost is $g, into its bucket. The only place the
# open list grows. No membership test: a duplicate of a relaxed node is allowed
# and skipped at pop time (see the %Seen note above).
sub bucket_add ($p, $g) {
    my $f = $H_on ? $g + odhad($p) : $g;    # ASTAR orders by f, DIAL by g

    # A BUCKET THE DIAL HAS ALREADY LEFT MUST NOT SILENTLY SWALLOW AN ENTRY. In DIAL it
    # cannot receive one: an insert lands at parent cost + step, i.e. at least one above
    # the position being expanded. Under ASTAR it can, because our estimate is admissible
    # but NOT consistent -- `steps` is measured on Parser's pruned push graph while tahy()
    # generates from the search's own, so one push can lower h by more than the move cost
    # -- and then f falls.
    #
    # THE DIAL DESCENDS TO MEET IT (2026-09-02). The pilot CLAMPED such an insert into the
    # bucket being emptied, and that quietly cost the search its proof: a clamped node has
    # a TRUE f below the bucket holding it, so "$CurMin >= $Bestlen" could be reached with
    # a node of f < $Bestlen still waiting. Nothing went wrong in 157 proofs -- and that
    # is exactly the evidence v1.8 refused to ship on. Lowering $CurMin keeps the bucket
    # index equal to f, so both exits are proofs again; the advance loop rescans upward
    # from wherever the dial now stands, and one compare is the whole price.
    $CurMin = $f if $f < $CurMin;
    push @{ $Bucket[$f] //= [] }, $p;
    ++$N_Open;
    ++$Pushed;    # numerator of info()'s children-per-parent
    $MaxOpen = $N_Open if $N_Open > $MaxOpen;
}

# FIFO: queue $p unless it is already queued. The only place @Heap grows, and the only
# place the low bit of %Seen means QUEUED rather than EXPANDED (see the %Seen note).
sub heap_add ($p) {
    return if $Seen{$p} & 1;
    push @Heap, $p;
    $Seen{$p} |= 1;
    ++$N_Open;
    ++$Pushed;    # numerator of info()'s children-per-parent
    $MaxOpen = $N_Open if $N_Open > $MaxOpen;
}

# ASTAR: the estimate of a packed position -- the sum over its boxes of the shortest push
# distance to any goal. Computed from the position rather than carried, so nothing new is
# stored per node; it is paid only where a position is really queued, not for every
# candidate the deadlock battery throws away.
sub odhad ($p) {
    my (undef, @boxes) = unpack($pu, $p);
    my $h = 0;
    $h += $MinSteps[$_] // 0 foreach @boxes;
    return $h;
}

# Walks %Parent from $pozice back to the root, returning the full
# root-to-$pozice sequence. Used both to feed restart() at seed time and to
# build the final move string at the end of solve().
sub parent_postup ($pozice) {
    my @postup = ($pozice);
    my $p      = $pozice;

    # The walk stops on a false parent -- '' at the root, undef for a node that
    # has none -- so a chain that meets itself has no stop at all, and the loop
    # below would unshift until the machine dies. That is not a case to survive
    # quietly: a cycle means %Parent is corrupt, and a truncated chain would put
    # a WRONG path into bestbet. Since 2026-09-10 restart() no longer builds one
    # (a seed path that revisits a position keeps its first parenting), so this
    # is a tripwire, not a handler -- but it is the one that would have named the
    # fault in seconds instead of an OOM two games later.
    my %on;
    while (($p = $Parent{$p})) {
        confess(sprintf('parent_postup: %%Parent closes into a cycle on game %s after %d nodes',
            $Gameid // '?', scalar @postup))
            if exists $on{$p};
        $on{$p} = undef;
        unshift @postup, $p;
    }
    return @postup;
}

# Pure conversion, no side effects on %Seen/%Parent/@Heap: replays a move
# string (e.g. firstbet.path -- lowercase = walk, uppercase = push) from the
# game's start position and returns the sequence of "pozice" after each
# completed push (root first, final position last). Validates every step
# against %Cg (walls) and the live box layout, confess()ing on mismatch
# rather than silently producing a wrong sequence.
sub cesta_na_pozice ($path) {
    my @baggage = @Baggage;
    my %bag_at  = map(($_, 1), @baggage);
    my $man     = $Game{'player'};
    my @postup  = (pack($pu, $man, @baggage));
    for my $ch (split //, $path) {
        my $d = $InvPis{ lc $ch };
        confess("cesta_na_pozice: unknown move char '$ch'") unless defined $d;
        my $target = $man + $d;
        confess("cesta_na_pozice: $man has no neighbour $target (wall?)")
            unless grep {$_ == $target} @{ $Cg[$man] };
        if ($ch eq lc $ch) {
            confess("cesta_na_pozice: walk into occupied cell $target") if $bag_at{$target};
            $man = $target;
            next;
        }
        confess("cesta_na_pozice: no box to push at $target") unless $bag_at{$target};
        my $new_t = $target + $d;
        confess("cesta_na_pozice: push target $new_t has no path (wall?)")
            unless grep {$_ == $new_t} @{ $Cg[$target] };
        confess("cesta_na_pozice: push target $new_t already occupied") if $bag_at{$new_t};
        delete $bag_at{$target};
        $bag_at{$new_t} = 1;
        $man            = $target;
        @baggage        = sort {$a <=> $b} keys %bag_at;
        push @postup, pack($pu, $man, @baggage);
    } ## end for my $ch (split //, $path)
    return @postup;
} ## end sub cesta_na_pozice

# Thread a known root-to-solution sequence into an EMPTY search, and be the whole of
# what the two families do differently with it.
#
# In DIAL and ASTAR this is the SEED THREADER ONLY -- called once from solve() with the
# path from cesta_na_pozice() and never again during the search. Nothing compacts a
# cost-ordered frontier, and wiping %Seen would forfeit the finality the order
# guarantees. Every path node goes into the bucket of its own cost, the root at 0, so
# completeness holds by the old argument: nothing reachable is cut off, because the
# root's off-path children are generated when bucket 0 pops.
#
# In FIFO it is also the COMPACTION, called again after every improvement want_restart()
# approves. That is the mode's whole strength and its whole cost: the frontier is thrown
# away and rebuilt around the new record, which re-explores the record's neighbourhood
# breadth-first -- an accidental local search, and the reason FIFO mines shorter paths
# than either bucket mode. $nStart counts those calls.
# The caller must set $Bestbet/$Bestlen (to $postup[-1] and its cost) beforehand.
sub restart (@postup) {
    ++$nStart if $Fifo;
    @Bucket  = ();
    @Heap    = ();
    $CurMin  = 0;
    %Seen    = ();
    %Parent  = ();
    my $root = $postup[0];
    $Seen{$root}   = 0;
    $Parent{$root} = '';
    $N_Open        = 0;
    $O_Open        = $Fifo ? 1 : 0;
    my $pushed = $Pushed;    # the enqueues below count path nodes; put back at the end
    $Fifo ? heap_add($root) : bucket_add($root, 0);

    for my $i (0 .. $#postup - 1) {
        my $pozice      = $postup[$i];
        my $next_pozice = $postup[$i + 1];
        my $sol         = $Seen{$pozice} >> 1;
        my $next_sollen;

        # Only the step cost onto the next path node is needed here; the rest of
        # tahy()'s answer is hledej()'s business when it pops $pozice.
        foreach my ($child, $step)(tahy($pozice)) {
            next unless $child eq $next_pozice;
            $next_sollen = $sol + $step;
            last;
        }
        confess("restart: $next_pozice is not a child of its predecessor in \@postup")
            unless defined $next_sollen;

        # A path node's threaded cost need not be its MINIMAL cost -- a cheaper
        # route to it may exist off the path. No special case is needed for that:
        # if one exists, the search discovers it before $CurMin reaches this
        # bucket (every prefix of the cheaper route is cheaper still), relaxes the
        # node downward and this copy is skipped as stale. The terminal is never
        # queued -- its cost IS $Bestlen and its bucket is never reached.
        # A PATH THAT COMES BACK TO A POSITION IT HAS ALREADY BEEN IN must not
        # rewire that position's parent (USER 2026-09-10). The chain from the
        # later node runs back through the earlier one, so the rewiring closes
        # %Parent into a CYCLE -- and parent_postup() walks that with
        # `while (($p = $Parent{$p}))`, which then never ends: it unshifts into
        # an array for ever, inside save_improvement(), where neither the clock
        # nor the $MAX_GB net can see it. That is memory at gigabytes a second
        # and an OOM with no MEMCAP, which is exactly how it announced itself.
        # The root is the worst case, its `$Parent{$root} = ''` being the walk's
        # only stop.
        #
        # Keep the FIRST arrival: it is the cheaper one (the revisit means the
        # path spent moves to come back), and the note above already says a
        # threaded cost need not be the path's own. Measured on the stored
        # seeds: 3 of 803 paths revisit a position, and all three came from
        # FESTIVAL modes -- that engine's LURD is not a walk in our position
        # graph and nothing ever promised it would be.
        next if exists $Seen{$next_pozice};

        $Parent{$next_pozice} = $pozice;
        $Seen{$next_pozice}   = $next_sollen * 2;
        unless (exists $SolReal{$next_pozice}) {
            $Fifo ? heap_add($next_pozice) : bucket_add($next_pozice, $next_sollen);
        }
    } ## end for my $i (0 .. $#postup...)
    $MaxOpen = $N_Open;

    # Threaded path nodes are not children of anything; keep the children-per-parent
    # metric clean (the enqueues above counted them). Put back, NOT zeroed: a zero here
    # wiped the whole numerator while $Expanded kept the whole solve, so after a FIFO
    # compaction info() showed a ratio under 1 on a frontier that was growing (USER
    # 2026-09-05).
    $Pushed = $pushed;

    # The band is a property of the record just threaded: rebuilt here, at the width
    # solve() has chosen ($BAND after an improvement, 0 = none after an exhaustion).
    # $Band_dropped describes the FRONTIER, not the band: it is zeroed here, where the
    # frontier was just discarded, and nowhere else -- band_build() used to zero it, and
    # the rebuild WITHOUT a restart in hledej_fifo (heap kept) then forgot the children
    # already dropped from that heap, so a dry heap passed as a proof: game 7265 came out
    # SOLVED at 55 against an optimum of 49 proved three ways (found 2026-09-06 by the
    # band's population gate, now ai/band_vs_proof.pl, 1 of 60 games).
    $Band_dropped = 0;
    band_build(@postup) if $Fifo and $Band_cur;
} ## end sub restart

# FIFO ONLY: is the open list worth throwing away? A restart COMPACTS an overgrown
# frontier; it does not exist to rebuild a small one. Only when the list is both large
# ($RESTART_MIN_OPEN) and still mostly unexplored ($RESTART_RATIO of its peak) does
# re-seeding from the best path beat simply continuing with the tightened $Bestlen, which
# prunes the same list for free. The bucket modes never call this: their frontier is
# ordered, and a %Seen wipe would forfeit the finality that ordering buys.
sub want_restart () {
    return
           $RESTART_MIN_OPEN
        && $N_Open > $RESTART_MIN_OPEN
        && $N_Open / $MaxOpen > $RESTART_RATIO;
}

# THE BAND (see $BAND above). A configuration = the BOX part of a packed position (boxes
# are kept sorted by tahy(), so substr($p, $Cw) is canonical); its distance to the track =
# $Nbox - max_T |C & T| over the track's configurations T, each a bit string over the cells.
sub band_build (@postup) {
    %BandMemo = ();    # verdicts and witnesses were about the OLD band
    @BandCfg  = ();
    for my $p (@postup) {
        my $k = substr($p, $Cw);
        next if exists $BandMemo{$k};
        push @BandCfg, band_bits($p);
        $BandMemo{$k} = pack('Cn', 0, $#BandCfg);    # on the track: distance 0, its own witness
    }
    return;
}

sub band_bits ($p) {
    my $b = $Band_zero;
    my @c = unpack($pu, $p);
    shift @c;    # the player
    vec($b, $_, 1) = 1 for @c;
    return $b;
}

# Is $child within $Band_cur boxes of the record's track? $parent is the position it was
# generated from -- already in the band, so its memo entry normally exists.
sub in_band ($child, $parent) {
    my $k = substr($child, $Cw);
    my $m = $BandMemo{$k};
    return length $m ? 1 : 0 if defined $m;
    my $cb = band_bits($child);
    my $pm = $BandMemo{ substr($parent, $Cw) };
    if (defined $pm and length $pm) {
        my $tp = unpack('xn', $pm);
        my $d  = $Nbox - unpack('%32b*', $cb &. $BandCfg[$tp]);
        if ($d <= $Band_cur) {
            $BandMemo{$k} = pack('Cn', $d, $tp);
            return 1;
        }
    }
    my ($best, $bt) = ($Nbox + 1, 0);
    for my $t (0 .. $#BandCfg) {
        my $d = $Nbox - unpack('%32b*', $cb &. $BandCfg[$t]);
        next unless $d < $best;
        ($best, $bt) = ($d, $t);
        last if $d == 0;
    }
    if ($best <= $Band_cur) {
        $BandMemo{$k} = pack('Cn', $best, $bt);
        return 1;
    }
    $BandMemo{$k} = '' if keys %BandMemo < $BAND_MEMO_MAX;
    return 0;
} ## end sub in_band

# A betterment, the moment it happens: the path is built, kept in @Track and handed to
# $ON_IMPROVED, so a caller has every improvement before the solve ends (in the Sokoban
# project this was the write to the database that let a killed run keep its record).
sub save_improvement () {
    my $cas  = tv_interval($timer);
    my $path = get_path(parent_postup($Bestbet));
    push @Track,
        {
            'seq'     => scalar(@Track) + 1,
            'cas'     => $cas,
            'sollen'  => length $path,
            'pushes'  => ($path =~ tr/UDRL//),
            'counter' => $counter,
            'n_open'  => $N_Open,
            'nstart'  => $nStart,    # FIFO's restarts so far; 0 in the bucket modes
            'path'    => $path,
        };
    $ON_IMPROVED->($path, $cas) if $ON_IMPROVED;
} ## end sub save_improvement

# Free the buckets at and above the (just tightened) $Bestlen: nothing there
# can ever be popped again. Runs once per improvement, so the walk over the
# discarded tail to keep $N_Open honest is paid where nothing is hot.
# It cuts under ASTAR too, and for a reason worth stating: the bucket index there is
# f = g + h with h ADMISSIBLE, so f >= $Bestlen means no solution through that node can
# beat the record -- the same statement the cost order made with g alone. (Under a WEIGHT
# it would not, which is one more reason a weight is not a mode here.) FIFO never calls
# this: it has no tail to cut, only the pointwise `>= $Bestlen` tests.
sub trim_tail () {
    return if $#Bucket < $Bestlen;
    for my $b (@Bucket[$Bestlen .. $#Bucket]) {
        $N_Open -= scalar @$b if $b;
    }
    splice(@Bucket, $Bestlen);
}

# THE LEVEL PROFILE: the moment the dial enters a cost level, noted when $CurMin has really
# moved on -- what overrun_ok() predicts the rest of the proof from. (In the Sokoban
# project this wrote one row per level, with the level's width and counters, into a table;
# the width at this moment is the level's COMPLETE population in DIAL -- nothing can be
# inserted into a bucket the dial already stands in -- and a snapshot under ASTAR, whose
# estimate is not consistent, so a level can grow after it is entered and even be
# re-entered; a level is noted only on its first arrival. FIFO has no levels at all.)
sub record_level () {
    $Level_at = $CurMin;
    $LevelCas[$CurMin] = tv_interval($timer);
} ## end sub record_level

# THE OVERRUN (v3.3): may DIAL or ASTAR go on at $t seconds, past $LIMIT and before the
# hard stop at 2 * $LIMIT? Asked at the last level entered. In DIAL a level's price rises
# while the frontier grows and FALLS as the record starts cutting children off, so the
# last two levels predict the rest: w1 = cas(g) - cas(g-2) (pairs, because odd and even
# levels alternate in width), rho = w1 / (cas(g-2) - cas(g-4)), and the pairs still to go
# up to $Bestlen cost w1*rho + w1*rho^2 + ... The prediction runs high more often than
# low, so HALF of it must fit into the time left -- the replay put that at 62 % of the
# late proofs in DIAL and 86 % in ASTAR, against 48 / 67 % for the whole prediction.
# A cheaper-ing trend (rho < 1) is NOT required: a few rising levels still fit, and
# demanding it lost half the proofs. Levels can be skipped (an empty bucket), so "g - 2"
# is the highest level recorded at or below it.
sub overrun_ok ($t) {
    my $g  = $Level_at;
    my $cg = $LevelCas[$g] // return 0;
    my ($c2, $c4);
    for (my $j = $g; $j >= 0; --$j) {
        next unless defined $LevelCas[$j];
        $c2 //= $LevelCas[$j] if $j <= $g - 2;
        if ($j <= $g - 4) {$c4 = $LevelCas[$j]; last}
    }
    return 0 unless defined $c4 and $cg > $c2 and $c2 > $c4 and $Bestlen < 1e6;
    my $w1  = $cg - $c2;
    my $rho = $w1 / ($c2 - $c4);
    my $m   = int(($Bestlen - $g + 1) / 2);
    my $pred;
    if    (abs($rho - 1) < 1e-9)             {$pred = $w1 * $m}
    elsif ($rho > 1 and $m * log($rho) > 50) {return 0}
    else                                     {$pred = $w1 * $rho * ($rho**$m - 1) / ($rho - 1)}
    return 0.5 * $pred <= 2 * $LIMIT - $t ? 1 : 0;
} ## end sub overrun_ok

# DIAL's bublej (reinstated -- USER 2026-09-01): the relaxation cascade came
# back, because throwing it away deferred KNOWN improvements. A waiting node
# cannot be expanded yet, but its continuation may already be on record -- the
# threaded seed path, and on a warm game env everything the previous runs ever
# expanded (tahy.brk). A shortcut into such a node is an improvement CERTIFICATE
# the moment it is found: cheaper arrival + recorded continuation = better
# solution. Without the cascade that certificate sat in one %Seen cell until
# $CurMin climbed to it -- and a run that never got there lost it entirely.
#
# Simpler than the FIFO original in three ways, all forced by the order:
#   * no re-queue verdict: a relaxed waiting node MUST get its copy in the
#     lower bucket every time, or the staleness check would skip it for good;
#   * no $Improved/want_restart abort: there is no restart to hand over to,
#     and an interrupted cascade would strand stale costs with no re-trigger;
#   * an EXPANDED node stops the walk by itself: its cost is final, so the
#     `improves?` test fails and the recursion never enters it.
# THAT LAST ONE HOLDS ONLY IN THE COST ORDER. Under ASTAR the pop order is f, a popped
# cost is NOT final, and an expanded node must be re-openable -- so both of its guards
# (here and at the call site) are conditional on $H_on, and the plain assignment to
# %Seen below is what re-opens it: it clears the expanded bit. Measured: without the
# re-opening 37928 came back with 78 against a known 77.
# On a COLD run the cascade is near-inert: only expanded nodes carry %Tahy,
# and expanded nodes cannot be relaxed -- so the A/B numbers measured without
# it stand. It pays on a warm env, which is where the endgame lives.
sub bublej ($child, $pozice, $sollen) {
    $Parent{$child} = $pozice;
    $Seen{$child}   = $sollen * 2;
    if (exists $SolReal{$child}) {
        if ($sollen < $Bestlen) {
            $Bestbet = $child;
            $Bestlen = $sollen;
            save_improvement();
            trim_tail();
        }

        # A terminal is never queued -- its cost IS $Bestlen and its bucket is
        # never reached.
        return;
    }
    bucket_add($child, $sollen);
    my $th = tahy_get($child) or return;
    foreach my ($grand, $step)(@$th) {
        info();
        my $sol = $sollen + $step;
        next if $sol >= $Bestlen;
        next unless exists $Seen{$grand};             # the cascade never discovers
        next if !$H_on and $Seen{$grand} & 1;         # cost order: expanded = final
        next unless ($Seen{$grand} >> 1) > $sol;      # recurse only into a real improvement
        next if isbad($grand);
        bublej($grand, $child, $sol);
    }
    return;
} ## end sub bublej

# DIAL: take the cheapest waiting position, always. The proof no longer waits
# for the open list to drain -- the moment the cheapest bucket reaches $Bestlen,
# everything still queued is provably no better than the record and 'SOLVED' is
# earned on the spot. $CurMin along the way is a live lower bound: no solution
# shorter than $CurMin exists once bucket $CurMin - 1 has emptied.
sub hledej () {
    while (1) {

        # Advance to the next non-empty bucket. In DIAL this is monotone -- every insert
        # lands at parent cost + step >= $CurMin + 1, so an emptied bucket stays empty.
        # Under ASTAR an insert may LOWER $CurMin (bucket_add), and the scan simply
        # starts again from wherever the dial now stands; an emptied bucket can be
        # refilled and that is exactly what the descent is for.
        # Two ways to finish, both a PROOF in either mode: the cheapest waiting position
        # is no better than the record, or the buckets ran out entirely (the whole
        # reachable space is expanded -- the unseeded UNSOLVABLE case ends here). Under
        # ASTAR the first one reads f >= $Bestlen, which with an admissible h says the
        # same thing about g.
        while ($CurMin < $Bestlen and $CurMin <= $#Bucket and !($Bucket[$CurMin] and @{ $Bucket[$CurMin] })) {++$CurMin}
        return 'SOLVED' if $CurMin >= $Bestlen or $CurMin > $#Bucket;
        record_level() if $CurMin > $Level_at;    # the level profile, one row per level
        ++$counter;
        info();

        # $LIMIT = 0 means NO time limit: run until the proof lands or the state
        # space is exhausted. Past the limit the search goes on only while the level
        # profile says the proof fits before 2 * $LIMIT (v3.3, see overrun_ok); the
        # verdict is renewed at every new level. FIFO's easing is a different one --
        # "this wave is draining", a notion of the restart regime.
        if ($LIMIT and (my $t = tv_interval($timer)) > $LIMIT) {
            return 'TIMEOUT' if $t > 2 * $LIMIT;
            if (!defined $Overrun_level or $Overrun_level != $Level_at) {
                $Overrun_level = $Level_at;
                $Overrun_ok    = overrun_ok($t);
            }
            return 'TIMEOUT' unless $Overrun_ok;
        }

        # The race signal and the $MAX_GB safety net, gated to one read per 4096 pops: the
        # memory call is ~2 us, but a search does millions of pops. Same shape and cadence
        # as SolverBerk's.
        unless ($counter & 4095) {
            return 'IGNORE' if race_lost();    # another mode proved this game
            return 'MEMCAP' if $MAX_GB and Games::Sokoban::Solver::Memory::used_gb() > $MAX_GB;
        }
        my $pozice = pop @{ $Bucket[$CurMin] };
        --$N_Open;
        my $s   = $Seen{$pozice};
        my $sol = $s >> 1;               # the position's own COST g -- under ASTAR not the bucket index
        next if $s & 1;                  # already expanded -- a stale duplicate

        # Relaxed while waiting: the cheaper copy did the work, and this one's recorded
        # cost no longer matches the bucket it is sitting in. The comparison is against
        # the ORDERING KEY, which is g in DIAL and f in ASTAR -- and it is a valid test in
        # both only because no insert is clamped any more (see bucket_add): every entry in
        # this bucket was put here with that exact key, so a mismatch means the node has
        # been relaxed since and its cheaper copy is waiting further down. Under the
        # clamp this test had to be switched off entirely, and the expanded bit above
        # carried the whole duty.
        next if ($H_on ? $sol + odhad($pozice) : $sol) != $CurMin;
        next if isbad($pozice);
        $Seen{$pozice} |= 1;             # cheapest-first: this cost is FINAL
        ++$Expanded;                     # a real parent: denominator of info()'s children-per-parent
        foreach my ($child, $step)(tahy($pozice)) {
            ++$bc;
            my $sollen = $sol + $step;
            next if $sollen >= $Bestlen;
            next if isbad($child);
            if (!exists $Seen{$child}) {
                $Parent{$child} = $pozice;
                $Seen{$child}   = $sollen * 2;
                if (exists $SolReal{$child}) {

                    # Terminals are generated in cost order, so every one that gets
                    # past the $Bestlen test above IS an improvement. Never queued.
                    $Bestbet = $child;
                    $Bestlen = $sollen;
                    save_improvement();
                    trim_tail();
                    next;
                }
                bucket_add($child, $sollen);
            }
            elsif (($H_on or !($Seen{$child} & 1)) and ($Seen{$child} >> 1) > $sollen) {

                # The "not expanded" half of this guard is the COST ORDER's -- under the
                # f-order a popped cost is NOT final (f is a cost order only while the
                # estimate is consistent, and ours is not: `steps` is measured on Parser's
                # pruned push graph while tahy() generates from the search's own, so one
                # push can lower the estimate by more than the move it cost). So an
                # expanded node whose cheaper route turns up must be RE-OPENED, and bublej
                # does exactly that: its plain `$Seen{$child} = $sollen * 2` clears the
                # expanded bit, and bucket_add puts the node back in a bucket. Measured:
                # without re-opening, 37928 came back with 78 against a known 77.
                #
                # A cheaper route to a node waiting in a higher bucket (or, under ASTAR,
                # to one already expanded): bublej() relaxes it, queues its copy at the
                # better cost, and pushes the saving onward through whatever continuations
                # are on record -- the threaded seed path, a warm env's tahy.brk --
                # REPORTING any terminal it improves on the way. That reporting is the
                # whole point and not an optimisation: the saving reaches %Parent by
                # itself, so a run without the cascade returns a shorter path while
                # $Bestlen, the trajectory and the bestbet write know nothing about it.
                bublej($child, $pozice, $sollen);
            }
        } ## end foreach my ($child, $step)(...)
    } ## end while (1)
} ## end sub hledej

# FIFO's cascade (v1.8, verbatim in behaviour from SolverOld.pm). Two things separate it
# from the bucket modes' bublej above, and both come straight from the order:
#   * it RETURNS A VERDICT -- whether $child is still worth queueing. Expanding a node can
#     do exactly two things, DISCOVER a child not in %Seen or RELAX one at a worse cost,
#     and this walk has just done every relaxation there was. So the only reason left to
#     pop $child again is a child nobody has seen, and the loop below passes that very
#     test on its way through: the verdict costs nothing, it is read off the walk the
#     cascade makes anyway. Measured over seven proven games, 98.2 % of what the old
#     unconditional re-queue put back was a node whose whole move list had just been
#     settled; re-expansions fell from 47.8 % of all expansions to 0.7 %.
#   * it PRESERVES the queued bit ($Seen{$child} & 1). The node may be sitting in @Heap
#     right now, and a relaxation must not silently unqueue it.
# It also may ABANDON the cascade, but only when a restart is about to discard the work
# anyway -- dropping relaxations otherwise strands nodes at stale %Seen values with
# nothing left to re-trigger them, so a verdict built from half a list must be the safe
# one.
sub bublej_fifo ($child, $pozice, $sollen) {
    $Parent{$child} = $pozice;
    $Seen{$child}   = $sollen * 2 + ($Seen{$child} & 1);
    if (exists $SolReal{$child}) {
        if ($sollen < $Bestlen) {
            $Bestbet  = $child;
            $Bestlen  = $sollen;
            $Improved = 1;
        }

        # A terminal's own cost IS $Bestlen by construction, so hledej_fifo() would pop it
        # and drop it again on `$sol >= $Bestlen` every single time. restart() has always
        # refused to thread a terminal onto the heap for exactly this reason.
        return 0;
    }

    # Never expanded -> nothing seen below it, and nothing but a real expansion will ever
    # generate its children. THIS is the case the re-queue exists for: the node was popped
    # and dropped on `$sol >= $Bestlen` without being expanded, so the cascade dead-ends
    # here and only the heap can carry it further.
    my $th   = tahy_get($child) or return 1;
    my $need = 0;
    foreach my ($grand, $step)(@$th) {
        if ($Improved and want_restart()) {
            $need = 1;
            last;
        }
        info();
        my $sol = $sollen + $step;
        next if $sol >= $Bestlen;
        next if isbad($grand);

        # A child nobody has seen is the one thing a re-expansion of $child could add,
        # because the cascade never discovers. `exists` is deliberate -- the root's cost
        # is 0, which is false, and must not be mistaken for absence.
        if (!exists $Seen{$grand}) {
            $need = 1;
            next;
        }
        next unless ($Seen{$grand} >> 1) > $sol;    # recurse only into a real improvement
        heap_add($grand) if bublej_fifo($grand, $child, $sol);
    } ## end foreach my ($grand, $step)(...)
    return $need;
} ## end sub bublej_fifo

# FIFO's search loop (v1.8). The open list is unordered, so there is no bound to read off
# it and no early proof: 'SOLVED' means @Heap GENUINELY RAN DRY, which is the only
# statement this regime can make about optimality. In exchange it finds improvements as a
# staircase, and hands each one back to solve() as 'IMPROVED' whenever want_restart()
# approves compacting the frontier around it.
sub hledej_fifo () {
    while ($N_Open) {
        ++$counter;
        info();

        # The easing clause is this regime's own: "not close to finishing" means "this
        # wave is still draining", a notion only a restart search has.
        return 'TIMEOUT' if $LIMIT and tv_interval($timer) > $LIMIT and $N_Open > 0.7 * $MaxOpen;

        # The race signal and the $MAX_GB safety net -- see the bucket loop.
        unless ($counter & 4095) {
            return 'IGNORE' if race_lost();
            return 'MEMCAP' if $MAX_GB and Games::Sokoban::Solver::Memory::used_gb() > $MAX_GB;
        }
        my $pozice = shift @Heap;
        $Seen{$pozice} &= ~1;    # off the queue; the cost keeps the high bits
        --$N_Open;
        next if isbad($pozice);
        my $sol = $Seen{$pozice} >> 1;

        # NB: popped and NOT expanded -- no %Tahy is cached for it. This is precisely the
        # node bublej_fifo()'s cascade can dead-end on later, hence heap_add() there.
        next if $sol >= $Bestlen;
        ++$Expanded;    # a real parent: denominator of info()'s children-per-parent
        foreach my ($child, $step)(tahy($pozice)) {
            ++$bc;
            my $sollen = $sol + $step;
            next if $sollen >= $Bestlen;
            next if isbad($child);

            # THE BAND: an unseen child more than $Band_cur boxes off the record's track is
            # not queued and not recorded (a later, closer route must still be free to
            # discover it). Counted: a heap that ran dry with drops is not a proof, and
            # solve() drops the band on that count.
            if ($Band_cur and !exists $Seen{$child} and !in_band($child, $pozice)) {
                ++$Band_dropped;
                next;
            }

            # Discovery and enqueueing live HERE, not in the cascade:
            #   unseen        -> record it (it gets expanded when its turn comes)
            #   seen, better  -> relax it and let bublej_fifo() carry that onward
            #   seen, no gain -> nothing to do
            # Either way it must be queued if it is not queued already (SPFA).
            my $need;
            if (!exists $Seen{$child}) {
                $Parent{$child} = $pozice;
                $Seen{$child}   = $sollen * 2;    # not queued yet; heap_add sets the bit
                $need           = 1;              # nobody has expanded it: it must be queued
                if (exists $SolReal{$child}) {
                    $Bestbet  = $child;
                    $Bestlen  = $sollen;
                    $Improved = 1;
                    next;
                }
            }
            elsif (($Seen{$child} >> 1) > $sollen) {
                $need = bublej_fifo($child, $pozice, $sollen);
            }
            else {
                next;
            }
            heap_add($child) if $need;
            if ($Improved) {
                save_improvement();
                return 'IMPROVED' if want_restart();

                # The band follows the RECORD, not the restart: under a band the frontier
                # stays small and want_restart() hardly ever fires (17850: 122 improvements,
                # 3 restarts), so the band would go on hugging the seed. Rebuild it around
                # the new record and keep the heap -- what is queued was admitted under the
                # old band and may finish; nothing new gets in outside the new one.
                # The heap is KEPT, so $Band_dropped is NOT reset here: what the old band
                # dropped is still missing from this frontier, and a dry heap later is a
                # proof only if nothing was ever dropped from it (see restart()).
                band_build(parent_postup($Bestbet)) if $Band_cur;

                # Keep this open list and carry on with the tighter $Bestlen, which now
                # prunes it via the `>= $Bestlen` tests above. $pozice's remaining children
                # still get their turn -- that is the whole point.
                $Improved = 0;
            }
        } ## end foreach my ($child, $step)(...)
    } ## end while ($N_Open)
    return 'SOLVED';
} ## end sub hledej_fifo

# solve($gameid, $gm, $first_path): $gameid any integer the caller names the level by
# (printed in the progress lines), $gm the Parser's analysis in its blob() form,
# $first_path a solution to start from (the upper bound the search prunes against;
# undef or '' = none). $LIMIT (seconds; 0 = no limit) and $MODE are package variables.
sub solve ($gameid, $gm, $first_path = undef) {
    my ($pozice, $reason, $path, $plen, $steps, $doba, $ending, $status);

    # Resolve $MODE ONCE, here, into the two flags everything downstream branches on --
    # beyond speed: this module runs under `warnings FATAL => uninitialized`, so a sub
    # testing an unresolved flag would die on its first call. An unknown mode dies HERE,
    # loudly, rather than silently running as DIAL.
    confess("solve: unknown \$MODE '$MODE' (want DIAL, ASTAR or FIFO)")
        unless $MODE eq 'DIAL' or $MODE eq 'ASTAR' or $MODE eq 'FIFO';
    $Fifo = ($MODE eq 'FIFO')  ? 1 : 0;
    $H_on = ($MODE eq 'ASTAR') ? 1 : 0;
    initvars($gameid, $gm);
    $pozice          = pack($pu, $Game{'player'}, @Baggage);
    $Seen{$pozice}   = 0;    # cost 0, NOT expanded -- see the %Seen note at the top
    $Parent{$pozice} = '';
    @Bucket          = ();
    @Heap            = ();
    $Improved        = 0;
    $CurMin          = 0;
    $Level_at        = -1;    # no level recorded yet (0 is a real level)
    @LevelCas        = ();
    $Overrun_level   = undef;
    $Overrun_ok      = undef;
    $N_Open          = 0;
    $O_Open          = 0
        ; # last-print open count; must be set here too, not only in restart(), or an unseeded solve that runs past info()'s 6s threshold reads it undef (FATAL under 'uninitialized')
    $MaxOpen = 0;
    $Pushed  = 0;    # the enqueue increments it; zeroed before the root goes in
    $Fifo ? heap_add($pozice) : bucket_add($pozice, 0);
    $bc      = 0;
    $counter = 0;

    # Same reason as $O_Open above: info() divides by these, and the module runs under
    # `warnings FATAL => uninitialized`.
    $Pushed   = 0;
    $Expanded = 0;
    $reason   = 'UNSOLVABLE';
    $timer   = [&gettimeofday()];
    $Gameid   = $gameid;
    $Cas      = time();

    # The trajectory is per-solve: a second solve() in the same process must not inherit
    # the first one's.
    @Track      = ();
    $LastStatus = '';

    if (defined $first_path && length $first_path) {
        my @postup = cesta_na_pozice($first_path);
        $Bestbet = $postup[-1];
        $Bestlen = length($first_path);
        backlinen("START: $Bestlen") if $QUIET < 2;

        # The band exists only around a threaded record, and only in FIFO. An unseeded
        # solve has no record to build it from and runs unrestricted.
        $Band_cur = ($Fifo and $BAND and $BAND < $Nbox) ? $BAND : 0;
        restart(@postup);
    }

    # Seeding the search is not a restart -- the 1.8 archive did not count it either.
    # Reset AFTER restart(), which increments it under FIFO.
    $nStart = 0;

    # info() compares against these to decide which of its lines to leave standing; set
    # AFTER the seed, so the very first line is not treated as a fresh record.
    ($O_Bestbet, $O_CurMin) = ($Bestlen, $CurMin);

    # DIAL and ASTAR: ONE call. hledej() reports every improvement itself and never
    # unwinds -- there are no restarts to unwind for.
    # FIFO: the restart loop. hledej_fifo() returns 'IMPROVED' only when want_restart()
    # has approved compacting the frontier, and it has already persisted the betterment,
    # so there is nothing left to decide here.
    if (!$Fifo) {
        $status = hledej();
    }
    else {
        while (1) {
            $Improved = 0;
            $status   = hledej_fifo();
            last if $status eq 'TIMEOUT' or $status eq 'MEMCAP' or $status eq 'IGNORE';
            if ($status eq 'SOLVED') {

                # The heap ran dry. Under a band that dropped children that is NOT a proof
                # -- it says "nothing shorter within $Band_cur boxes of the record". Drop the
                # filter and search the same record's surroundings UNRESTRICTED: only a heap
                # that dropped nothing proves, and a wider band would either drop something
                # too (no proof, its region re-crawled by the next width) or drop nothing
                # (the same positions the unrestricted search visits, plus the test cost).
                # The 3.1 ladder 3, 4, ... $Nbox paid that for improvements found 3+ boxes
                # off the track -- 4 of 344 measured (USER 2026-09-07). An improvement found
                # here puts the band back at $BAND around the new record (below).
                last unless $Band_cur and $Band_dropped;
                $Band_total += $Band_dropped;
                backlinen(sprintf 'BAND %d exhausted: %d children dropped -> unrestricted', $Band_cur, $Band_dropped)
                    if $QUIET < 2;
                $Band_cur = 0;
                restart(parent_postup($Bestbet));
                next;
            }

            # An improvement: a new record, so a fresh band at the base width around it.
            $Band_total += $Band_dropped;
            $Band_cur = ($BAND and $BAND < $Nbox) ? $BAND : 0;
            restart(parent_postup($Bestbet));
        }
    }
    $path  = undef;
    $doba  = tv_interval($timer);
    $plen  = 0;
    $steps = 0;
    if ($Bestbet) {

        # Populate the path whenever we have a $Bestbet at all, regardless of
        # how we got here -- a TIMEOUT'd run can still be carrying a real,
        # often better-than-the-seed solution; the caller (and a future
        # solve() call seeded from it) shouldn't lose that just because it
        # wasn't proven optimal this time.
        $path  = get_path(parent_postup($Bestbet));
        $plen  = length($path);
        $steps = $path =~ tr/UDRL//;
    }
    if ($status eq 'TIMEOUT' or $status eq 'MEMCAP' or $status eq 'IGNORE') {

        # The open list was cut short (clock, the $MAX_GB memory net, or another mode's
        # proof in a race -- IGNORE, which $LastStatus keeps by name) -- even a
        # seeded/already-improved $Bestbet hasn't been proven optimal, so this must NOT be
        # reported SOLVED. Both leave as TIMEOUT so every caller and status contract holds;
        # the memory stop says so loudly instead.
        say {*STDERR} colored(sprintf('OUT OF MEMORY (used %.2f GiB > MAX_GB %.2f)',
                Games::Sokoban::Solver::Memory::used_gb(), $MAX_GB // 0), 'bright_red')
            if $status eq 'MEMCAP';
        $reason = 'TIMEOUT';
    }
    elsif ($Bestbet) {

        # The search returned 'SOLVED': in DIAL/ASTAR the cheapest waiting position
        # reached $Bestlen (or the buckets ran out), in FIFO the heap genuinely ran dry.
        # Either way $Bestbet is provably the best reachable from this start.
        $reason = 'SOLVED';
    }

    # else: exhausted with no $Bestbet at all -- $reason stays 'UNSOLVABLE'.
    $ending = sprintf '%8d %3d %4d %-10s %6d %6d %12.4f %8.0f %8.0f',
        $gameid, $Game{'nbox'}, $Game{'ncell'}, $reason, $plen, $steps, $doba, $bc / $doba, $counter / $doba;
    barva($reason, $ending);
    bad_close($reason eq 'SOLVED' ? 1 : 0);

    # Why the run ended, by name: a MEMCAP or IGNORE stop returns as TIMEOUT (see above)
    # but must not be laundered -- the console line is gone by morning, this is what says
    # WHY the run ended.
    $LastStatus = ($status eq 'MEMCAP' or $status eq 'IGNORE') ? $status : $reason;
    backlinen(sprintf 'BAND %d: %d children dropped, memo %d, track %d', $BAND,
        $Band_total + $Band_dropped, scalar keys %BandMemo, scalar @BandCfg)
        if $Fifo and $BAND and $QUIET < 2;

    # A race's loser returns IGNORE, so a driver can tell "another mode proved it" from
    # "the clock ran out"; the record it holds is in $path all the same.
    $reason = 'IGNORE' if $status eq 'IGNORE';
    return ($reason, $path, $doba, $bc, $counter);
} ## end sub solve
1;
