package Games::Sokoban::Solver::Festival::Analysis;

# THE LEVEL ANALYSIS FOR THE FESTIVAL ENGINE, ON ITS OWN.
#
# Games::Sokoban::Solver::Parser turns a level into the hash Firstbet reads its
# maps out of. This module is that arrangement for Games::Sokoban::Solver::
# Festival: it produces every map that depends on the LEVEL and not on where
# the boxes stand, once, and the engine's eight modes then read the frozen hash
# and compute none of it -- a quarter of a minute of preparation on a large
# level that would otherwise be paid by every mode.
#
# INDEPENDENT OF THE ENGINE, DELIBERATELY. 250 subs of the engine are reachable
# from the analysis; 48 of them are its own and 202 are used by the search as
# well. Rather than have the analysis call back into the engine, those 202 are
# DUPLICATED here, with the maintenance cost stated: two copies of an algorithm
# are two chances to drift. Everything below the API section is the analysis
# itself, carried over from the engine unchanged.
#
# TWO FUSES, AND WHAT THEY SAY. Two parts of the analysis give themselves a
# share of the budget and stop when it is spent: the hotspot builder throws its
# whole table away after a quarter of it, the envelope analysis stops adding
# patterns after half. The maps are still correct without them -- the engine's
# own deadlock tests stand in -- but the engine is then a somewhat weaker
# solver, and nothing in its results would say so. Hence the two flags in the
# hash, hotspots_incomplete and envelopes_incomplete: in the Sokoban project,
# where the analysis was stored once with hours of budget, a fuse that fired
# was a hard stop; here a level is analysed when it is solved, under a budget
# of the caller's choosing, so the caller is told and decides. Nothing else of
# the analysis is bounded: on the project's database the rest took minutes at
# the worst.
#
# NO FALLBACKS on the reading side: a frozen hash that is empty, corrupt or
# stamped by different analysis code is a hard stop (thaw), because an engine
# quietly running on wrong maps would be a slightly worse solver and nothing
# would ever report it.
#
# Lineage: Games::Sokoban::Festival_Parser 0.02 of the Sokoban project.

our $VERSION = '0.01';

use v5.42;
use warnings FATAL => 'uninitialized';
no warnings 'recursion';

# Every file-scope variable of this module, in one place. Nothing here is
# reachable from outside: parse() returns the analysis and that is the whole
# interface.
my (
    $Analysed_key, $BOX_ONLY, $CACHE_MISS, $DZ_ONLY, $DZ_len,
    $Envelopes_incomplete, $Hotspots_incomplete, $NOT_BASE, $NOT_BOX, $NOT_DZ, $NOT_SOKOBAN,
    $NOT_TARGET, $SOK_ONLY, $ZERO_BOARD, $bfs_distance_from_to, $blocks_place,
    $completely_blocks, $dist_normalizer, $distance_from_to, $end_time, $forbidden_pull_tunnel,
    $forbidden_push_tunnel, $girl_distance, $global_boxes_in_level, $global_fail_reason, $global_initial_sokoban_x,
    $global_initial_sokoban_y, $height, $index_num, $initial_board, $inner,
    $inv_n_boxes, $log_deadlock_cache, $max_push_dist, $mpdb_board, $ncells,
    $netlock_grid, $netlock_level_detected, $pull_mpdb_board, $rooms_board, $rooms_num,
    $semi_holes, $snail_chain, $snail_chain_len, $snail_dist, $snail_level_detected,
    $snail_target_x, $snail_target_y, $start_time, $target_holes, $time_limit,
    $total_deadlock_cache_entries, $width, %CODE_VAL, %cache, @ANALYSIS_STATE,
    @base_graph, @delta_p, @delta_p_8, @delta_x, @delta_x_8,
    @delta_y, @delta_y_8, @gamma_table, @impossible_place, @index_to_p,
    @index_to_x, @index_to_y, @mpdb_list, @new_envelope_patterns, @patterns,
    @pull_mpdb_list, @pull_patterns, @room_size, @room_with_corridors, @square_place_p,
    @square_place_x, @square_place_y, @targets_reachable_from, @y_x_to_index_table,
);


use Carp ();
use Storable ('nfreeze');    # thaw() stays qualified: this module has its own
use Compress::Zlib ('compress', 'uncompress');


# ====================================================================
# CONSTANTS (all modules, dependency order)
# ====================================================================

use constant {
    WALL          => 1,
    BOX           => 2,
    TARGET        => 4,
    SOKOBAN       => 8,
    BASE          => 16,
    DEADLOCK_ZONE => 32,

    SPACE => 0,

    MAX_SOL_LEN => 1500,
    MAX_ROOMS   => 70,
};
use constant {
    OCCUPIED   => WALL | BOX,
    PACKED_BOX => BOX | TARGET,
};
use constant {
    NORMAL                => 0,
    DEADLOCK_SEARCH       => 1,
    BASE_SEARCH           => 2,
    K_DIST_SEARCH         => 3,
    MINI_SEARCH           => 4,
    FORWARD_WITH_BASES    => 5,
    GIRL_SEARCH           => 6,
    REV_SEARCH            => 7,
    DRAGONFLY             => 8,
    WOBBLERS_SEARCH       => 9,
    HF_SEARCH             => 10,
    ROOMS_DEADLOCK_SEARCH => 11,
    NAIVE_SEARCH          => 12,
    XY_SEARCH             => 13,
    MINI_CORRAL           => 14,
    IGNORE_CORRAL         => 15,
    BICON_SEARCH          => 16,
    MAX_DIST_SEARCH       => 17,
    MAX_DIST_SEARCH2      => 18,
    SNAIL_SEARCH          => 19,
    NETLOCK_SEARCH        => 20,
};
use constant MAX_REQUESTS => 10000;    # helper.h
use constant MAX_MOVES => 11500;
use constant {
    OPTIMIZE_PACKED       => 0,
    OPTIMIZE_CONNECTIVITY => 1,
    OPTIMIZE_ROOMS        => 2,
    OPTIMIZE_HOTSPOTS     => 3,
    OPTIMIZE_OUT_OF_PLAN  => 4,
};
use constant {PER_DEPTH => 0, PER_SIDE => 1, PER_ALG => 2};
use constant {
    K_DIST_MAX_POSITIONS => 600,

    MAX_K_DIST_HASH_SIZE => 500,
};
use constant {
    NOT_DEADLOCK    => 0,
    IS_DEADLOCK     => 1,
    SEARCH_EXCEEDED => 2,

    MAX_ROOMS_DEADLOCK_SEARCH => 200,
};
use constant {
    MAX_TREE_LABELS => 10000,

    SIZEOF_EXPANSION_DATA => 136,    # measured from the C build (x64 gcc)
};
use constant {

    MAX_WOBBLERS_DEADLOCK_SEARCH => 50,
};
use constant {

    MAX_XY_DEADLOCK_SEARCH => 500,
};
use constant BIG_DISTANCE => 6;
use constant {
    MAX_STUCK_PATTERN_SIZE => 12,

    DISTILL_ON_TARGETS => 0,
    DISTILL_XY         => 1,
};
use constant {
    MAX_DEADLOCK_SEARCH => 50,

};
use constant MAX_DRAGONFLY_ROOTS => 200;

# ====================================================================
# FILE-SCOPE VARIABLES (all modules, dependency order)
#
# Hoisted, and that is REQUIRED, not cosmetic: one file is one
# lexical scope, and a sub must stand below the declaration it
# mentions. The tree does not respect that order -- Util reads
# Board's initial_board while standing above Board -- so leaving
# the declarations in place does not compile.
#
# 'our' survives only where something outside needs the symbol:
# exported names (Exporter goes through the symbol table) and the
# names the compatibility shim aliases (a typeglob cannot point at
# a lexical), plus two declared knobs. Everything else is lexical.
# ====================================================================

$time_limit = 600;
$height = 0;
$width  = 0;
@delta_y = (-1, 0, 1, 0);
@delta_x = (0, 1, 0, -1);
@delta_y_8 = (-1, -1, 0, 1, 1, 1, 0, -1);
@delta_x_8 = (0, 1, 1, 1, 0, -1, -1, -1);
$global_boxes_in_level = 0;
$global_fail_reason = '';
$ncells    = 0;    # $height * $width of the current level
@delta_p   = ();   # flat neighbor offsets, same order as delta_y/delta_x
@delta_p_8 = ();   # flat 8-neighbor offsets, same order as delta_y_8/delta_x_8
$ZERO_BOARD = '';
$initial_board = '';
$inner         = '';
$index_num     = 0;
$CACHE_MISS = [-1, 0];    # shared miss entry: [score, queries]
$total_deadlock_cache_entries = 0;
$log_deadlock_cache           = 22;
$target_holes = '';
$semi_holes   = '';
%CODE_VAL = (
    '0' => SPACE,           '1' => WALL,
    '2' => SPACE,           '3' => TARGET,
    '4' => BOX,             '5' => SOKOBAN,
    '6' => SOKOBAN,         '7' => BOX | TARGET,
    '8' => SOKOBAN | TARGET, '9' => WALL,
);
$DZ_len = -1;
$rooms_board = [];
$rooms_num   = 0;
$snail_level_detected = 0;
$netlock_level_detected = 0;
$netlock_grid           = '';
$snail_dist      = [];    # int_board, from snail target
$snail_chain     = '';
$snail_chain_len = 0;
$forbidden_push_tunnel = '';
$forbidden_pull_tunnel = '';
# Deadlock pattern tables, PRECOMPUTED (wave 2, 2026-08-21): the same
# rotations + dedup the C original ran over its pattern .txt files at
# startup, executed ONCE by devel/gen_ff_patterns.pl over the pristine
# port and frozen here as literals. cells = the non-wildcard cells of
# each pattern, row-major: [dy, dx, expected byte].
@patterns = (
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,1],[0,1,2],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,2],[3,1,1],[3,2,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[0,3,1],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,0,1],[2,1,2],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,1],[0,1,1],[1,0,2],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,1],[3,1,2],[3,2,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 0, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[0,3,1],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,0,1],[2,1,1],[2,2,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,2],[0,2,1],[1,0,2],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,1],[3,0,1],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 3, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,2],[0,2,2],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,1,1],[2,2,1],[2,3,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,2],[3,0,1],[3,1,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,1],[0,2,1],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,1,2],[2,2,2],[2,3,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,0,2],[2,1,1],[2,2,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,2],[0,1,2],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,2],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[0,3,2],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,1,2],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,2],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,1],[3,1,2],[3,2,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,1,1],[2,2,1],[2,3,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,2],[3,0,2],[3,1,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,2],[0,1,1],[0,2,1],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,1,2],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,2],[0,2,2],[1,0,2],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,1],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 0, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,0,1],[2,1,1],[2,2,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,1],[0,1,2],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,2],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[0,3,1],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,1,2],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,2],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,1],[3,1,2],[3,2,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 3, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,1,1],[2,2,1],[2,3,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,2],[3,0,1],[3,1,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,1],[0,2,1],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,1,2],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,2],[0,2,1],[1,0,2],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,1],[3,1,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,1],[0,1,1],[1,0,2],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,1],[3,0,2],[3,1,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 0, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,2],[0,1,2],[0,2,2],[0,3,1],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,1,1],[2,2,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,2],[0,2,2],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,2],[3,1,1],[3,2,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,0,1],[2,1,2],[2,2,2],[2,3,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,2],[3,1,2],[3,2,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,0,2],[2,1,2],[2,2,2],[2,3,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,2],[0,1,2],[1,0,2],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,1],[3,0,1],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 3, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,2],[0,2,2],[0,3,2],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,1,1],[2,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,0],[2,3,2],[3,1,1],[3,2,1],[3,3,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,0,1],[2,1,0],[2,2,2],[3,0,1],[3,1,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,1],[0,2,1],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,1,2],[2,2,0],[2,3,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,2,2],[0,3,1],[1,1,2],[1,2,0],[1,3,1],[2,0,1],[2,1,0],[2,2,0],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,2,1],[1,1,2],[1,2,0],[1,3,1],[2,0,2],[2,1,0],[2,2,0],[2,3,1],[3,0,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,2],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,0],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[0,3,1],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,0,1],[2,1,0],[2,2,2],[3,1,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,1,2],[2,2,0],[2,3,1],[3,2,2],[3,3,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,0],[2,3,2],[3,1,1],[3,2,1],[3,3,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,0,1],[2,1,0],[2,2,2],[3,0,2],[3,1,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,2],[0,1,1],[0,2,1],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,1,2],[2,2,0],[2,3,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,2,2],[0,3,2],[1,1,2],[1,2,0],[1,3,1],[2,0,1],[2,1,0],[2,2,0],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,2,1],[1,1,2],[1,2,0],[1,3,1],[2,0,2],[2,1,0],[2,2,0],[2,3,1],[3,0,2],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,2],[0,1,2],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,0],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[0,3,2],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,0,1],[2,1,0],[2,2,2],[3,1,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,1,2],[2,2,0],[2,3,1],[3,2,2],[3,3,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 1, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,1],[0,2,1],[0,3,1],[1,0,2],[1,1,0],[1,2,0],[1,3,2],[2,1,2],[2,2,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,2],[0,2,1],[1,0,2],[1,1,0],[1,2,1],[2,0,1],[2,1,0],[2,2,1],[3,1,2],[3,2,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 3, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,2],[1,0,2],[1,1,0],[1,2,0],[1,3,2],[2,0,1],[2,1,1],[2,2,1],[2,3,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,1],[0,1,2],[1,0,1],[1,1,0],[1,2,1],[2,0,1],[2,1,0],[2,2,2],[3,0,1],[3,1,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,1],[0,2,1],[0,3,1],[1,0,2],[1,1,0],[1,2,0],[1,3,2],[2,1,1],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,2],[0,2,1],[1,0,1],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,1],[3,1,2],[3,2,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 3, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,1],[1,0,2],[1,1,0],[1,2,0],[1,3,2],[2,0,1],[2,1,1],[2,2,1],[2,3,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,1],[0,1,2],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,1],[3,0,1],[3,1,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,2],[0,3,1],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,0,1],[2,1,0],[2,2,0],[2,3,2],[3,1,1],[3,2,1],[3,3,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,0,1],[2,1,0],[2,2,0],[2,3,2],[3,0,1],[3,1,2],[3,2,2],[3,3,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,1],[0,2,1],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,0,2],[2,1,0],[2,2,0],[2,3,1],[3,0,1],[3,1,2],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,2],[0,2,2],[0,3,1],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,0,1],[2,1,0],[2,2,0],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,2],[0,2,1],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,0,2],[2,1,0],[2,2,0],[2,3,1],[3,0,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,2],[0,2,2],[0,3,1],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,0,1],[2,1,0],[2,2,0],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[0,3,1],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,0,1],[2,1,0],[2,2,0],[2,3,2],[3,1,1],[3,2,2],[3,3,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,0,2],[2,1,0],[2,2,0],[2,3,1],[3,0,1],[3,1,2],[3,2,2],[3,3,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,2],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,1],[3,0,2],[3,1,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,2],[0,1,1],[0,2,2],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,1,1],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,2],[0,2,2],[1,0,1],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,2],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,1],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,1,2],[2,2,1],[2,3,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,2],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,1],[3,1,2],[3,2,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,2],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,0,2],[2,1,1],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,2],[0,1,2],[1,0,1],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,2],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 1, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,1],[0,3,2],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,1,2],[2,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[1,0,1],[1,1,0],[1,2,2],[1,3,1],[2,0,1],[2,1,0],[2,2,0],[2,3,2],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,0,1],[2,1,0],[2,2,2],[3,1,2],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,0,1],[2,1,2],[2,2,0],[2,3,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,2],[1,1,2],[1,2,0],[1,3,1],[2,0,1],[2,1,0],[2,2,0],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,2,1],[1,0,1],[1,1,2],[1,2,0],[1,3,1],[2,0,2],[2,1,0],[2,2,0],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,1],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,0],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,0,1],[2,1,0],[2,2,2],[2,3,1],[3,1,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,1,2],[2,2,0],[2,3,1],[3,1,1],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,2],[0,2,2],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,0],[2,3,1],[3,0,1],[3,1,2],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,1],[0,2,1],[0,3,1],[1,0,2],[1,1,0],[1,2,0],[1,3,2],[2,0,2],[2,1,0],[2,2,2],[2,3,2],[3,1,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[0,3,1],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,1,2],[2,2,0],[2,3,1],[3,1,2],[3,2,2],[3,3,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,2,1],[1,0,2],[1,1,2],[1,2,0],[1,3,2],[2,0,2],[2,1,0],[2,2,0],[2,3,2],[3,0,1],[3,1,1],[3,2,1],[3,3,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[0,3,1],[1,1,2],[1,2,0],[1,3,1],[2,0,1],[2,1,0],[2,2,0],[2,3,1],[3,1,2],[3,2,2],[3,3,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[1,0,2],[1,1,0],[1,2,2],[1,3,2],[2,0,2],[2,1,0],[2,2,0],[2,3,2],[3,0,1],[3,1,1],[3,2,1],[3,3,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,2],[0,2,2],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,0,1],[2,1,0],[2,2,2],[3,0,1],[3,1,2],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,1],[0,2,1],[0,3,1],[1,0,2],[1,1,0],[1,2,0],[1,3,2],[2,0,2],[2,1,2],[2,2,0],[2,3,2],[3,2,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,1],[0,3,1],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,1,2],[2,2,2],[2,3,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,2],[1,1,0],[1,2,2],[2,0,2],[2,1,0],[2,2,1],[3,0,1],[3,1,2],[3,2,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,2],[0,2,2],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,0,1],[2,1,1],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,1],[0,1,2],[0,2,1],[1,0,1],[1,1,0],[1,2,2],[2,0,2],[2,1,0],[2,2,2],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,1],[0,2,2],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,0,1],[2,1,2],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,1],[0,1,2],[0,2,1],[1,0,2],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,2],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 1, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[0,3,1],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,1,2],[2,2,1],[2,3,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,2],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,2],[3,0,1],[3,1,2],[3,2,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,2],[0,2,2],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,0,1],[2,1,2],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,1],[0,1,1],[0,2,1],[1,0,2],[1,1,0],[1,2,2],[2,0,2],[2,1,0],[2,2,2],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[0,3,1],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,1,2],[2,2,2],[2,3,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,2],[1,1,0],[1,2,2],[2,0,2],[2,1,0],[2,2,2],[3,0,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,2],[0,1,1],[0,2,1],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,0,2],[2,1,0],[2,2,2],[2,3,1],[3,1,2],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[0,3,2],[1,0,2],[1,1,0],[1,2,0],[1,3,1],[2,0,2],[2,1,2],[2,2,0],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[1,0,1],[1,1,2],[1,2,0],[1,3,2],[2,0,1],[2,1,0],[2,2,0],[2,3,2],[3,1,1],[3,2,1],[3,3,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,2],[1,3,2],[2,0,1],[2,1,0],[2,2,0],[2,3,2],[3,0,2],[3,1,2],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[0,3,2],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,0,1],[2,1,2],[2,2,0],[2,3,2],[3,1,2],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,2],[1,1,2],[1,2,0],[1,3,1],[2,0,2],[2,1,0],[2,2,0],[2,3,1],[3,1,2],[3,2,2],[3,3,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[1,0,2],[1,1,0],[1,2,2],[1,3,1],[2,0,2],[2,1,0],[2,2,0],[2,3,1],[3,0,2],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,0,2],[0,1,2],[0,2,2],[1,0,1],[1,1,0],[1,2,0],[1,3,2],[2,0,1],[2,1,0],[2,2,2],[2,3,2],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,1],[0,1,2],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,2],[3,0,1],[3,1,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,1],[0,2,1],[0,3,1],[1,0,2],[1,1,0],[1,2,0],[1,3,2],[2,1,2],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,2],[0,2,1],[1,0,2],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,1],[3,1,2],[3,2,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 3, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[1,0,2],[1,1,0],[1,2,0],[1,3,2],[2,0,1],[2,1,1],[2,2,1],[2,3,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,1],[1,1,0],[1,2,2],[2,0,1],[2,1,0],[2,2,2],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,1,2],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,2],[1,1,0],[1,2,1],[2,0,2],[2,1,0],[2,2,1],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 0, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[1,0,1],[1,1,0],[1,2,0],[1,3,1],[2,1,1],[2,2,1]]},
);
@pull_patterns = (
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,1,2],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,2],[1,1,8],[1,2,1],[2,0,2],[2,1,8],[2,2,1],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 0, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,1,1],[2,2,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,1],[1,1,8],[1,2,2],[2,0,1],[2,1,8],[2,2,2],[3,1,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[1,0,1],[1,1,8],[1,2,2],[2,0,1],[2,1,8],[2,2,8],[2,3,2],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,0,1],[2,1,8],[2,2,2],[3,1,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,2],[1,1,8],[1,2,8],[1,3,1],[2,1,2],[2,2,8],[2,3,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,2,2],[1,1,2],[1,2,8],[1,3,1],[2,0,1],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,2,1],[1,1,2],[1,2,8],[1,3,1],[2,0,2],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[1,0,1],[1,1,8],[1,2,2],[2,0,1],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,2],[2,0,1],[2,1,8],[2,2,2],[3,1,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,1,2],[2,2,8],[2,3,1],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[1,0,1],[1,1,8],[1,2,2],[2,0,1],[2,1,8],[2,2,8],[2,3,2],[3,1,1],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,0,2],[2,1,8],[2,2,2],[3,1,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,1],[1,0,2],[1,1,8],[1,2,8],[1,3,1],[2,1,2],[2,2,8],[2,3,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,2,2],[1,1,2],[1,2,8],[1,3,2],[2,0,1],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,2,1],[1,1,2],[1,2,8],[1,3,1],[2,0,2],[2,1,8],[2,2,8],[2,3,1],[3,1,2],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[1,0,2],[1,1,8],[1,2,2],[2,0,1],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,2],[1,0,1],[1,1,8],[1,2,8],[1,3,2],[2,0,1],[2,1,8],[2,2,2],[3,1,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,1,2],[2,2,8],[2,3,2],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,2],[2,0,1],[2,1,8],[2,2,2],[3,1,1],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,0,2],[2,1,2],[2,2,8],[2,3,1],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,1],[1,1,2],[1,2,8],[1,3,1],[2,0,2],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[1,0,1],[1,1,8],[1,2,2],[1,3,2],[2,0,1],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,2],[1,1,8],[1,2,8],[1,3,1],[2,1,2],[2,2,8],[2,3,1],[3,1,2],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,2,2],[1,0,2],[1,1,2],[1,2,8],[1,3,1],[2,0,1],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,2],[1,0,1],[1,1,8],[1,2,2],[2,0,1],[2,1,8],[2,2,8],[2,3,2],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,0,1],[2,1,8],[2,2,2],[2,3,2],[3,1,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,2],[2,0,1],[2,1,8],[2,2,8],[2,3,2],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,0,1],[2,1,8],[2,2,8],[2,3,1],[3,1,2],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,2],[1,1,8],[1,2,8],[1,3,1],[2,0,2],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 0, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,0,1],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 3, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[1,0,2],[1,1,8],[1,2,8],[1,3,2],[2,0,1],[2,1,1],[2,2,1],[2,3,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,0,1],[0,1,2],[1,0,1],[1,1,8],[1,2,2],[2,0,1],[2,1,8],[2,2,2],[3,0,1],[3,1,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,0,1],[0,1,1],[0,2,1],[0,3,1],[1,0,2],[1,1,8],[1,2,8],[1,3,2],[2,1,2],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,2],[0,2,1],[1,0,2],[1,1,8],[1,2,1],[2,0,2],[2,1,8],[2,2,1],[3,1,2],[3,2,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 3, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,2],[2,1,1],[2,2,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,1],[1,1,8],[1,2,2],[2,0,1],[2,1,8],[2,2,1],[3,1,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,2],[1,1,8],[1,2,8],[1,3,1],[2,1,1],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,2],[1,0,1],[1,1,8],[1,2,1],[2,0,2],[2,1,8],[2,2,1],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 0, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,2],[1,0,2],[1,1,8],[1,2,8],[1,3,1],[2,1,1],[2,2,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,2],[1,0,1],[1,1,8],[1,2,1],[2,0,1],[2,1,8],[2,2,2],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 1, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,2],[2,1,2],[2,2,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,2],[1,1,8],[1,2,1],[2,0,1],[2,1,8],[2,2,1],[3,1,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 3, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[1,0,1],[1,1,8],[1,2,8],[1,3,2],[2,1,1],[2,2,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,1],[1,1,8],[1,2,2],[2,0,1],[2,1,8],[2,2,2],[3,1,2]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,2],[1,1,8],[1,2,8],[1,3,1],[2,1,2],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,2],[1,0,2],[1,1,8],[1,2,1],[2,0,2],[2,1,8],[2,2,1],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 0, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,2],[1,0,2],[1,1,8],[1,2,8],[1,3,1],[2,1,1],[2,2,1]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,2],[1,0,1],[1,1,8],[1,2,2],[2,0,1],[2,1,8],[2,2,2],[3,1,1]]},
    {'y' => 3, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 2, 'maxcy' => 2, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,2],[2,1,2],[2,2,2]]},
    {'y' => 4, 'x' => 3, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 2, 'cells' => [[0,1,1],[1,0,2],[1,1,8],[1,2,1],[2,0,2],[2,1,8],[2,2,1],[3,1,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,2],[2,0,1],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,2],[2,0,1],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 2, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,0,2],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,2]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,2],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,0,2],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 1, 'box_shift_x' => 0, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,2],[1,0,2],[1,1,8],[1,2,8],[1,3,1],[2,0,1],[2,1,8],[2,2,8],[2,3,1],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 2, 'box_shift_x' => 3, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,2],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,0,1],[2,1,8],[2,2,8],[2,3,2],[3,1,1],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,1],[1,1,8],[1,2,8],[1,3,1],[2,0,1],[2,1,8],[2,2,8],[2,3,2],[3,1,2],[3,2,1]]},
    {'y' => 4, 'x' => 4, 'box_shift_y' => 3, 'box_shift_x' => 1, 'maxcy' => 3, 'maxcx' => 3, 'cells' => [[0,1,1],[0,2,1],[1,0,2],[1,1,8],[1,2,8],[1,3,1],[2,0,1],[2,1,8],[2,2,8],[2,3,1],[3,1,2],[3,2,1]]},
);
@square_place_y = ([-2, -2], [-1, 0], [1, 1], [-1, 0]);
@square_place_x = ([-1, 0], [1, 1], [-1, 0], [-2, -2]);
$distance_from_to     = '';
$bfs_distance_from_to = '';
$blocks_place      = '';
$completely_blocks = '';
$mpdb_board = '';
$pull_mpdb_board = '';

# THE LEVEL ANALYSIS IS DONE ONCE PER LEVEL, NOT ONCE PER solve().
#
# preprocess_level builds a dozen maps that are a property of the LEVEL --
# distance tables, rooms, hotspots, both pair-deadlock tables, envelopes,
# tunnels -- and solve() used to rebuild all of them on every call. On the
# bigger levels that is 13 seconds and more, and a portfolio that runs eight
# modes over one game paid it eight times (measured 2026-08-22: a third of an
# eight-mode portfolio's whole wall clock, 54 % on one game).
#
# $Analysed_key names the level whose analysis is currently loaded. It is the
# incoming board plus the row width, which is the entire input the analysis has
# -- proved rather than assumed (in the Sokoban project, where the analysis was
# stored: analysing other levels in between changed nothing of a level's).
$Analysed_key = '';

# The two fuses of the analysis, read by parse() into the hash. init_hotspots
# gives itself a quarter of the time limit and, if it runs out, THROWS ITS OWN
# TABLE AWAY rather than finishing it; the envelope analysis stops after half.
# Both verdicts depend on the wall clock, so an analysis that lost them is not
# the analysis the level deserves -- it is an accident of how busy the machine
# was, and the hash says so.
$Hotspots_incomplete  = 0;
$Envelopes_incomplete = 0;
$girl_distance = [];    # int_board, from targets
$max_push_dist = 0;
$inv_n_boxes     = 0;
$dist_normalizer = 0;


# ====================================================================
# Games::Sokoban::Fest::Global  (was lib2/Games/Sokoban/Fest/Global.pm)
# ====================================================================

# Port of festival/global.h + global.cpp (Festival 3.1, Yaron Shoham).
# Literal transcription phase (see the Fest port plan): same names, same
# values. C file-scope globals become exported package variables, so every
# Fest module does 'use Global' the way every C file
# includes global.h.
#
# Representation decisions fixed for the whole port (dynamic sizing since
# Board.pm v0.02 -- nothing is dimensioned by the MAX_* constants):
#   - C 'board' (unsigned char[MAX_SIZE][MAX_SIZE]) = ONE Perl string of
#     exactly $height * $width bytes, row stride $width; cell access
#     vec($brd, $y * $width + $x, 8). Geometry state ($ncells, @delta_p,
#     masks) is rebuilt per level by Fest::Board::init_board_geometry().
#   - C 'int_board' = flat Perl array(ref) of $ncells ints, same indexing.
#   - Huge int matrices (ncells x ncells distance tables etc.) = packed
#     strings, decided per module when they appear.
#   - MAX_SIZE / MAX_BOXES / MAX_SOL_LEN survive ONLY as refusal limits
#     mirroring the C exe's behavior (needed while the equivalence gate
#     diffs against it); dropping a limit later = deleting one check.

# cell bit flags

# search modes

# globals from global.cpp (same initial values)

($global_initial_sokoban_y, $global_initial_sokoban_x) = (0, 0);

($start_time, $end_time) = (0, 0);

# ====================================================================
# Games::Sokoban::Fest::Util  (was lib2/Games/Sokoban/Fest/Util.pm)
# ====================================================================

# Port of festival/util.cpp (Festival 3.1, Yaron Shoham).
# Deviations from the C original, all deliberate:
#   - errors confess (Carp) instead of printf+getch+exit (tripwire
#     style, same as is_bad's UNKNOWN pattern confess).
#   - my_getch() is a no-op: the C version pauses interactive verbose>=5
#     debugging; the port never blocks on the keyboard.
#   - the string trimmers, the timestamp formatters and the core counter
#     are GONE: they served the level-set file reader, the solution log
#     and the thread pool, none of which this port has.
#
# Globals ledger:
#   reads:  $height $width Board::$initial_board
#   writes: nothing

# byte-sequence prefix compare; a and b are packed byte strings
# a = int_board (flat arrayref of $ncells ints)

# group_size kept from C: callers may pass a prefix of a larger buffer
sub in_group ($val, $group, $group_size) {
    for my $i (0 .. $group_size - 1) {
        return 1 if $group->[$i] == $val;
    }
    return 0;
}

# dist = int_board (flat arrayref); reads Fest::Board's initial_board


# cyclic level = no plain box and no plain target cell on the initial board
# (boxes all start ON targets); exact-value byte search, whole string is
# the active region


# ====================================================================
# Games::Sokoban::Fest::Board  (was lib2/Games/Sokoban/Fest/Board.pm)
# ====================================================================

# Port of festival/board.cpp (Festival 3.1, Yaron Shoham).
#
# Representation (v0.02, first PRELOZIT step -- dynamic sizing):
#   board = ONE Perl string of exactly $height * $width bytes, row stride
#   $width; cell = vec($brd, $y * $width + $x, 8). No fixed 51x51 buffer and
#   no padding: the string IS the active region, so whole-string ops
#   (copy, eq, masks, hash, popcnt) cover exactly what the C active-region
#   loops cover, and storing a position is a plain string copy (the C
#   original's compact serialization has nothing left to do -- that is why
#   board_to_bytes/bytes_to_board are gone).
#   Geometry-derived state ($ncells, @delta_p, masks) is rebuilt
#   once per level by init_board_geometry(), called from
#   set_board_from_code() -- the single place where a new level's
#   height/width enter the system.
#
# Calling conventions (signature rework 2026-08-21): every sub has a
# signature; argument aliasing is gone. A sub that mutates a board
# takes it and RETURNS it ($b = f($b, ...)); flag-and-board subs
# return (flag, board); out-parameters became return values. The only
# refs left are recursion accumulators (biconnect_dfs) and real refs.
#
# Globals ledger (the workflow map -- kept current in every Fest module):
#   reads:  $height $width (set by set_board_from_code)
#   writes: $ncells @delta_p (init_board_geometry)
#           $initial_board $global_initial_sokoban_y/_x
#           $global_boxes_in_level (save_initial_board)
#           $inner (init_inner), $index_num (init_index_x_y)

# whole-string bit masks for single-bit ops, sized to the current level

# file-scope index tables
# inner index -> flat cell position (y * $width + x). Exported since v0.04:
# the P1 lookup-instead-of-recompute swap is useful outside this module too
# (Hotspot), and an accessor sub would cost exactly what P1 saves.

# not in the C original: rebuild all geometry-derived state for the level
# whose $height/$width are currently set
sub init_board_geometry () {
    for my $d (0 .. 3) {
        $square_place_p[$d] = [
            map {$square_place_y[$d][$_] * $width + $square_place_x[$d][$_]} 0, 1];
    }
    Carp::confess('init_board_geometry: no level dimensions')
        if $height == 0 or $width == 0;

    $ncells    = $height * $width;
    @delta_p   = (-$width, 1, $width, -1);    # up right down left
    @delta_p_8 = map {$delta_y_8[$_] * $width + $delta_x_8[$_]} 0 .. 7;

    $ZERO_BOARD  = "\0" x $ncells;
    $NOT_BOX     = chr(0xFF ^ BOX)     x $ncells;
    $NOT_SOKOBAN = chr(0xFF ^ SOKOBAN) x $ncells;
    $NOT_TARGET  = chr(0xFF ^ TARGET)  x $ncells;
    $NOT_BASE    = chr(0xFF ^ BASE)    x $ncells;
    $BOX_ONLY    = chr(BOX)            x $ncells;
    $SOK_ONLY    = chr(SOKOBAN)        x $ncells;
    return;
}

# not in the C original: fresh all-zero board for Perl locals ('board c;')
sub save_initial_board ($brd) {
    $initial_board = $brd;
    my $sok_p = get_sokoban_position($brd);
    $global_initial_sokoban_y = int($sok_p / $width);
    $global_initial_sokoban_x = $sok_p % $width;
    $global_boxes_in_level = (($brd &. $BOX_ONLY) =~ tr/\x00//c);
    return;
}

sub get_sokoban_position ($brd) {    # returns the flat cell position
    my $t = $brd &. $SOK_ONLY;
    return $-[0] if $t =~ /[^\0]/;
    Carp::confess("sokoban not found\n");
}

sub init_inner ($brd) {
    my $c;
    $c = $brd &. $NOT_BOX;
    $c = expand_sokoban_cloud($c);

    # inner = 1 wherever the cloud reached (SOKOBAN bit -> 1)
    ($inner = $c &. $SOK_ONLY) =~ tr/\x08/\x01/;
    return;
}

sub index_to_y_x ($index) {    # returns (y, x)
    if ($index < 0 or $index >= $index_num) {
        Carp::confess("index_error: $index of $index_num");
    }
    return ($index_to_y[$index], $index_to_x[$index]);
}

sub init_index_x_y () {
    $index_num          = 0;
    @y_x_to_index_table = (-1) x $ncells;
    @index_to_x         = ();
    @index_to_y         = ();
    @index_to_p         = ();

    for my $p (0 .. $ncells - 1) {
        next if vec($inner, $p, 8) == 0;

        $y_x_to_index_table[$p] = $index_num;
        $index_to_x[$index_num] = $p % $width;
        $index_to_y[$index_num] = int($p / $width);
        $index_to_p[$index_num] = $p;
        $index_num++;
    }
    return;
}

sub turn_boxes_into_walls ($brd) {
    for my $p (0 .. $ncells - 1) {
        vec($brd, $p, 8) = WALL if vec($brd, $p, 8) & BOX;
    }
    return $brd;
}

sub expand_sokoban_cloud ($brd) {
    my @queue;

    # init queue from existing sokoban positions
    for my $p (0 .. $ncells - 1) {
        push @queue, $p if vec($brd, $p, 8) & SOKOBAN;
    }

    my $queue_pos = 0;
    while ($queue_pos < @queue) {
        my $p = $queue[$queue_pos];
        for my $i (0 .. 3) {
            my $next = $p + $delta_p[$i];
            next if vec($brd, $next, 8) & SOKOBAN;
            next if vec($brd, $next, 8) & OCCUPIED;
            vec($brd, $next, 8) |= SOKOBAN;
            push @queue, $next;
        }
        $queue_pos++;
    }
    return $brd;
}

# verbatim duplicate in the C original

sub get_board_hash ($brd) {
    # multiplicative rolling hash relying on unsigned 64-bit wraparound in
    # C. 'use integer' gives the same wrapping bit patterns (signed two's
    # complement); the right shift must be masked because it sign-extends
    # under 'use integer'. The result is a signed IV whose BITS match the C
    # UINT_64 (print with sprintf '%016x'). The string is exactly the
    # active region, so hashing every byte matches the C cell order.
    use integer;
    my $hash = 1;
    for my $c (unpack 'C*', $brd) {
        $hash = $hash * 12345 + $c + (($hash >> 32) & 0xFFFFFFFF);
    }
    return $hash;
}

sub all_boxes_in_place ($brd, $pull_mode) {
    for my $p (0 .. $ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;

        if ($pull_mode == 0) {
            return 0 if (vec($brd, $p, 8) & TARGET) == 0;
        }
        else {
            # don't use BASES because they don't exist in paper mode
            return 0 if (vec($initial_board, $p, 8) & BOX) == 0;
        }
    }
    return 1;
}

sub board_is_solved ($brd, $pull_mode) {
    if ($pull_mode) {
        my $p = $global_initial_sokoban_y * $width + $global_initial_sokoban_x;
        return 0 if (vec($brd, $p, 8) & SOKOBAN) == 0;
    }
    return all_boxes_in_place($brd, $pull_mode);
}

sub enter_reverse_mode ($brd, $mark_bases) {

    $brd &.= $NOT_SOKOBAN;

    for my $p (0 .. $ncells - 1) {
        my $c = vec($brd, $p, 8);

        vec($brd, $p, 8) = 0            if $c == BOX;
        vec($brd, $p, 8) = BOX | TARGET if $c == TARGET;

        if ($mark_bases) {
            vec($brd, $p, 8) |= BASE if vec($initial_board, $p, 8) & BOX;
        }
    }
    return $brd;
}


sub boxes_on_bases ($brd) {
    my $sum = 0;
    for my $p (0 .. $ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;
        $sum++ if vec($initial_board, $p, 8) & BOX;
    }
    return $sum;
}


sub negate_board ($brd) {
    for my $p (0 .. $ncells - 1) {
        Carp::confess('bad neg value') if vec($brd, $p, 8) > 1;
        vec($brd, $p, 8) = 1 - vec($brd, $p, 8);
    }
    return $brd;
}


sub go_to_final_position_with_given_walls ($brd) {
    for my $p (0 .. $ncells - 1) {
        my $c = vec($brd, $p, 8);
        next if $c == WALL;

        if   ($c & TARGET) {vec($brd, $p, 8) |= BOX;}
        else               {vec($brd, $p, 8) &= 0xFF ^ BOX;}
    }
    return $brd;
}

sub put_sokoban_everywhere ($brd) {
    for my $i (0 .. $index_num - 1) {
        my $p = $index_to_p[$i];
        vec($brd, $p, 8) |= SOKOBAN if (vec($brd, $p, 8) & OCCUPIED) == 0;
    }
    return $brd;
}

sub put_sokoban_in_zone ($brd, $zones, $z) {

    $brd &.= $NOT_SOKOBAN;
    for my $p (0 .. $ncells - 1) {
        next unless $zones->[$p] == $z;
        vec($brd, $p, 8) |= SOKOBAN if (vec($brd, $p, 8) & OCCUPIED) == 0;
    }
    $brd = expand_sokoban_cloud($brd);
    return $brd;
}

sub get_untouched_areas ($brd) {
    my $untouched = $ZERO_BOARD;
    for my $p (0 .. $ncells - 1) {
        next if vec($inner, $p, 8) == 0;
        next if vec($brd, $p, 8) & OCCUPIED;
        vec($untouched, $p, 8) = 1 if (vec($brd, $p, 8) & SOKOBAN) == 0;
    }
    return $untouched;
}


# ====================================================================
# Games::Sokoban::Fest::DeadlockCache  (was lib2/Games/Sokoban/Fest/DeadlockCache.pm)
# ====================================================================

# Port of festival/deadlock_cache.cpp (Festival 3.1, Yaron Shoham).
# The shared transposition cache of deadlock verdicts, keyed by (board
# hash, pull_mode, alg); result -1 = unknown, 0/1 = verdict, 2 = "being
# computed" (upgradable). REPRESENTATION: the C open-addressed table is a
# hash map -- here %cache keyed by "hash/pull/alg", value [result,
# queries]. The capacity fuse survives with the C sizing (2^22 entries at
# 1 core, half-full limit). The C mutex is gone with the threads.
# The "different cache value!" tripwire ((old ^ new) == 1) is kept.
#
# Globals ledger:
#   reads: 
#   writes: %cache $total_deadlock_cache_entries $log_deadlock_cache


sub deadlock_cache_is_full () {
    my $limit = 1 << ($log_deadlock_cache - 1);
    return 0 if $total_deadlock_cache_entries < $limit;
    return 1;
}

sub insert_to_deadlock_cache ($hash, $res, $pull_mode, $alg) {
    return if deadlock_cache_is_full();

    my $key = "$hash/$pull_mode/$alg";
    my $e   = $cache{$key};

    if (defined $e) {    # already in cache
        Carp::confess('different cache value!') if ($e->[0] ^ $res) == 1;

        $e->[0] = $res if $e->[0] == 2;
    }
    else {
        $cache{$key} = [$res, 0];
        $total_deadlock_cache_entries++;
    }
    return;
}

# ====================================================================
# Games::Sokoban::Fest::Hungarian  (was lib2/Games/Sokoban/Fest/Hungarian.pm)
# ====================================================================

# Port of festival/hungarian.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. The Hungarian assignment algorithm (min-cost
# perfect matching boxes -> targets) with the incremental cache: when the
# new cost matrix differs from the previous one in AT MOST one row, the
# previous potentials/matching are reused and only that row is re-matched
# (did_one_row_change / init_from_prev); an identical matrix returns the
# cached solution outright.
# Data shapes: cost matrix = arrayref of arrayrefs (box_mat); solution =
# hashref {V, U, matched_v, matched_u (arrayrefs), weight}; cache = hashref
# {prev_c, prev_sol, prev_n}. C struct copies become deep copies.
# solve_hungarian FILLS the caller's solution hashref (C shape).
#
# Globals ledger: nothing global (everything through the arguments).

sub set_hungarian_problem ($size, $mat, $hd) {
    my $n = $hd->{'n'} = $size;
    for my $i (0 .. $n - 1) {
        for my $j (0 .. $n - 1) {
            $hd->{'c'}[$i][$j] = $mat->[$i][$j];
        }
    }
    return;
}

sub init_U_V ($hd) {
    my $n = $hd->{'n'};
    my $V = $hd->{'V'} = [];
    my $U = $hd->{'U'} = [];

    for my $i (0 .. $n - 1) {
        my $min = 10000000;
        for my $j (0 .. $n - 1) {
            $min = $hd->{'c'}[$i][$j] if $hd->{'c'}[$i][$j] < $min;
        }
        $V->[$i] = $min;
    }

    for my $j (0 .. $n - 1) {
        my $min = 10000000;
        for my $i (0 .. $n - 1) {
            $min = $hd->{'c'}[$i][$j] - $V->[$i]
                if $hd->{'c'}[$i][$j] - $V->[$i] < $min;
        }
        $U->[$j] = $min;
    }
    return;
}

sub init_match ($hd) {
    my $n         = $hd->{'n'};
    my $matched_v = $hd->{'matched_v'} = [];
    my $matched_u = $hd->{'matched_u'} = [];
    my $V         = $hd->{'V'};
    my $U         = $hd->{'U'};

    $hd->{'match_size'} = 0;

    for my $i (0 .. $n - 1) {
        $matched_v->[$i] = -1;
        $matched_u->[$i] = -1;
    }

    for my $i (0 .. $n - 1) {
        for my $j (0 .. $n - 1) {
            next if $matched_u->[$j] != -1;

            if ($hd->{'c'}[$i][$j] == $V->[$i] + $U->[$j]) {
                $matched_v->[$i] = $j;
                $matched_u->[$j] = $i;
                $hd->{'match_size'}++;
                last;    # j iteration
            }
        }
    }
    return;
}

sub init_hungarian_bfs ($hd) {
    my $n = $hd->{'n'};

    $hd->{'v_list_num'} = 0;
    $hd->{'u_list_num'} = 0;

    for my $i (0 .. $n - 1) {
        $hd->{'src_of_v'}[$i]  = -1;
        $hd->{'src_of_u'}[$i]  = -1;
        $hd->{'visited_v'}[$i] = 0;
        $hd->{'visited_u'}[$i] = 0;
    }

    for my $i (0 .. $n - 1) {
        if ($hd->{'matched_v'}[$i] == -1) {
            $hd->{'v_list'}[$hd->{'v_list_num'}++] = $i;
            $hd->{'visited_v'}[$i] = 1;
        }
    }
    return;
}

sub bfs_v_side ($hd) {
    my $changed = 0;
    my $n       = $hd->{'n'};

    $hd->{'u_list_num'} = 0;

    for my $t (0 .. $hd->{'v_list_num'} - 1) {
        my $i = $hd->{'v_list'}[$t];

        for my $j (0 .. $n - 1) {
            next if $hd->{'visited_u'}[$j];

            if ($hd->{'V'}[$i] + $hd->{'U'}[$j] == $hd->{'c'}[$i][$j]) {
                $hd->{'visited_u'}[$j] = 1;
                $hd->{'src_of_u'}[$j]  = $i;
                $hd->{'u_list'}[$hd->{'u_list_num'}++] = $j;
                $changed = 1;
            }
        }
    }
    return $changed;
}

sub bfs_u_side ($hd) {
    my $changed = 0;

    $hd->{'v_list_num'} = 0;
    for my $t (0 .. $hd->{'u_list_num'} - 1) {
        my $j = $hd->{'u_list'}[$t];

        next if $hd->{'matched_u'}[$j] == -1;

        my $i = $hd->{'matched_u'}[$j];

        next if $hd->{'visited_v'}[$i] == 1;

        $hd->{'v_list'}[$hd->{'v_list_num'}++] = $i;
        $hd->{'visited_v'}[$i] = 1;
        $hd->{'src_of_v'}[$i]  = $j;
        $changed = 1;
    }
    return $changed;
}

sub hungarian_bfs ($side, $hd) {    # v = side 0
    my $res;

    do {
        if ($side == 0) {
            Carp::confess("bad hungarian v side\n") if $hd->{'v_list_num'} == 0;
            $res = bfs_v_side($hd);
        }
        else {
            Carp::confess("bad hungarian u side\n") if $hd->{'u_list_num'} == 0;
            $res = bfs_u_side($hd);
        }
        $side = 1 - $side;
    } while ($res);
    return;
}

sub try_to_increase_match ($hd) {
    my $n = $hd->{'n'};

    for my $j (0 .. $n - 1) {
        next if $hd->{'matched_u'}[$j] != -1;
        next if $hd->{'visited_u'}[$j] == 0;

        my $jj = $j;
        while ($jj != -1) {
            my $i = $hd->{'src_of_u'}[$jj];
            $hd->{'matched_u'}[$jj] = $i;
            $hd->{'matched_v'}[$i]  = $jj;
            $jj = $hd->{'src_of_v'}[$i];
        }
        return 1;
    }
    return 0;
}

sub add_new_edges ($hd) {
    my $min = 10000000;
    my $n   = $hd->{'n'};

    $hd->{'u_list_num'} = 0;

    # determine delta
    for my $i (0 .. $n - 1) {
        next if $hd->{'visited_v'}[$i] == 0;

        for my $j (0 .. $n - 1) {
            next if $hd->{'visited_u'}[$j] == 1;

            my $delta = $hd->{'c'}[$i][$j] - $hd->{'V'}[$i] - $hd->{'U'}[$j];
            $min = $delta if $delta < $min;
        }
    }

    my $delta = $min;

    # update weights
    for my $i (0 .. $n - 1) {
        $hd->{'V'}[$i] += $delta if $hd->{'visited_v'}[$i];
        $hd->{'U'}[$i] -= $delta if $hd->{'visited_u'}[$i];
    }

    # add vertices to U using new edges
    for my $j (0 .. $n - 1) {
        next if $hd->{'visited_u'}[$j];

        for my $i (0 .. $n - 1) {
            next if $hd->{'visited_v'}[$i] == 0;

            if ($hd->{'V'}[$i] + $hd->{'U'}[$j] == $hd->{'c'}[$i][$j]) {
                $hd->{'visited_u'}[$j] = 1;
                $hd->{'src_of_u'}[$j]  = $i;
                last;
            }
        }    # i

        $hd->{'u_list'}[$hd->{'u_list_num'}++] = $j if $hd->{'visited_u'}[$j];
    }    # j
    return;
}

sub verify_hungarian_invariant ($hd) {
    my $n = $hd->{'n'};

    for my $i (0 .. $n - 1) {
        for my $j (0 .. $n - 1) {
            Carp::confess("invariant failed\n")
                if $hd->{'V'}[$i] + $hd->{'U'}[$j] > $hd->{'c'}[$i][$j];
        }
    }
    return;
}

sub add_edge_to_match ($hd) {
    init_hungarian_bfs($hd);

    hungarian_bfs(0, $hd);    # side = v
    # do several v-u iterations, starting from v

    while (1) {
        return if try_to_increase_match($hd);

        add_new_edges($hd);

        hungarian_bfs(1, $hd);    # side = u
    }
}

sub verify_hungarian_solution ($hd) {
    verify_hungarian_invariant($hd);

    # confirm match
    for my $i (0 .. $hd->{'n'} - 1) {
        my $j = $hd->{'matched_v'}[$i];
        Carp::confess('not perm') if $j == -1;
        Carp::confess('not perm') if $hd->{'matched_u'}[$j] != $i;

        Carp::confess('match problem')
            if $hd->{'V'}[$i] + $hd->{'U'}[$j] != $hd->{'c'}[$i][$j];
    }
    return;
}

sub is_match_full ($hd) {
    for my $i (0 .. $hd->{'n'} - 1) {
        return 0 if $hd->{'matched_v'}[$i] == -1;
    }
    return 1;
}

sub do_hungarian_iterations ($hd) {
    while (is_match_full($hd) == 0) {
        add_edge_to_match($hd);
        verify_hungarian_invariant($hd);
    }

    verify_hungarian_solution($hd);
    return;
}

sub set_hungarian_solution ($sol, $hd) {
    $sol->{'weight'}  = 0;
    $sol->{'V'}       = [];
    $sol->{'U'}       = [];
    $sol->{'matched_v'} = [];
    $sol->{'matched_u'} = [];

    for my $i (0 .. $hd->{'n'} - 1) {
        $sol->{'matched_v'}[$i] = $hd->{'matched_v'}[$i];
        $sol->{'matched_u'}[$i] = $hd->{'matched_u'}[$i];
        $sol->{'U'}[$i]       = $hd->{'U'}[$i];
        $sol->{'V'}[$i]       = $hd->{'V'}[$i];
        $sol->{'weight'} += $hd->{'c'}[$i][$hd->{'matched_v'}[$i]];
    }
    return;
}

sub did_one_row_change ($size, $row_ref, $c, $hc) {
    my @row_changed;
    my $total = 0;

    return 0 if $size != $hc->{'prev_n'};

    for my $i (0 .. $size - 1) {
        my $same = 1;
        for my $j (0 .. $size - 1) {
            if ($c->[$i][$j] != $hc->{'prev_c'}[$i][$j]) {$same = 0; last;}
        }
        $row_changed[$i] = $same ? 0 : 1;
    }

    $total += $_ for @row_changed;

    if ($total == 0) {    # same problem !
        $$row_ref = $size;
        return 1;
    }

    return 0 if $total > 1;

    for my $i (0 .. $size - 1) {
        $$row_ref = $i if $row_changed[$i];
    }

    return 1;
}

sub init_from_prev ($row, $hd, $hc) {
    my $n = $hc->{'prev_n'};

    $hd->{'n'} = $n;

    for my $i (0 .. $n - 1) {
        $hd->{'V'}[$i]         = $hc->{'prev_sol'}{'V'}[$i];
        $hd->{'U'}[$i]         = $hc->{'prev_sol'}{'U'}[$i];
        $hd->{'matched_v'}[$i] = $hc->{'prev_sol'}{'matched_v'}[$i];
        $hd->{'matched_u'}[$i] = $hc->{'prev_sol'}{'matched_u'}[$i];
    }
    $hd->{'matched_u'}[$hd->{'matched_v'}[$row]] = -1;
    $hd->{'matched_v'}[$row] = -1;

    my $min = 10000000;
    for my $i (0 .. $n - 1) {
        $min = $hd->{'c'}[$row][$i] - $hd->{'U'}[$i]
            if $hd->{'c'}[$row][$i] - $hd->{'U'}[$i] < $min;
    }
    $hd->{'V'}[$row] = $min;

    verify_hungarian_invariant($hd);
    return;
}

sub save_prev_data ($sol, $hd, $hc) {
    my $n = $hd->{'n'};

    $hc->{'prev_n'} = $n;
    for my $i (0 .. $n - 1) {
        for my $j (0 .. $n - 1) {
            $hc->{'prev_c'}[$i][$j] = $hd->{'c'}[$i][$j];
        }
    }
    # struct copy in C -> deep copy
    $hc->{'prev_sol'} = {
        'weight'  => $sol->{'weight'},
        'V'       => [@{ $sol->{'V'} }],
        'U'       => [@{ $sol->{'U'} }],
        'matched_v' => [@{ $sol->{'matched_v'} }],
        'matched_u' => [@{ $sol->{'matched_u'} }],
    };
    return;
}

sub solve_hungarian ($n, $cost, $sol, $hc) {    # fills the $sol hashref
    my $row;

    my $hd = {'c' => []};

    set_hungarian_problem($n, $cost, $hd);

    my $one_row_changed = did_one_row_change($n, \$row, $cost, $hc);

    if ($one_row_changed == 0) {
        init_U_V($hd);
        init_match($hd);
    }
    else {
        if ($row == $n) {    # same problem
            # struct copy in C -> deep copy
            $sol->{'weight'}  = $hc->{'prev_sol'}{'weight'};
            $sol->{'V'}       = [@{ $hc->{'prev_sol'}{'V'} }];
            $sol->{'U'}       = [@{ $hc->{'prev_sol'}{'U'} }];
            $sol->{'matched_v'} = [@{ $hc->{'prev_sol'}{'matched_v'} }];
            $sol->{'matched_u'} = [@{ $hc->{'prev_sol'}{'matched_u'} }];
            return;
        }
        init_from_prev($row, $hd, $hc);
    }

    do_hungarian_iterations($hd);

    set_hungarian_solution($sol, $hd);

    # solved a new problem and not a variation
    save_prev_data($sol, $hd, $hc) if $one_row_changed == 0;
    return;
}

# ====================================================================
# Games::Sokoban::Fest::Bfs  (was lib2/Games/Sokoban/Fest/Bfs.pm)
# ====================================================================

# Port of festival/bfs.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 translation: wavefronts run over flat cell positions (@delta_p)
# instead of parallel x/y arrays; scans are single loops over $ncells.
# All results (distance values, marks, component ids) are independent of
# visit order inside a wave, so the traces cannot change.
#
# Globals ledger:
#   reads:  $width $ncells @delta_y @delta_x Board::@delta_p $inner
#   writes: nothing (all results go through arguments/returns)

sub bfs_from_place ($brd, $dist, $start_p, $ignore_boxes) {
    # do bfs, assuming "dist" is initialized

    my $occupied_mask = $ignore_boxes ? WALL : OCCUPIED;

    my @current = ($start_p);
    $dist->[$start_p] = 0;

    my $d = 0;
    while (@current) {
        my @next;
        for my $p (@current) {
            for my $delta (@delta_p) {
                my $np = $p + $delta;

                if ((vec($brd, $np, 8) & $occupied_mask) == 0
                    and $dist->[$np] == 1000000)
                {
                    $dist->[$np] = $d + 1;
                    push @next, $np;
                }
            }
        }
        $d++;
        @current = @next;
    }
    return;
}

sub get_connectivity ($brd) {
    my @dist;
    my $c = 0;

    @{(\@dist)} = (1000000) x $ncells;

    for my $p (0 .. $ncells - 1) {
        next if vec($inner, $p, 8) == 0;
        next if $dist[$p] != 1000000;
        next if vec($brd, $p, 8) & OCCUPIED;

        bfs_from_place($brd, \@dist, $p, 0);
        $c++;
    }
    return $c;
}


sub mark_connectivities ($brd, $dist) {
    my @local_dist;
    my $c = 0;

    @{$dist} = (1000000) x $ncells;

    for my $p (0 .. $ncells - 1) {
        next if vec($inner, $p, 8) == 0;
        next if $dist->[$p] != 1000000;
        next if vec($brd, $p, 8) & OCCUPIED;

        @{(\@local_dist)} = (1000000) x $ncells;
        bfs_from_place($brd, \@local_dist, $p, 0);

        for my $q (0 .. $ncells - 1) {
            $dist->[$q] = $c if $local_dist[$q] < 1000000;
        }
        $c++;
    }
    return $c;
}

sub mark_connectivities_around_place ($brd, $dist, $start_p) {
    my @local_dist;

    @{$dist} = (1000000) x $ncells;

    for my $c (0 .. 3) {
        my $p = $start_p + $delta_p[$c];

        next if vec($inner, $p, 8) == 0;
        next if $dist->[$p] != 1000000;
        next if vec($brd, $p, 8) & OCCUPIED;

        @local_dist = (1000000) x $ncells;
        bfs_from_place($brd, \@local_dist, $p, 0);

        for my $q (0 .. $ncells - 1) {
            $dist->[$q] = $c if $local_dist[$q] < 1000000;
        }
    }
    return;
}

sub get_srcs_of_all_targets ($b_in) {
    # the board configuration may change after freezing boxes.
    # find updated sources of all targets.


    my @queue;
    my $queue_place = 0;
    my ($brd, $srcs);

    $srcs = $ZERO_BOARD;
    $brd = $b_in &. $NOT_BOX;

    for my $p (0 .. $ncells - 1) {
        next if vec($inner, $p, 8) == 0;
        next if (vec($brd, $p, 8) & TARGET) == 0;
        push @queue, $p;
        vec($srcs, $p, 8) = 1;
    }

    while ($queue_place < @queue) {
        my $p = $queue[$queue_place++];

        for my $delta (@delta_p) {
            my $bp = $p + $delta;    # candidate box cell

            next if vec($brd, $bp, 8) & OCCUPIED;
            next if vec($brd, $bp + $delta, 8) & OCCUPIED;    # pull stance
            next if vec($srcs, $bp, 8);

            vec($srcs, $bp, 8) = 1;
            push @queue, $bp;
        }
    }

    return $srcs;
}

sub expand_group ($brd, $group, $dist) {

    my @current;

    for my $p (0 .. $ncells - 1) {
        $dist->[$p] = 1000000;

        if (vec($group, $p, 8)) {
            push @current, $p;
            $dist->[$p] = 0;
        }
    }

    while (@current) {
        my @next;

        for my $p (@current) {
            for my $delta (@delta_p) {
                my $np = $p + $delta;

                next if vec($group, $np, 8);
                next if vec($brd, $np, 8) & OCCUPIED;

                vec($group, $np, 8) = 1;
                push @next, $np;
                $dist->[$np] = $dist->[$p] + 1;
            }
        }

        @current = @next;
    }
    return $group;
}

# ====================================================================
# Games::Sokoban::Fest::Biconnect  (was lib2/Games/Sokoban/Fest/Biconnect.pm)
# ====================================================================

# Port of festival/biconnect.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 translation: P4 (flat positions). The depth-first walk now
# carries a flat cell position and steps via @delta_p instead of the C
# y/x pair -- the neighbour order (i = 0..3) is untouched, so the walk
# visits cells in exactly the same sequence and the recorded depths
# cannot change. The @low table is one list assignment.
# A depth-first walk marks free cells that lie on a cycle (removing them
# does NOT disconnect the area); biconnect_score() = free inner cells NOT
# on any cycle, i.e. how "corridor-like" the current position is. The walk
# recurses one level per cell -- 'recursion' warnings are disabled (depth
# legitimately reaches the free-cell count).
#
# Globals ledger:
#   reads:  $ncells @delta_p $inner $index_num $global_boxes_in_level
#   writes: nothing (results via arguments/returns)

sub biconnect_dfs ($brd, $p, $father, $d, $vr, $low, $cr) {

    vec($$vr, $p, 8) = 1;
    $low->[$p] = $d;

    for my $i (0 .. 3) {
        my $np = $p + $delta_p[$i];

        next if vec($brd, $np, 8) & OCCUPIED;
        next if vec($$vr, $np, 8);

        biconnect_dfs($brd, $np, ($i + 2) & 3, $d + 1, $vr, $low, $cr);
    }

    for my $i (0 .. 3) {
        next if $i == $father;
        my $np = $p + $delta_p[$i];
        $low->[$p] = $low->[$np] if $low->[$np] < $low->[$p];
        vec($$cr, $np, 8) = 1 if $low->[$np] < $d;
    }

    vec($$cr, $p, 8) = 1 if $low->[$p] < $d;
    return;
}


sub biconnect_score ($b_in, $report) {
    my ($brd, $visited, $on_cycle);

    $brd = $b_in;

    $visited = $ZERO_BOARD;
    $on_cycle = $ZERO_BOARD;
    my @low = (1000000) x $ncells;

    for my $p (0 .. $ncells - 1) {
        next if vec($inner, $p, 8) == 0;
        next if vec($visited, $p, 8);
        next if vec($brd, $p, 8) & OCCUPIED;

        biconnect_dfs($brd, $p, -1, 0, \$visited, \@low, \$on_cycle);
    }

    # allow pulling boxes from target areas even if it creates tunnels
    # (which increase biconnectivity)
    for my $p (0 .. $ncells - 1) {
        vec($on_cycle, $p, 8) = 1
            if (vec($brd, $p, 8) & TARGET) and (vec($brd, $p, 8) & BOX) == 0;
    }

    return $index_num - $global_boxes_in_level - unpack('%32C*', $on_cycle);
}

# ====================================================================
# Games::Sokoban::Fest::Diags  (was lib2/Games/Sokoban/Fest/Diags.pm)
# ====================================================================

# Port of festival/diags.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 pass: POD only, NO code change -- and that is a decision, not an
# omission. Every scan here is either edge-aware (ranges 1..height-2,
# which keep the staircase probes one cell inside the border) or steps
# DIAGONALLY (p +- width +- 1 with a running k). Flattening those to a
# single loop over $ncells would either need a modulo per cell to rebuild
# the column guard, or would hide the diagonal in arithmetic. Same call as
# in Deadlock.pm's window matchers: the y/x form carries the intent.
#
# A diagonal = a staircase of free cells walled on both sides; mark_diags()
# records its inner length at the top cell (diag_right / diag_left boards
# carry the length in the cell byte), diag_deadlock() scans it top-down
# deciding whether any box on it can ever be pushed out. mark_diags' local
# 'inner' shadows Board's global inner exactly like in C.
#
# Exports follow diags.h; wallify_diag_void / diag_deadlock stay internal.
#
# Globals ledger:
#   reads:  $height $width @delta_y @delta_x
#   writes: nothing (results via arguments/returns)

sub mark_diags ($brd) {

    # local 'inner' cloud of 4-surrounded free cells, shadows the global
    my $inner;
    my ($diag_right, $diag_left);
    $inner = $ZERO_BOARD;
    $diag_right = $ZERO_BOARD;
    $diag_left = $ZERO_BOARD;

    # mark all empty squares surrounded by four elements
    for my $i (1 .. $height - 2) {
        for my $j (1 .. $width - 2) {
            my $p = $i * $width + $j;
            next if vec($brd, $p, 8) & OCCUPIED;
            next if vec($brd, $p, 8) & SOKOBAN;  # this can happen in the initial position

            next if (vec($brd, $p - $width, 8) & OCCUPIED) == 0;
            next if (vec($brd, $p + $width, 8) & OCCUPIED) == 0;
            next if (vec($brd, $p + 1, 8) & OCCUPIED) == 0;
            next if (vec($brd, $p - 1, 8) & OCCUPIED) == 0;
            vec($inner, $p, 8) = 1;
        }
    }

    # look for pattern:
    # O
    #  D
    #   D
    #    D
    #     O

    for my $i (1 .. $height - 2) {
        for my $j (1 .. $width - 2) {
            my $p = $i * $width + $j;
            next if vec($inner, $p, 8) == 0;

            my $diag_start = 0;
            $diag_start = 1 if vec($brd, $p - $width - 1, 8) & OCCUPIED;
            $diag_start = 1
                if vec($brd, $p - $width, 8) == WALL and vec($brd, $p - 1, 8) == WALL;
            next if $diag_start == 0;

            my $k = 1;
            $k++ while vec($inner, ($i + $k) * $width + $j + $k, 8);

            my $diag_end = 0;
            my $ep = ($i + $k) * $width + $j + $k;
            $diag_end = 1 if vec($brd, $ep, 8) & OCCUPIED;
            $diag_end = 1
                if vec($brd, $ep - $width, 8) == WALL and vec($brd, $ep - 1, 8) == WALL;
            next if $diag_end == 0;

            vec($diag_right, $p, 8) = $k;
        }
    }

    # same for diag_left:
    #      O
    #     D
    #    D
    #   D
    #  O

    for my $i (1 .. $height - 2) {
        for my $j (1 .. $width - 2) {
            my $p = $i * $width + $j;
            next if vec($inner, $p, 8) == 0;

            my $diag_start = 0;
            $diag_start = 1 if vec($brd, $p - $width + 1, 8) & OCCUPIED;
            $diag_start = 1
                if vec($brd, $p - $width, 8) == WALL and vec($brd, $p + 1, 8) == WALL;
            next if $diag_start == 0;

            my $k = 1;
            $k++ while vec($inner, ($i + $k) * $width + $j - $k, 8);

            my $diag_end = 0;
            my $ep = ($i + $k) * $width + $j - $k;
            $diag_end = 1 if vec($brd, $ep, 8) & OCCUPIED;
            $diag_end = 1
                if vec($brd, $ep - $width, 8) == WALL and vec($brd, $ep + 1, 8) == WALL;
            next if $diag_end == 0;

            vec($diag_left, $p, 8) = $k;
        }
    }

    return ($diag_right, $diag_left);
}

sub wallify_diag_void ($brd, $p, $k, $diag_right) {
    if ($diag_right) {
        for my $n (0 .. $k - 1) {
            vec($brd, $p + $n * ($width + 1) - 1, 8) = WALL;
            vec($brd, $p + $n * ($width + 1) + 1, 8) = WALL;
        }

        vec($brd, $p - $width - 1, 8) = WALL
            if vec($brd, $p - $width - 1, 8) & OCCUPIED;
        vec($brd, $p - $width, 8) = WALL;

        vec($brd, $p + $k * ($width + 1), 8) = WALL
            if vec($brd, $p + $k * ($width + 1), 8) & OCCUPIED;
        vec($brd, $p + $k * ($width + 1) - 1, 8) = WALL;
    }
    else {
        for my $n (0 .. $k - 1) {
            vec($brd, $p + $n * ($width - 1) - 1, 8) = WALL;
            vec($brd, $p + $n * ($width - 1) + 1, 8) = WALL;
        }

        vec($brd, $p - $width + 1, 8) = WALL
            if vec($brd, $p - $width + 1, 8) & OCCUPIED;
        vec($brd, $p - $width, 8) = WALL;

        vec($brd, $p + $k * ($width - 1), 8) = WALL
            if vec($brd, $p + $k * ($width - 1), 8) & OCCUPIED;
        vec($brd, $p + $k * ($width - 1) + 1, 8) = WALL;
    }
    return $brd;
}

sub diag_has_no_targets ($brd, $p, $n, $diag_right) {
    my $step = $width + ($diag_right ? 1 : -1);

    for my $k (0 .. $n - 1) {
        return 0 if vec($brd, $p + $k * $step, 8) & TARGET;
    }
    return 1;
}


# ====================================================================
# Games::Sokoban::Fest::Helper  (was lib2/Games/Sokoban/Fest/Helper.pm)
# ====================================================================

# Port of festival/helper.cpp + the helper struct of helper.h (Festival
# 3.1, Yaron Shoham). The per-search context bag: solution buffer, parking
# order, plan boards, search flags. In Perl a helper is a hashref with the
# C field names; init_helper() RETURNS a fresh one (C fills a caller
# buffer). The big substructures (oop/imagine/request) start undef like
# the C NULL pointers; init_helper_extra_fields() gives them empty
# hashrefs -- their inner shape is owned by the modules that fill them
# (Oop/Imagine/Request, M5/M6).
# DEVIATION: imagined_hf_board / wallified / scored_distance start EMPTY
# (reads yield 0) where C leaves malloc garbage -- they are only read in
# search modes that fill them first.
#
# Globals ledger: reads nothing, writes nothing (pure constructor).

sub reset_helper ($h) {
    $h->{'parking_order_num'}       = 0;
    $h->{'full_parking_order_num'}  = 0;
    $h->{'sol_len'}                 = 0;
    $h->{'perimeter_found'}         = 0;
    $h->{'enable_inefficient_moves'} = 0;
    $h->{'level_solved'}            = 0;
    $h->{'weighted_search'}         = 1;
    $h->{'used_in_plan'}            = $ZERO_BOARD;

    # DEVIATION from C (2026-08-08, deliberate -- see the DEVIATIONS list in
    # the Fest section). C leaves these two alone here, and they are the ONLY
    # helper fields whose producer and consumer sit in the two halves of ONE
    # strategy: the first half writes them (packing_search ->
    # set_imagined_hf_board, or FESS -> setup_rev_board for REV), the second
    # half scores every position against them. Not clearing them means a
    # board SURVIVES -- into the next strategy, and, since one process
    # solves game after game, into the NEXT LEVEL. A leftover board of the
    # previous level has the previous level's box count, so the scorer dies
    # ("box num mismatch2" / "mismatch4"); a leftover 'wallified' silently
    # prunes moves in the REV branch of find_possible_moves. Reproduced with
    # ai/t_fest_short_limit.pl: 10 of 12 games died in ONE process while each
    # of them, solved alone, was fine.
    $h->{'imagined_hf_board'} = '';
    $h->{'wallified'}         = '';
    return;
}

sub init_helper () {    # returns the fresh helper hashref
    my $h = {
        # the large data structures (C: NULL until init_helper_extra_fields)
        'oop'     => undef,
        'imagine' => undef,
        'request' => undef,

        'parking_order'      => [],
        'boxes_were_removed' => 0,
        'full_parking_order' => [],
        'scored_distance'    => [],

        'imagined_hf_board' => '',
        'wallified'         => '',

        'sol_move' => [],

        'tested_deadlock_room' => 0,
        'k_dist_value'         => 0,
        'alg_type'             => 0,
        'my_core'              => 0,
    };
    reset_helper($h);
    return $h;
}


# ====================================================================
# Games::Sokoban::Fest::Holes  (was lib2/Games/Sokoban/Fest/Holes.pm)
# ====================================================================

# Port of festival/holes.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 translation: flat cell positions (@delta_p), single loops over
# $ncells. The ascending-position scan order equals the C row-major order,
# so the iterative peeling behaves identically.
#
# Globals ledger:
#   reads:  $ncells @delta_p Board geometry
#   writes: $target_holes $semi_holes (boards, filled by mark_target_holes)

sub is_square_a_target_hole ($brd, $p) {
    return 0 if (vec($brd, $p, 8) & TARGET) == 0;

    my $sum = grep {vec($brd, $p + $_, 8) == WALL} @delta_p;

    return $sum == 3 ? 1 : 0;
}

sub mark_semi_holes ($brd) {
    $semi_holes = $ZERO_BOARD;

    for my $p (0 .. $ncells - 1) {
        next unless vec($brd, $p, 8) & TARGET;

        for my $k (0 .. 3) {
            my $val1 = vec($brd, $p + $delta_p[$k], 8);
            my $val2 = vec($brd, $p + $delta_p[($k + 1) & 3], 8);

            vec($semi_holes, $p, 8) = 1 if $val1 == WALL and $val2 == WALL;
        }
    }
    return;
}

sub mark_target_holes ($b_in) {
    my $brd;
    my $changed = 1;

    $brd = $b_in;
    $brd &.= $NOT_BOX;
    $brd &.= $NOT_SOKOBAN;

    $target_holes = $ZERO_BOARD;

    while ($changed) {
        $changed = 0;

        for my $p (0 .. $ncells - 1) {
            if (is_square_a_target_hole($brd, $p)) {
                vec($brd, $p, 8) = WALL;
                $changed = 1;
                vec($target_holes, $p, 8) = 1;
            }
        }
    }

    mark_semi_holes($brd);
    return;
}


# ====================================================================
# Games::Sokoban::Fest::Io  (was lib2/Games/Sokoban/Fest/Io.pm)
# ====================================================================

# Port of festival/io.cpp (Festival 3.1, Yaron Shoham).
# Deviations, all display-only:
#   - the Win32 console color machinery (SetConsoleTextAttribute, color
#     codes, print_box glyph 254) is dropped; show_board() prints one plain
#     ASCII glyph per cell instead, keeping the C switch's case analysis and
#     its "unknown board value" tripwire:
#       ' ' floor        '#' wall         '$' box         '.' target
#       '@' sokoban      '*' box+target   '+' sokoban+target
#       '-' base         '~' base+sok     'B' base+box    '=' base+target
#       'X' base+target+box              '&' base+target+sokoban
#   - the .sok level-set reader and the XSB text path are GONE: levels
#     reach the port only through set_board_from_code, fed from the
#     database's digit code.
# A 'text level' (C: board used as char[51][51] text buffer) is an arrayref
# of row strings here.
#
# Globals ledger:
#   reads:  $height $width $ncells
#   writes: $height $width (set_board_from_code -- the ONLY entry point for a
#           new level's dimensions; also triggers init_board_geometry)


# The project's own digit code (game_blob.code), which is where every
# level actually comes from. Until now it reached the board by way of
# XSB text; this table is that detour composed into one step, and it must
# reproduce the detour's MANY-TO-ONE collapse EXACTLY, or this side would
# see distinctions the C oracle cannot:
#   2 avoid          -> SPACE, same as 0 (Festival has no avoid concept)
#   6 player-on-avoid-> SOKOBAN, same as 5
#   1 filler         -> WALL, same as 9
# The three collapses are the whole reason this table is written out
# instead of derived.

# (digit_level, row_num) -> (width, board); the board is built with row
# stride = level width, so its length is exactly row_num * width.
sub get_board_from_code ($level, $row_num) {

    # pipeline guarantee: every row has the same length as the first
    my $w = length $level->[0];

    my $brd = '';
    for my $i (0 .. $row_num - 1) {
        $brd .= pack 'C*', map {$CODE_VAL{$_} // 0} split //, $level->[$i];
    }

    return ($w, $brd);
}

# (digit_level, row_num) -> board; sets the $height/$width globals and
# rebuilds the per-level board geometry (ncells, delta_p, masks). The
# production entry point for a new level.
sub set_board_from_code ($level, $row_num) {
    ($width, my $brd) = get_board_from_code($level, $row_num);
    $height = $row_num;
    init_board_geometry();
    return $brd;
}

# ====================================================================
# Games::Sokoban::Fest::Overlap  (was lib2/Games/Sokoban/Fest/Overlap.pm)
# ====================================================================

# Port of festival/overlap.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 translation: P1 (the plan target index is turned into a cell
# position by table lookup). Everything else was already flat.
#
# save_full_parking_order backs up the parking
# plan before reduce_parking_order trims it (the full plan feeds the
# imagined boards and the used_in_plan board); overlap_score replays the
# full plan and scores how far the given board's boxes overlap it.
#
# Cross-module calls resolved at runtime, fully qualified (import cycle):
#   Imagine::init_imagine
#
# Globals ledger:
#   reads:  $width
#   writes: nothing global (helper full_parking_order/used_in_plan)


sub overlap_score ($brd, $h) {
    my $overlap_board;    # mostly for debug
    my $score              = 0;
    my $best_overlap_score = -1;

    return 0 if $h->{'boxes_were_removed'};

    return 0 if $h->{'full_parking_order_num'} == 0;

    $overlap_board = $ZERO_BOARD;

    for my $i (0 .. $h->{'full_parking_order_num'} - 1) {
        my $to_p = $index_to_p[$h->{'full_parking_order'}[$i]{'to'}];
        vec($overlap_board, $to_p, 8) = 1;
        $score++ if vec($brd, $to_p, 8) & BOX;

        if ($h->{'full_parking_order'}[$i]{'from'} >= 0) {
            my $from_p = $index_to_p[$h->{'full_parking_order'}[$i]{'from'}];
            vec($overlap_board, $from_p, 8) = 0;
            $score-- if vec($brd, $from_p, 8) & BOX;
        }

        $best_overlap_score = $score if $score >= $best_overlap_score;
    }

    return $best_overlap_score;
}

# ====================================================================
# Games::Sokoban::Fest::DeadlockUtils  (was lib2/Games/Sokoban/Fest/DeadlockUtils.pm)
# ====================================================================

# Port of festival/deadlock_utils.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 translation: bit extractions via whole-string masks + tr (the
# init_inner pattern), single-p scans, internal helpers on flat positions.
# The DEADLOCK_ZONE bit (32) marks the region the deadlock sub-search is
# allowed to work in; these helpers set, spread, shrink and query that
# zone (8-neighbor spreading uses @delta_p_8).
#
# Exports follow deadlock_utils.h; can_be_pushed_sideways, add_islands,
# update_deadlock_zone_from_group_push_mode, update_deadlock_zone_push_mode
# and near_deadlock_zone stay package-internal (file-local in C).
#
# Globals ledger:
#   reads:  $height $width $ncells @delta_p @delta_p_8 $inner
#           $index_num Board::$initial_board
#   writes: nothing global (mutates boards passed by the caller)


sub _dz_masks () {
    if ($DZ_len != $ncells) {
        $NOT_DZ  = chr(0xFF ^ DEADLOCK_ZONE) x $ncells;
        $DZ_ONLY = chr(DEADLOCK_ZONE) x $ncells;
        $DZ_len  = $ncells;
    }
    return;
}

sub work_left_in_deadlock_zone ($brd) {
    for my $p (0 .. $ncells - 1) {
        my $c = vec($brd, $p, 8);
        next if ($c & DEADLOCK_ZONE) == 0;
        next if $c & SOKOBAN;    # probably a diagonal added to the zone

        return 1 if ($c & BOX) and ($c & TARGET) == 0;
        return 1 if ($c & TARGET) and ($c & BOX) == 0;
    }
    return 0;
}


sub get_sokoban_cloud_as_group ($brd) {
    state $sok_only = '';
    $sok_only = chr(SOKOBAN) x $ncells if length($sok_only) != $ncells;

    # player bit -> 1 (0x08 = SOKOBAN)
    (my $g = $brd &. $sok_only) =~ tr/\x08/\x01/;
    return $g;
}

sub can_be_pushed_sideways ($brd, $p, $d) {
    # if the box is free to move twice, assume that it is not part of the corral
    $d = ($d + 1) & 3;

    if ((vec($brd, $p + $delta_p[$d], 8) & OCCUPIED) == 0) {
        if ((vec($brd, $p + 2 * $delta_p[$d], 8) & OCCUPIED) == 0) {
            return 1 if (vec($brd, $p - $delta_p[$d], 8) & OCCUPIED) == 0;
        }
    }

    $d = ($d + 2) & 3;

    if ((vec($brd, $p + $delta_p[$d], 8) & OCCUPIED) == 0) {
        if ((vec($brd, $p + 2 * $delta_p[$d], 8) & OCCUPIED) == 0) {
            return 1 if (vec($brd, $p - $delta_p[$d], 8) & OCCUPIED) == 0;
        }
    }

    return 0;
}

sub update_deadlock_zone_from_group_push_mode ($brd, $group) {

    my $prev_deadlock_zone;
    _dz_masks(); ($prev_deadlock_zone = $brd &. $DZ_ONLY) =~ tr/\x20/\x01/;

    _dz_masks(); $brd &.= $NOT_DZ;

    for my $p (0 .. $ncells - 1) {
        next if vec($inner, $p, 8) == 0;
        next if vec($group, $p, 8) == 0;

        vec($brd, $p, 8) |= DEADLOCK_ZONE;

        # add squares that touch the zone
        # (diagonals too: a box arriving there should join the zone)
        for my $k (0 .. 7) {
            vec($brd, $p + $delta_p_8[$k], 8) |= DEADLOCK_ZONE
                if vec($brd, $p + $delta_p_8[$k], 8) != WALL;
        }

        # add boxes that block access to the zone
        for my $k (0 .. 3) {
            if (vec($brd, $p + $delta_p[$k], 8) & BOX) {
                if (vec($brd, $p + 2 * $delta_p[$k], 8) & BOX) {
                    vec($brd, $p + 2 * $delta_p[$k], 8) |= DEADLOCK_ZONE
                        if can_be_pushed_sideways($brd,
                            $p + 2 * $delta_p[$k], $k) == 0;
                }
            }
        }
    }

    for my $p (0 .. $ncells - 1) {
        vec($brd, $p, 8) &= 0xFF ^ DEADLOCK_ZONE
            if vec($prev_deadlock_zone, $p, 8) == 0;
    }
    return $brd;
}

sub add_islands ($brd) {

    my $dz;
    _dz_masks(); ($dz = $brd &. $DZ_ONLY) =~ tr/\x20/\x01/;

    for my $p (0 .. $ncells - 1) {
        next if vec($inner, $p, 8) == 0;
        next if vec($brd, $p, 8) & OCCUPIED;
        next if vec($dz, $p, 8);

        # check if touches DZ
        next unless grep {vec($dz, $p + $_, 8)} @delta_p;

        # check surrounded
        if (not grep {(vec($brd, $p + $_, 8) & OCCUPIED) == 0} @delta_p) {
            vec($brd, $p, 8) |= DEADLOCK_ZONE;
            for my $k (0 .. 7) {
                vec($brd, $p + $delta_p_8[$k], 8) |= DEADLOCK_ZONE
                    if vec($brd, $p + $delta_p_8[$k], 8) & BOX;
            }
        }
    }
    return $brd;
}

sub init_deadlock_zone_from_group ($brd, $group, $pull_mode) {

    if ($pull_mode) {
        _dz_masks(); $brd &.= $NOT_DZ;

        for my $p (0 .. $ncells - 1) {
            next if vec($group, $p, 8) == 0;

            vec($brd, $p, 8) |= DEADLOCK_ZONE;
            for my $k (0 .. 7) {
                vec($brd, $p + $delta_p_8[$k], 8) |= DEADLOCK_ZONE
                    if vec($brd, $p + $delta_p_8[$k], 8) & BOX;
            }
        }

        $brd = add_islands($brd);
        return $brd;
    }

    for my $p (0 .. $ncells - 1) {
        vec($brd, $p, 8) |= DEADLOCK_ZONE;
    }

    $brd = update_deadlock_zone_from_group_push_mode($brd, $group);
    return $brd;
}

sub set_deadlock_zone_in_pull_mode ($brd) {
    my $g;
    $g = get_sokoban_cloud_as_group($brd);
    $brd = init_deadlock_zone_from_group($brd, $g, 1);
    return $brd;
}

sub update_deadlock_zone_push_mode ($brd) {

    my $unreachable;
    $unreachable = $ZERO_BOARD;

    for my $p (0 .. $ncells - 1) {
        next if vec($brd, $p, 8) & SOKOBAN;
        next if vec($inner, $p, 8) == 0;
        next if vec($brd, $p, 8) & OCCUPIED;

        # new DZ must be inside older DZ
        next if (vec($brd, $p, 8) & DEADLOCK_ZONE) == 0;

        vec($unreachable, $p, 8) = 1;
    }

    $brd = update_deadlock_zone_from_group_push_mode($brd, $unreachable);
    return $brd;
}


sub clear_boxes_out_of_deadlock_zone ($brd) {

    for my $p (0 .. $ncells - 1) {
        vec($brd, $p, 8) &= 0xFF ^ BOX
            if (vec($brd, $p, 8) & DEADLOCK_ZONE) == 0;
    }

    $brd = expand_sokoban_cloud($brd);
    return $brd;
}


sub update_deadlock_zone ($brd, $pull_mode) {
    if ($pull_mode) {$brd = set_deadlock_zone_in_pull_mode($brd);}
    else       {$brd = update_deadlock_zone_push_mode($brd);}

    $brd = clear_boxes_out_of_deadlock_zone($brd);
    return $brd;
}

sub size_of_deadlock_zone ($brd) {
    _dz_masks();
    my $t = $brd &. $DZ_ONLY;
    return $t =~ tr/\x00//c;
}

# ====================================================================
# Games::Sokoban::Fest::Envelope  (was lib2/Games/Sokoban/Fest/Envelope.pm)
# ====================================================================

# Port of festival/envelope.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. An "envelope" is a proven-dead ring of boxes
# around a corral (a region the player cannot reach): init_envelope
# _patterns() enumerates candidate rings (targets adjacent / diagonal to
# each reverse-mode corral, up to 2^diag combinations), keeps those from
# which NO outside zone can finish the level (mini_search), and
# fix_boxes_using_envelopes() later wallifies boxes matching a stored
# pattern. Time fuse: should_abort_envelopes() gives up after time_limit/2
# seconds since $start_time (deterministic runs must set $start_time).
#
# Exports follow envelope.h; the enumeration helpers stay internal.
# Runtime-qualified call (module ported later):
#   MiniSearch::can_put_all_on_targets
#
# Globals ledger:
#   reads:  $height $width $ncells @delta_y @delta_x @delta_p_8 $inner
#           $index_num $global_boxes_in_level $start_time $time_limit
# Board::$initial_board
# writes: @new_envelope_patterns (as scalar @)

sub size_of_corral ($corrals, $corral_index) {    # corrals = int_board arrayref
    my $sum = 0;
    for my $p (0 .. $ncells - 1) {
        $sum++ if $corrals->[$p] == $corral_index;
    }
    return $sum;
}

sub wallify_boxes_using_pattern ($brd, $pat_num) {

    for my $p (0 .. $ncells - 1) {
        vec($brd, $p, 8) = WALL
            if vec($new_envelope_patterns[$pat_num], $p, 8) & BOX;
    }
    return $brd;
}

sub matches_envelope_pattern ($brd, $n) {
    # check that all pattern boxes are in place
    for my $p (0 .. $ncells - 1) {
        if (vec($new_envelope_patterns[$n], $p, 8) & BOX) {
            # a wall is as good as box
            return 0 if (vec($brd, $p, 8) & OCCUPIED) == 0;
        }
    }

    # make sure the sokoban is not in the corral
    for my $p (0 .. $ncells - 1) {
        if ((vec($new_envelope_patterns[$n], $p, 8) & SOKOBAN) == 0) {
            return 0 if vec($brd, $p, 8) & SOKOBAN;
        }
    }
    return 1;
}

sub fix_boxes_using_envelopes ($brd) {
    for my $i (0 .. $#new_envelope_patterns) {
        next if matches_envelope_pattern($brd, $i) == 0;
        $brd = wallify_boxes_using_pattern($brd, $i);
    }
    return $brd;
}

sub already_in_envelopes ($brd) {
    for my $i (0 .. $#new_envelope_patterns) {
        return 1 if matches_envelope_pattern($brd, $i);
    }
    return 0;
}

sub get_envelope_boxes ($corrals, $corral_index) {
    # returns (\@regular_boxes, \@diag_boxes)
    my $brd;
    $brd = $initial_board &. $NOT_BOX;

    my (@regular_boxes, @diag_boxes);

    # collect regular boxes
    for my $p (0 .. $ncells - 1) {
next if $corrals->[$p] != $corral_index;

for my $k (0 .. 3) {
my $q = $p + $delta_p[$k];

if (vec($brd, $q, 8) & TARGET) {
push @regular_boxes, $y_x_to_index_table[$q];
vec($brd, $q, 8) &= 0xFF ^ TARGET;
}
}
}

    # collect diagonal boxes
    for my $p (0 .. $ncells - 1) {
next if $corrals->[$p] != $corral_index;

for my $k (0 .. 7) {
my $q = $p + $delta_p_8[$k];

if (vec($brd, $q, 8) & TARGET) {
push @diag_boxes, $y_x_to_index_table[$q];
vec($brd, $q, 8) &= 0xFF ^ TARGET;
}
}
}

    return (\@regular_boxes, \@diag_boxes);
}

sub simple_popcnt ($v) {
    my $sum = 0;
    for (0 .. 31) {
        $sum += $v & 1;
        $v >>= 1;
    }
    return $sum;
}

sub set_up_corral ($regular_boxes, $diag_boxes, $diag_indices) {

    my $brd;
    $brd = $initial_board &. $NOT_BOX;
    $brd &.= $NOT_SOKOBAN;

    for my $i (0 .. $#$regular_boxes) {
        my $p = $index_to_p[$regular_boxes->[$i]];
        vec($brd, $p, 8) |= BOX;
    }

    for my $i (0 .. 31) {
        if (($diag_indices >> $i) & 1) {
            my $p = $index_to_p[$diag_boxes->[$i]];
            vec($brd, $p, 8) |= BOX;
        }
    }

    return $brd;
}

sub put_sokoban_out_of_corral ($brd, $corrals, $corral_index) {

    $brd &.= $NOT_SOKOBAN;

    for my $p (0 .. $ncells - 1) {
        next if vec($inner, $p, 8) == 0;
        next if $corrals->[$p] == $corral_index;
        next if vec($brd, $p, 8) & OCCUPIED;
        vec($brd, $p, 8) |= SOKOBAN;
    }
    return $brd;
}

sub can_solve_from_any_zone ($corrals, $corral_index, $b_in) {
    my $corral_zone = -1;
    my @zones;

    my $brd = $b_in;

    my $zones_num = mark_connectivities($brd, \@zones);

    for my $p (0 .. $ncells - 1) {
        $corral_zone = $zones[$p] if $corrals->[$p] == $corral_index;
    }

    Carp::confess('no corral zone') if $corral_zone == -1;

    for my $z (0 .. $zones_num - 1) {
        next if $z == $corral_zone;

        $brd = put_sokoban_in_zone($brd, \@zones, $z);

        # note that this is a little recursive: the move generator uses
        # turn_fixed_boxes_into_walls which uses the envelopes, and computing
        # the envelopes uses find_box_moves... but using patterns found so
        # far can't hurt the move generator.
        # (-1 is unknown result - so maybe boxes can be put on targets)
        return 1
            if can_put_all_on_targets($brd, 100);
    }
    return 0;
}

sub should_abort_envelopes () {
    my $t = time() - $start_time;
    if ($t > $time_limit / 2) {
        $Envelopes_incomplete = 1;    # the patterns found so far stay; the hash says they are not all
        return 1;
    }
    return 0;
}

sub analyse_envelope ($corrals, $corral_index, $regular_boxes, $diag_boxes) {
    my $diag_boxes_num = scalar @$diag_boxes;

    return if $diag_boxes_num >= 8;    # limit enumeration size

    # how many diagonal boxes are in the envelope
    for my $enum_diag (0 .. $diag_boxes_num) {
        for my $i (0 .. (1 << $diag_boxes_num) - 1) {
            return if should_abort_envelopes();

            next if simple_popcnt($i) != $enum_diag;

            my $brd;
            $brd = set_up_corral($regular_boxes, $diag_boxes, $i);
            $brd = put_sokoban_out_of_corral($brd, $corrals, $corral_index);

            # position is solved
            next if (($brd &. $BOX_ONLY) =~ tr/\x00//c) == $global_boxes_in_level;

            next if already_in_envelopes($brd);

            next if can_solve_from_any_zone($corrals, $corral_index, $brd);

            push @new_envelope_patterns, $brd;

        }
    }
    return;
}

sub init_envelope_patterns () {
    my @corrals;

    @new_envelope_patterns = ();
    $Envelopes_incomplete  = 0;

    my $brd;
    $brd = $initial_board;
    $brd = enter_reverse_mode($brd, 0);    # 0 : don't mark bases

    my $n = mark_connectivities($brd, \@corrals);

    return if $n == 1;

    for my $i (0 .. $n - 1) {
        my ($regular_boxes, $diag_boxes) = get_envelope_boxes(\@corrals, $i);

        next if size_of_corral(\@corrals, $i) > $index_num / 2;

        analyse_envelope(\@corrals, $i, $regular_boxes, $diag_boxes);
    }
    return;
}

# ====================================================================
# Games::Sokoban::Fest::FixedBoxes  (was lib2/Games/Sokoban/Fest/FixedBoxes.pm)
# ====================================================================

# Port of festival/fixed_boxes.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. turn_fixed_boxes_into_walls() iterates five
# wallification passes (2x2 blocks, closable holes, immovable boxes,
# target-free diagonals, retrograde "crystaline" boxes) to a fixed point.
#
# Exports follow fixed_boxes.h; the pass helpers stay package-internal.
# Cross-module references resolved at runtime, fully qualified:
#   deadlock_in_direction (deadlock.cpp)
#   fix_boxes_using_envelopes
#
# Globals ledger:
#   reads:  $height $width @delta_y @delta_x
#   writes: nothing (results via arguments/returns)

sub turn_2x2_to_walls ($brd) {
    # this routine does not guarantee to blockify all boxes in one pass
    my $changed = 0;

    for my $i (0 .. $height - 2) {
        for my $j (0 .. $width - 2) {
            my $sum = 0;

            for my $y (0 .. 1) {
                for my $x (0 .. 1) {
                    $sum++
                        if vec($brd, ($i + $y) * $width + $j + $x, 8) & OCCUPIED;
                }
            }

            if ($sum == 4) {
                # check if one of them is a box
                for my $y (0 .. 1) {
                    for my $x (0 .. 1) {
                        my $p = ($i + $y) * $width + $j + $x;
                        $changed = 1 if vec($brd, $p, 8) & BOX;
                        vec($brd, $p, 8) = WALL;
                    }
                }
            }
        }
    }
    return ($changed, $brd);
}

sub close_holes ($brd) {

    for my $i (1 .. $height - 2) {
        for my $j (1 .. $width - 2) {
            my $p = $i * $width + $j;

            if (vec($brd, $p, 8) == SPACE) {
                # close holes of type
                #    $
                #   # #
                #    #

                for my $k (0 .. 3) {
                    next
                        if vec($brd, ($i + $delta_y[($k + 1) & 3]) * $width + $j + $delta_x[($k + 1) & 3], 8) != WALL;
                    next
                        if vec($brd, ($i + $delta_y[($k + 2) & 3]) * $width + $j + $delta_x[($k + 2) & 3], 8) != WALL;
                    next
                        if vec($brd, ($i + $delta_y[($k + 3) & 3]) * $width + $j + $delta_x[($k + 3) & 3], 8) != WALL;
                    vec($brd, $p, 8) = WALL;
                    return (1, $brd);
                }
            }

            if (vec($brd, $p, 8) == SOKOBAN) {
                # close holes of type
                #    .
                #   #.#
                #    #

                for my $k (0 .. 3) {
                    next
                        if (vec($brd, ($i + $delta_y[$k]) * $width + $j + $delta_x[$k], 8) & SOKOBAN) == 0;
                    next
                        if vec($brd, ($i + $delta_y[($k + 1) & 3]) * $width + $j + $delta_x[($k + 1) & 3], 8) != WALL;
                    next
                        if vec($brd, ($i + $delta_y[($k + 2) & 3]) * $width + $j + $delta_x[($k + 2) & 3], 8) != WALL;
                    next
                        if vec($brd, ($i + $delta_y[($k + 3) & 3]) * $width + $j + $delta_x[($k + 3) & 3], 8) != WALL;
                    vec($brd, $p, 8) = WALL;
                    return (1, $brd);
                }
            }
        }
    }

    return (0, $brd);
}

sub remove_all_pushable_boxes ($brd) {
    # this routine assumes that the player can be everywhere

    my $changed = 1;
    while ($changed) {
        $changed = 0;

        for my $p (0 .. $ncells - 1) {
next if (vec($brd, $p, 8) & BOX) == 0;

for my $k (0 .. 3) {
next if vec($brd, $p + $delta_p[$k], 8) & OCCUPIED;
next if vec($brd, $p - $delta_p[$k], 8) & OCCUPIED;

next if deadlock_in_direction($brd, $p, $k);

vec($brd, $p, 8) &= 0xFF ^ BOX;
$changed = 1;
last;
}    # k
}
    }    # changed
    return $brd;
}

sub fix_crystaline ($b_in) {
    # use retrograde analysis to find boxes that can't be moved until the end
    # (because from the end they can't be pulled)

    my $brd;
    my $fixed_box = 0;

    $brd = $b_in;
    $brd &.= $NOT_SOKOBAN;
    $brd = go_to_final_position_with_given_walls($brd);

    my $removed_box;
    do {
        $removed_box = 0;
        for my $p (0 .. $ncells - 1) {
next if vec($brd, $p, 8) != PACKED_BOX;

for my $k (0 .. 3) {
next
if vec($brd, $p + $delta_p[$k], 8) & OCCUPIED;
next
if vec($brd, $p + 2 * $delta_p[$k], 8) & OCCUPIED;

vec($brd, $p, 8) &= 0xFF ^ BOX;
$removed_box = 1;
last;
}
}
    } while ($removed_box);

    for my $p (0 .. $ncells - 1) {
        $fixed_box = 1
            if (vec($brd, $p, 8) & BOX) and (vec($b_in, $p, 8) & BOX);
    }

    if ($fixed_box) {
        for my $p (0 .. $ncells - 1) {
            vec($b_in, $p, 8) = WALL
                if (vec($brd, $p, 8) & BOX) and (vec($b_in, $p, 8) & BOX);
        }
    }

    return ($fixed_box, $b_in);
}

sub turn_immovable_boxes_to_walls ($brd) {

    my $remaining;
    my $changed = 0;

    $remaining = $brd;
    $remaining = remove_all_pushable_boxes($remaining);

    for my $p (0 .. $ncells - 1) {
        if (vec($remaining, $p, 8) & BOX) {
            vec($brd, $p, 8) = WALL;
            $changed = 1;
        }
    }
    return ($changed, $brd);
}

sub fix_diagonals ($w) {

    my ($diag_right, $diag_left);
    my $changed = 0;

    ($diag_right, $diag_left) = mark_diags($w);

    for my $p (0 .. $ncells - 1) {

if (vec($diag_right, $p, 8)) {
if (diag_has_no_targets($w, $p, vec($diag_right, $p, 8), 1)) {
my $backup = $w;
$w = wallify_diag_void($w, $p, vec($diag_right, $p, 8), 1);
$changed |= ($w eq $backup ? 0 : 1);
}
}

if (vec($diag_left, $p, 8)) {
if (diag_has_no_targets($w, $p, vec($diag_left, $p, 8), 0)) {
my $backup = $w;
$w = wallify_diag_void($w, $p, vec($diag_left, $p, 8), 0);
$changed |= ($w eq $backup ? 0 : 1);
}
}
}
    return ($changed, $w);
}

sub turn_fixed_boxes_into_walls ($brd) {
    my $w;

    $w = $brd;
    $w = fix_boxes_using_envelopes($w);

    my $changed = 1;
    while ($changed) {
        my $f;
        ($changed, $w) = turn_2x2_to_walls($w);
        ($f, $w) = close_holes($w);
        $changed |= $f;
        ($f, $w) = turn_immovable_boxes_to_walls($w);
        $changed |= $f;
        ($f, $w) = fix_diagonals($w);
        $changed |= $f;
        ($f, $w) = fix_crystaline($w);
        $changed |= $f;
    }

    return $w;
}


# ====================================================================
# Games::Sokoban::Fest::Graph  (was lib2/Games/Sokoban/Fest/Graph.pm)
# ====================================================================

# Port of festival/graph.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 translation: the per-vertex hashrefs of the transcription are
# repacked into parallel flat arrays inside the graph handle (pattern P6;
# this module is the hot path of set_distances). Algorithms unchanged.
#
# Data shapes:
#   vertex index = (box inner-index * 4) | sokoban_side (2 bits);
#   gd handle = hashref of parallel arrays indexed by vertex:
#     active[], weight[], src[], reversible[], push[], pull[]
#     shift[] flat at (vertex * 4 + direction)
#   plus vertices_num and current_impossible_board (board string).
#   shift/push/pull hold the vertex index reached by that operation, with
#   the C original's 0-as-"no edge" sentinel KEPT AS IS (edges into vertex
#   0 are impossible in the original too -- do not fix);
#   'move' records returned by get_box_moves_from_graph are hashrefs
#   {from, to, sokoban_position, kill, base, attr => {weight, advisor,
#   reversible}} -- the moves.cpp struct shape, owned by Fest::Moves.
#
# Only the graph.h functions are exported (the C header contract); the
# file-local helpers stay package-internal.
#
# Cross-module references resolved at runtime, fully qualified (C externs):
#   @impossible_place  (distance.cpp)
#   mark_deadlock_2x2  (deadlock.cpp)
#
# Globals ledger:
#   reads:  $width $ncells @delta_y @delta_x @delta_p $inner $index_num
#           Distance::@impossible_place
#   writes: nothing global (everything lives in the gd handle)

sub allocate_graph () {
    my $n = $index_num * 4;
    return {
        'vertices_num'             => $n,
        'active'                   => [(0) x $n],
        'weight'                   => [(0) x $n],
        'src'                      => [(-1) x $n],
        'reversible'               => [(0) x $n],
        'push'                     => [(0) x $n],
        'pull'                     => [(0) x $n],
        'shift'                    => [(0) x ($n * 4)],
        'current_impossible_board' => '',
    };
}

sub init_active ($brd, $gd) {
    my $active = $gd->{'active'};

    # "active" tests if sokoban can be positioned in this side of the box

    @$active = (0) x $gd->{'vertices_num'};

    for my $i (0 .. $index_num - 1) {
        my $base_p = $index_to_p[$i];
        my $p = $base_p;

        # a wall here can happen when boxes are converted to walls
        # in order to find possible moves of a single box
        next if vec($brd, $p, 8) & WALL;

        for my $j (0 .. 3) {
            $active->[$i * 4 + $j] = 1
                if (vec($brd, $p + $delta_p[$j], 8) & WALL) == 0;
        }
    }
    return;
}

sub make_holes_inactive ($brd, $gd) {
    # this routine identifies cases such as
    #
    #     @        $
    #    #@#      # #    (maybe target in the hole)
    #     #        #
    #
    # and makes it impossible to position the player in the hole, closed by a box

    my $active = $gd->{'active'};

    for my $p (0 .. $ncells - 1) {
        next if vec($inner, $p, 8) == 0;
        next if vec($brd, $p, 8) & OCCUPIED;

        my $sum = grep {vec($brd, $p + $_, 8) == WALL} @delta_p;
        next if $sum != 3;

        for my $i (0 .. 3) {
            my $bp = $p + $delta_p[$i];
            next if vec($brd, $bp, 8) == WALL;
            next if vec($inner, $bp, 8) == 0;

            my $index = $y_x_to_index_table[$bp] * 4;

            if (vec($brd, $p, 8) & SOKOBAN) {
                if (vec($brd, $bp, 8) & SOKOBAN) {
                    $active->[$index + (($i + 2) & 3)] = 0;
                }
            }

            if ((vec($brd, $p, 8) & SOKOBAN) == 0) {
                $active->[$index + (($i + 2) & 3)] = 0;
            }
        }
    }
    return;
}

sub init_shift ($brd, $gd) {

    my $active = $gd->{'active'};
    my $shift  = $gd->{'shift'};
    my @zones;

    @$shift = (0) x ($gd->{'vertices_num'} * 4);

    for my $i (0 .. $index_num - 1) {
        my $p = $index_to_p[$i];

        next if vec($brd, $p, 8) & OCCUPIED;

        vec($brd, $p, 8) |= BOX;
        mark_connectivities_around_place($brd, \@zones, $p);

        vec($brd, $p, 8) &= 0xFF ^ BOX;

        for my $from (0 .. 3) {
            next if $active->[$i * 4 + $from] == 0;
            my $zf = $zones[$p + $delta_p[$from]];
            next if $zf == 1000000;

            for my $to (0 .. 3) {
                next if $to == $from;
                next if $active->[$i * 4 + $to] == 0;
                my $zt = $zones[$p + $delta_p[$to]];
                next if $zt == 1000000;

                $shift->[($i * 4 + $from) * 4 + $to] = $i * 4 + $to
                    if $zf == $zt;
            }
        }
    }    # index of box
    return;
}

sub init_push ($brd, $gd) {
    my $active = $gd->{'active'};
    my $push   = $gd->{'push'};

    for my $i (0 .. $gd->{'vertices_num'} - 1) {
        next if $active->[$i] == 0;

        my $base_p = $index_to_p[int($i / 4)];

        Carp::confess('something is bad')
            if vec($brd, $base_p, 8) & OCCUPIED;

        my $push_p = $base_p - $delta_p[$i % 4];

        if (vec($brd, $push_p, 8) & OCCUPIED) {
            $push->[$i] = 0;
        }
        else {
            $push->[$i] = $y_x_to_index_table[$push_p] * 4 + ($i % 4);
        }
    }
    return;
}

sub init_pull ($brd, $gd) {
    my $active = $gd->{'active'};
    my $pull   = $gd->{'pull'};

    for my $i (0 .. $gd->{'vertices_num'} - 1) {
        next if $active->[$i] == 0;

        my $base_p = $index_to_p[int($i / 4)];

        Carp::confess('something is bad')
            if vec($brd, $base_p, 8) & OCCUPIED;

        $pull->[$i] = 0;

        next if vec($brd, $base_p + $delta_p[$i % 4] * 2, 8) & OCCUPIED;

        $pull->[$i] = $y_x_to_index_table[$base_p + $delta_p[$i % 4]] * 4 + ($i % 4);
    }
    return;
}

sub set_graph_weights_to_infinity ($gd) {
    my $n = $gd->{'vertices_num'};

    @{$gd->{'weight'}}     = (1000000) x $n;
    @{$gd->{'src'}}        = (-1) x $n;
    @{$gd->{'reversible'}} = (0) x $n;
    return;
}

sub build_graph ($brd, $pull_mode, $gd) {
    # set up the active vertices and edges, don't compute anything yet

    Carp::confess('boxes in board') if (($brd &. $BOX_ONLY) =~ tr/\x00//c);

    init_active($brd, $gd);
    init_shift($brd, $gd);

    if ($pull_mode) {init_pull($brd, $gd);}
    else            {init_push($brd, $gd);}

    set_graph_weights_to_infinity($gd);
    return;
}

sub clear_weight_around_cell ($index, $gd) {
    my $active = $gd->{'active'};
    my $weight = $gd->{'weight'};

    for my $j (0 .. 3) {
        $weight->[$index * 4 + $j] = 0 if $active->[$index * 4 + $j];
    }
    return;
}

sub do_graph_iterations ($pull_mode, $gd) {
    my (@current, @next, @visited);

    my $active = $gd->{'active'};
    my $weight = $gd->{'weight'};
    my $src    = $gd->{'src'};
    my $shift  = $gd->{'shift'};
    my $step   = $pull_mode ? $gd->{'pull'} : $gd->{'push'};

    @visited = (0) x $gd->{'vertices_num'};

    # init from start vertices
    for my $i (0 .. $gd->{'vertices_num'} - 1) {
        if ($weight->[$i] == 0) {
            $src->[$i] = -1;
            push @next, $i;
            $visited[$i] = 1;
        }
    }

    while (@next) {
        @current = @next;
        @next    = ();

        for my $v (@current) {
            for my $j (0 .. 3) {
                my $next_vertex = $shift->[$v * 4 + $j];
                next if $next_vertex == 0;

                Carp::confess('internal error1')
                    if $active->[$next_vertex] == 0;

                next if $visited[$next_vertex];

                $visited[$next_vertex]  = 1;
                $weight->[$next_vertex] = $weight->[$v];
                $src->[$next_vertex]    = $v;
                push @next, $next_vertex;
            }

            my $next_vertex = $step->[$v];
            next if $next_vertex == 0;

            Carp::confess('internal error2')
                if $active->[$next_vertex] == 0;

            next if $visited[$next_vertex];
            $visited[$next_vertex]  = 1;
            $weight->[$next_vertex] = $weight->[$v] + 1;
            $src->[$next_vertex]    = $v;
            push @next, $next_vertex;
        }    # loop on current vertices with weight d
    }    # while next d
    return;
}

sub get_weight_around_cell ($index, $gd) {
    my $min    = 1000000;
    my $active = $gd->{'active'};
    my $weight = $gd->{'weight'};

    for my $j (0 .. 3) {
        next if $active->[$index * 4 + $j] == 0;

        $min = $weight->[$index * 4 + $j] if $weight->[$index * 4 + $j] < $min;
    }
    return $min;
}

sub get_box_moves_from_graph ($start_index, $gd) {    # returns the move list
    my @moves;
    my $weight     = $gd->{'weight'};
    my $src        = $gd->{'src'};
    my $reversible = $gd->{'reversible'};

    for my $i (0 .. $index_num - 1) {
        my $p = $index_to_p[$i];

        # can't push box here - probably simple deadlock
        next if vec($gd->{'current_impossible_board'}, $p, 8);

        for my $j (0 .. 3) {
            next if $weight->[$i * 4 + $j] == 1000000;

            # this is one of the start positions - not a push
            next if $weight->[$i * 4 + $j] == 0;

            # last move was not a push, but a sokoban move
            next if int($src->[$i * 4 + $j] / 4) == $i;

            push @moves, {
                'from'             => $start_index,
                'to'               => $i,
                'sokoban_position' => $j,
                'kill'             => 0,
                'base'             => 0,
                'attr'             => {
                    'weight'     => 0,
                    'advisor'    => 0,
                    'reversible' => $reversible->[$i * 4 + $j],
                },
            };
        }
    }
    return @moves;
}


sub find_targets_of_a_group ($brd, $group, $group_size) {

    my $gd = allocate_graph();

    build_graph($brd, 0, $gd);    # 0 - push mode

    for my $i (0 .. $group_size - 1) {
        clear_weight_around_cell($group->[$i], $gd);
    }

    do_graph_iterations(0, $gd);    # 0 - push mode

    my @tmp_targets = grep {
        get_weight_around_cell($_, $gd) != 1000000
            or in_group($_, $group, $group_size)
    } 0 .. $index_num - 1;

    my $targets;
    $targets = $ZERO_BOARD;
    for my $i (@tmp_targets) {
        my $p = $index_to_p[$i];
        vec($targets, $p, 8) = 1;
    }

    return $targets;
}

sub find_targets_of_a_board_input ($brd, $in) {
    my @group;

    for my $p (0 .. $ncells - 1) {
        next if vec($inner, $p, 8) == 0;

        push @group, $y_x_to_index_table[$p] if vec($in, $p, 8);
    }

    return find_targets_of_a_group($brd, \@group, scalar @group);
}


sub find_targets_of_place_without_init_graph ($start_p, $gd) {

    my $weight = $gd->{'weight'};

    my $targets;
    $targets = $ZERO_BOARD;
    set_graph_weights_to_infinity($gd);
    clear_weight_around_cell($y_x_to_index_table[$start_p], $gd);

    do_graph_iterations(0, $gd);

    for my $i (0 .. $gd->{'vertices_num'} - 1) {
        if ($weight->[$i] != 1000000) {
            my $p = $index_to_p[int($i / 4)];
            vec($targets, $p, 8) = 1;
        }
    }

    vec($targets, $start_p, 8) = 1;
    return $targets;
}

sub find_distance_from_a_group ($brd, $group, $dist, $pull_mode) {
    my $gd = allocate_graph();

    build_graph($brd, $pull_mode, $gd);

    for my $i (0 .. $index_num - 1) {
        my $p = $index_to_p[$i];
        clear_weight_around_cell($i, $gd) if vec($group, $p, 8);
    }

    do_graph_iterations($pull_mode, $gd);

    @$dist = (1000000) x $ncells;

    for my $i (0 .. $index_num - 1) {
        my $p = $index_to_p[$i];
        $dist->[$p] = get_weight_around_cell($i, $gd);
    }
    return;
}

sub update_shift ($brd, $p, $gd) {
    # using the sokoban cloud, mark which shifts are possible
    my $shift = $gd->{'shift'};

    my $index = $y_x_to_index_table[$p] * 4;

    my @has_sokoban =
        map {(vec($brd, $p + $delta_p[$_], 8) & SOKOBAN) ? 1 : 0} 0 .. 3;

    for my $from (0 .. 3) {
        next if $has_sokoban[$from] == 0;

        for my $to (0 .. 3) {
            $shift->[($index + $from) * 4 + $to] = $index + $to
                if $has_sokoban[$to];
        }
    }
    return;
}

sub mark_box_moves_in_graph ($b_in, $box_index, $pull_mode, $gd) {
    my $brd;
    $brd = $b_in;

    my $weight = $gd->{'weight'};
    my $src    = $gd->{'src'};

    my $d = 0;
    my (@current, @next);

    @{$gd->{'shift'}} = (0) x ($gd->{'vertices_num'} * 4);

    set_graph_weights_to_infinity($gd);

    my $box_p = $index_to_p[$box_index];
    if ((vec($brd, $box_p, 8) & BOX) == 0) {
        Carp::confess('missing box3');
    }

    for my $i (0 .. 3) {
        if (vec($brd, $box_p + $delta_p[$i], 8) & SOKOBAN) {
            $weight->[$box_index * 4 + $i] = $d;
            push @current, $box_index * 4 + $i;
        }
    }

    vec($brd, $box_p, 8) &= 0xFF ^ BOX;

    # invariant: queue contains box locations and all nearby player positions.
    # all that is left is to push/pull

    while (@current) {
        $d++;
        @next = ();

        for my $index (@current) {
            my $direction = $index & 3;
            $box_p = $index_to_p[int($index / 4)];

            my $sok_p = $box_p + $delta_p[$direction];

            my ($next_box_p, $next_sok_p);

            if ($pull_mode == 0) {
                $next_box_p = $box_p - $delta_p[$direction];
                $next_sok_p = $sok_p - $delta_p[$direction];

                next if vec($brd, $next_box_p, 8) & OCCUPIED;
            }
            else {
                $next_box_p = $box_p + $delta_p[$direction];
                $next_sok_p = $sok_p + $delta_p[$direction];

                next if vec($brd, $next_sok_p, 8) & OCCUPIED;
            }

            next if vec($gd->{'current_impossible_board'}, $next_box_p, 8);

            my $next_index = $y_x_to_index_table[$next_box_p] * 4 + $direction;

            next if $weight->[$next_index] != 1000000;

            # so the box can be pushed there, and this is a new move. now compute surroundings

            $weight->[$next_index] = $d;
            $src->[$next_index]    = $index;
            push @next, $next_index;
            my $index_after_push = $next_index;

            $brd &.= $NOT_SOKOBAN;
            vec($brd, $next_box_p, 8) |= BOX;
            vec($brd, $next_sok_p, 8) |= SOKOBAN;
            $brd = expand_sokoban_cloud($brd);

            update_shift($brd, $next_box_p, $gd);

            my $next_box_index4 = $y_x_to_index_table[$next_box_p] * 4;
            for my $j (0 .. 3) {
                next
                    if (vec($brd, $next_box_p + $delta_p[$j], 8) & SOKOBAN) == 0;

                $next_index = $next_box_index4 + $j;

                next if $weight->[$next_index] != 1000000;

                $weight->[$next_index] = $d;
                $src->[$next_index]    = $index_after_push;
                push @next, $next_index;
            }

            vec($brd, $next_box_p, 8) &= 0xFF ^ BOX;
        }    # current_size

        @current = @next;
    }    # BFS queue
    return;
}

# some routines to detect reversible moves

sub find_reversible_moves ($brd, $box_index, $pull_mode, $gd) {

    my (@current, @next, @visited);

    my $src        = $gd->{'src'};
    my $reversible = $gd->{'reversible'};

    @visited = (0) x $gd->{'vertices_num'};

    my $box_p = $index_to_p[$box_index];

    Carp::confess('missing box4')
        if (vec($brd, $box_p, 8) & BOX) == 0;

    vec($brd, $box_p, 8) &= 0xFF ^ BOX;

    # maintain a list of indices such that:
    # all of them are reachable from the start (tested using "src" value)
    # all of them can lead to the start (verified by pulling the boxes)

    @$reversible = (0) x $gd->{'vertices_num'};

    for my $i (0 .. 3) {
        next if (vec($brd, $box_p + $delta_p[$i], 8) & SOKOBAN) == 0;
        my $index = $box_index * 4 + $i;

        $reversible->[$index] = 1;
        push @current, $index;
        $visited[$index] = 1;
    }

    while (@current) {
        @next = ();
        for my $index (@current) {

            # try shifts
            for my $j (0 .. 3) {
                my $next_index = ($index & ~3) + $j;

                next if $visited[$next_index];

                if ((($index ^ $next_index) >> 2 ? Carp::confess('bad call') : 0, $gd->{'shift'}[$index * 4 + ($next_index & 3)] == $next_index ? 1 : 0)[1]) {
                    if ($src->[$next_index] != -1) {
                        push @next, $next_index;
                        $reversible->[$next_index] = 1;
                        $visited[$next_index] = 1;
                    }
                }
            }

            # try pull

            $box_p = $index_to_p[$index >> 2];
            my $direction = $index & 3;

            my $sok_p = $box_p + $delta_p[$direction];

            Carp::confess('back problem')
                if vec($brd, $sok_p, 8) & OCCUPIED;

            if ($pull_mode == 0) {
                $sok_p += $delta_p[$direction];
                $box_p += $delta_p[$direction];

                next if vec($brd, $sok_p, 8) & OCCUPIED;
            }
            else {
                $box_p -= $delta_p[$direction];

                next if vec($brd, $box_p, 8) & OCCUPIED;
            }

            my $next_index = $y_x_to_index_table[$box_p] * 4 + $direction;

            next if vec($gd->{'current_impossible_board'}, $box_p, 8);
            next if $visited[$next_index];

            if ($src->[$next_index] != -1) {
                push @next, $next_index;
                $reversible->[$next_index] = 1;
                $visited[$next_index] = 1;
            }
        }    # i

        @current = @next;
    }    # while current

    vec($brd, $index_to_p[$box_index], 8) |= BOX;
    return;
}

sub set_current_impossible ($b_in, $box_p, $pull_mode, $search_mode, $possible_board, $gd) {
    my $brd;
    $brd = $b_in;

    my $cib;
    $cib = $ZERO_BOARD;

    for my $i (0 .. $index_num - 1) {
        my $p = $index_to_p[$i];

        # general impossible places of the level. board edges etc.
        vec($cib, $p, 8) = 1
            if $impossible_place[$i];

        # add boxes that were wallified
        vec($cib, $p, 8) = 1 if vec($brd, $p, 8) == WALL;
    }

    if ($pull_mode == 0) {    # pull mode can't pull to 2x2 patterns
        vec($brd, $box_p, 8) &= 0xFF ^ BOX;

        my $blocked;
        $blocked = mark_deadlock_2x2($brd);

        for my $p (0 .. $ncells - 1) {
            next if vec($inner, $p, 8) == 0;
            vec($cib, $p, 8) = 1 if vec($blocked, $p, 8);
        }
    }

    for my $p (0 .. $ncells - 1) {
        next if vec($inner, $p, 8) == 0;
        vec($cib, $p, 8) = 1 if vec($possible_board, $p, 8) == 0;
    }

    $gd->{'current_impossible_board'} = $cib;
    return;
}

# ====================================================================
# Games::Sokoban::Fest::Rooms  (was lib2/Games/Sokoban/Fest/Rooms.pm)
# ====================================================================

# Port of festival/rooms.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 translation: P4 throughout. rooms_bfs is a flat wavefront (the C
# parallel x/y buffer pairs are gone) and now takes a flat start position;
# the scans that drive it and fill rooms_board are single loops over
# $ncells, and the 1000000 fill is one list assignment. Order-safe: what a
# wave produces (which rooms it saw, which cells it marked) does not depend
# on the visit order inside the wave, and ascending flat order == the C
# row-major order for the scans that ARE order-sensitive.
# Left as y/x on purpose: the 2x2 square detector (ranges 0..height-2,
# 0..width-2) -- its edge-awareness is the loop bounds, and rebuilding the
# column guard flat would need a modulo per cell.
#
# Rooms = connected components of 2x2-free areas
# (corridors excluded); rooms_board labels each cell with its room color
# (1000000 = corridor/none); base_graph[i][j] = 1 when rooms i and j are
# mutually reachable on the empty board; score_rooms() counts connections
# LOST versus that baseline.
# The C original's edge reads outside the active region (row -1 above a
# 'squares' cell, column width in the shared-cells sweep) never fire on a
# wall-enclosed level: the border rows/columns can never hold a 2x2 square,
# so every guarding condition fails before the out-of-range value is used
# -- verified cell by cell before porting to the flat index.
#
# Exports follow rooms.h; rooms_bfs / get_current_graph / new_mark_rooms
# stay package-internal. base_graph is file-local.
#
# Globals ledger:
#   reads:  $height $width $ncells @delta_y @delta_x $inner
#   writes: $rooms_board (flat int_board arrayref) $rooms_num
#           $global_fail_reason (analyse_rooms, "too many rooms")

# file-scope but NOT static in C => external linkage; 'our' matches that
# (not exported -- access fully qualified, like the C extern)

sub rooms_bfs ($brd, $start_p, $color, $seen, $visited) {
    # this BFS is allowed to spread either in "color" room or in corridors.
    # It stops when it reaches other rooms.
    # P4: one flat wavefront instead of the C parallel x/y buffer pairs.
    # Safe because what the wave produces -- which rooms were seen and which
    # cells got marked -- does not depend on the visit order inside a wave.

    my $bfs_visited;
    $bfs_visited = $ZERO_BOARD;

    @$seen = (0) x $rooms_num;

    my @current = ($start_p);
    vec($visited, $start_p, 8) = 1;
    vec($bfs_visited, $start_p, 8) = 1;

    while (@current) {
        my @next;
        for my $p (@current) {
            for my $j (0 .. 3) {
                my $np = $p + $delta_p[$j];

                my $seen_color = $rooms_board->[$np];
                if ($seen_color != 1000000 and $seen_color != $color) {
                    $seen->[$seen_color] = 1;
                    next;
                }

                next if vec($bfs_visited, $np, 8);   # handled during current BFS
                next if vec($visited, $np, 8);           # handled during previous BFSs
                next if vec($brd, $np, 8) & OCCUPIED;

                vec($bfs_visited, $np, 8) = 1;       # this is mostly for corridors

                # this is for next BFS searches
                vec($visited, $np, 8) = 1 if $seen_color == $color;

                push @next, $np;
            }    # j = 0..3
        }

        @current = @next;
    }
    return $visited;
}

sub get_current_graph ($brd, $current_graph) {    # current_graph = AoA arrayref
    my @seen_during_bfs;
    my @color_processed;
    my $visited;

    $visited = $ZERO_BOARD;
    # visited are the color rooms seen in previous BFSs

    for my $i (0 .. $rooms_num - 1) {
        for my $j (0 .. $rooms_num - 1) {
            $current_graph->[$i][$j] = 1;
        }
    }

    for my $i (0 .. $rooms_num - 1) {
        $current_graph->[$i][$i] = 0;
    }

    for my $i (0 .. $rooms_num - 1) {
        $color_processed[$i] = 0;
    }

    # P4: ascending flat order == the C original's row-major order, so the
    # order in which rooms are visited (which the graph edits depend on) is
    # unchanged
    for my $p (0 .. $ncells - 1) {
        next if vec($inner, $p, 8) == 0;
        next if vec($brd, $p, 8) & OCCUPIED;
        next if vec($visited, $p, 8);

        my $color = $rooms_board->[$p];
        next if $color == 1000000;

        $color_processed[$color] = 1;

        $visited = rooms_bfs($brd, $p, $color, \@seen_during_bfs, $visited);

        for my $k (0 .. $rooms_num - 1) {
            if ($seen_during_bfs[$k] == 0) {
                $current_graph->[$color][$k] = 0;
                $current_graph->[$k][$color] = 0;
            }
        }
    }

    # apply correction for rooms full of boxes
    for my $i (0 .. $rooms_num - 1) {
        if ($color_processed[$i] == 0) {
            for my $j (0 .. $rooms_num - 1) {
                $current_graph->[$i][$j] = 0;
                $current_graph->[$j][$i] = 0;
            }
        }
    }
    return;
}

sub new_mark_rooms ($brd) {
    my $squares;
    my @tmp_rooms_board;

    $squares = $ZERO_BOARD;

    for my $i (0 .. $height - 2) {
        for my $j (0 .. $width - 2) {
            my $p = $i * $width + $j;
            if (    vec($brd, $p, 8) == 0
                and vec($brd, $p + 1, 8) == 0
                and vec($brd, $p + $width, 8) == 0
                and vec($brd, $p + $width + 1, 8) == 0)
            {
                vec($squares, $p, 8) = 1;
            }
        }
    }

    # remove stand-alone squares - too small to be considered rooms
    # (a border cell can never hold a square, so p +- width stays in range)

    for my $p (0 .. $ncells - 1) {
        if (    vec($squares, $p, 8) == 1
            and vec($squares, $p - $width, 8) == 0
            and vec($squares, $p + 1, 8) == 0
            and vec($squares, $p + $width, 8) == 0
            and vec($squares, $p - 1, 8) == 0)
        {
            vec($squares, $p, 8) = 0;
        }
    }

    # look for connected components
    $squares = negate_board($squares);

    $rooms_num = mark_connectivities($squares, \@tmp_rooms_board);

    @$rooms_board = (1000000) x $ncells;

    for my $p (0 .. $ncells - 1) {
        my $v = $tmp_rooms_board[$p];
        next if $v == 1000000;

        $rooms_board->[$p] = $v;
        $rooms_board->[$p + 1] = $v;
        $rooms_board->[$p + $width] = $v;
        $rooms_board->[$p + $width + 1] = $v;
    }

    # remove cells shared between rooms
    # (the C original reads one row/column past the active region here;
    # on an enclosed level the condition can never fire there, and our
    # flat reads see 0 / the next row's border wall square value 0 --
    # same net effect: no write)

    for my $p (0 .. $ncells - 1) {
        if (    vec($squares, $p, 8) == vec($squares, $p + $width + 1, 8)
            and vec($squares, $p + $width, 8) == vec($squares, $p + 1, 8)
            and vec($squares, $p, 8) != vec($squares, $p + $width, 8))
        {
            $rooms_board->[$p + $width + 1] = 1000000;
        }
    }
    return;
}

sub analyse_rooms ($b_inp) {
    my ($brd, $c);
    my @current_graph;

    $brd = $b_inp &. $NOT_BOX;
    $brd &.= $NOT_SOKOBAN;
    $brd &.= $NOT_TARGET;

    new_mark_rooms($brd);


    if ($rooms_num > MAX_ROOMS) {
        $global_fail_reason = 'too many rooms';
        $rooms_num = 0;
        return 1;
    }


    $c = $brd &. $NOT_BOX;
    get_current_graph($c, \@current_graph);

    for my $i (0 .. $rooms_num - 1) {
        for my $j (0 .. $rooms_num - 1) {
            $base_graph[$i][$j] = $current_graph[$i][$j];
        }
    }

    return 1;
}

sub score_rooms ($brd) {
    my $sum = 0;
    my @current_graph;

    return 0 if $rooms_num <= 1;

    get_current_graph($brd, \@current_graph);

    for my $i (0 .. $rooms_num - 1) {
        for my $j (0 .. $rooms_num - 1) {
            $sum += $base_graph[$i][$j] - $current_graph[$i][$j];
        }
    }

    Carp::confess('odd') if $sum % 2;

    return $sum / 2;
}

# ====================================================================
# Games::Sokoban::Fest::Snail  (was lib2/Games/Sokoban/Fest/Snail.pm)
# ====================================================================

# Port of festival/snail.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 pass: one P4 (a plain whole-board fill is a list assignment).
# The other y/x scans STAY, and here that is more than the usual reason:
# the netlock detector reasons about the PARITY of a cell's row and of its
# column separately (an every-other-cell anchor grid), so the two axes
# genuinely mean different things in this module. The rest feed helpers
# that take y/x.
#
# Detects "snail" levels (a long connected chain of
# targets that must be packed in strict order, like Sokevo/snail puzzles):
# for each empty target, put a box on it in the solved position and measure
# how many pull layers it takes before that box can move (compute_pull_order
# peels pullable boxes layer by layer). A depth >= 20 flags a snail level
# (the target chain is analyzed into snail_dist/snail_chain), depth >= 10
# flags the milder "netlock" variant (a parity grid of anchor cells).
# set_snail_parameters / set_netlock_parameters then reroute the standard
# strategies to the SNAIL/NETLOCK scoring modes.
#
# Globals ledger:
#   reads:  $height $width @delta_y @delta_x @delta_y_8 @delta_x_8
#           Global::$global_boxes_in_level Board::$initial_board Board::$inner
#   writes: $snail_level_detected $snail_target_y $snail_target_x
#           $netlock_level_detected $netlock_grid
#           $snail_dist $snail_chain $snail_chain_len (module-own)

($snail_target_y, $snail_target_x) = (0, 0);

sub set_netlock_grid () {
    $netlock_grid = $ZERO_BOARD;
    for my $i (0 .. $height - 1) {
        for my $j (0 .. $width - 1) {
            if (vec($inner, $i * $width + $j, 8)) {
                if ((($i ^ $snail_target_y) & 1) == 0) {
                    if ((($j ^ $snail_target_x) & 1) == 0) {
                        vec($netlock_grid, $i * $width + $j, 8) = 1;
                    }
                }
            }
        }
    }

    return;
}

sub simple_box_can_be_pulled ($brd, $p) {
    # ignores player's position

    for my $i (0 .. 3) {
        if ((vec($brd, $p + $delta_p[$i], 8) & OCCUPIED) == 0) {
            return 1
                if (vec($brd, $p + 2 * $delta_p[$i], 8) & OCCUPIED) == 0;
        }
    }
    return 0;
}

sub pullable_boxes ($brd) {
    my $res = 0;

    for my $p (0 .. $ncells - 1) {
$res += simple_box_can_be_pulled($brd, $p)
if vec($brd, $p, 8) & BOX;
}
    return $res;
}

sub compute_pull_order ($b_in, $order) {
    my ($brd, $visited);

    my (@current, @next);
    my $current_num = 0;
    my $next_num;

    my $depth = 0;

    $brd = $b_in;
    $visited = $ZERO_BOARD;

    @$order = (-1) x $ncells;    # P4: a plain fill is one list assignment

    # initialize the first layer of pullable boxes
    for my $p (0 .. $ncells - 1) {
if (vec($brd, $p, 8) & BOX) {
if (simple_box_can_be_pulled($brd, $p)) {
vec($visited, $p, 8) = 1;
$current[$current_num++] = $y_x_to_index_table[$p];
}
}
}

    while ($current_num) {
        # remove current layer
        for my $i (0 .. $current_num - 1) {
            my $p = $index_to_p[$current[$i]];
            $order->[$p] = $depth;
            vec($brd, $p, 8) &= 0xFF ^ BOX;
        }

        $next_num = 0;
        $depth++;

        for my $i (0 .. $current_num - 1) {
            my $p = $index_to_p[$current[$i]];

            for my $j (0 .. 3) {
                my $box_p = $p + $delta_p[$j];

                next if (vec($brd, $box_p, 8) & BOX) == 0;
                next if vec($visited, $box_p, 8);
                next if vec($brd, $p - $delta_p[$j], 8) & OCCUPIED;

                vec($visited, $box_p, 8) = 1;
                $next[$next_num++] = $y_x_to_index_table[$box_p];
            }

            for my $j (0 .. 3) {
                next if vec($brd, $p + $delta_p[$j], 8) & OCCUPIED;

                my $box_p = $p + $delta_p[$j] * 2;

                next if (vec($brd, $box_p, 8) & BOX) == 0;
                next if vec($visited, $box_p, 8);

                vec($visited, $box_p, 8) = 1;
                $next[$next_num++] = $y_x_to_index_table[$box_p];
            }
        }

        for my $i (0 .. $next_num - 1) {
            $current[$i] = $next[$i];
        }
        $current_num = $next_num;
    }

    if ((($brd &. $BOX_ONLY) =~ tr/\x00//c) > 0) {
        # remaining boxes are crystalline-stuck
        return;    # order will be -1
    }
    return;
}

sub analyze_chain ($brd) {
    my $max_val = -1;
    my $peel_from_p;

    my $not_targets;
    $not_targets = $ZERO_BOARD;
    for my $p (0 .. $ncells - 1) {
vec($not_targets, $p, 8) =
(vec($brd, $p, 8) & TARGET ? 0 : 1);
}

    # find the connected chain
    @{$snail_dist} = (1000000) x $ncells;
    bfs_from_place($not_targets, $snail_dist, $snail_target_y * $width + $snail_target_x, 1);

    # determine where the chain starts (which box must be pulled first)

    $snail_chain_len = -1;
    $snail_chain = $ZERO_BOARD;

    for my $p (0 .. $ncells - 1) {
next if $snail_dist->[$p] == 1000000;

vec($snail_chain, $p, 8) = 1;
if ($snail_dist->[$p] > $snail_chain_len) {
$snail_chain_len = $snail_dist->[$p];
$peel_from_p     = $p;
}
}

    @{$snail_dist} = (1000000) x $ncells;
    bfs_from_place($not_targets, $snail_dist, $peel_from_p, 1);

    for my $p (0 .. $ncells - 1) {
if ($snail_dist->[$p] != 1000000) {
$snail_dist->[$p] =
$snail_chain_len - $snail_dist->[$p];
}
}

    $snail_chain_len++;

    return;
}

sub detect_snail_level ($b_in) {
    my $brd;
    my $order          = [];
    my $max_difficulty = -1;

    $snail_level_detected   = 0;
    $netlock_level_detected = 0;

    $brd = $b_in;
    $brd = enter_reverse_mode($brd, 0);

    for my $p (0 .. $ncells - 1) {
if ((vec($initial_board, $p, 8) & BOX) == 0) {
vec($brd, $p, 8) &= 0xFF ^ BOX;
}
}

    for my $i (0 .. $height - 1) {
        for my $j (0 .. $width - 1) {
            next if (vec($brd, $i * $width + $j, 8) & TARGET) == 0;
            next if vec($initial_board, $i * $width + $j, 8) & BOX;

            vec($brd, $i * $width + $j, 8) |= BOX;
            compute_pull_order($brd, $order);
            vec($brd, $i * $width + $j, 8) &= 0xFF ^ BOX;

            if ($order->[$i * $width + $j] > $max_difficulty) {
                $max_difficulty = $order->[$i * $width + $j];
                $snail_target_y = $i;
                $snail_target_x = $j;
            }
        }
    }

    set_netlock_grid();

    if ($max_difficulty >= 20) {
        $snail_level_detected = 1;

        analyze_chain($brd);
        return;
    }

    if ($max_difficulty >= 10) {

        $netlock_level_detected = 1;
    }
    return;
}

sub touched_boxes ($brd) {
    my $sum = 0;

    for my $p (0 .. $ncells - 1) {
next if (vec($brd, $p, 8) & BOX) == 0;

my $k;
for ($k = 0; $k < 4; $k++) {
last if vec($brd, $p + $delta_p[$k], 8)
& SOKOBAN;
}
$sum++ if $k < 4;
}
    return $sum;
}

sub count_101 ($brd) {
    my $sum = 0;

    for my $p (0 .. $ncells - 1) {
if (vec($brd, $p, 8) & BOX) {
if ((vec($brd, $p + 1, 8) & OCCUPIED) == 0) {
$sum++ if vec($brd, $p + 2, 8) & BOX;
}

if ((vec($brd, $p + $width, 8) & OCCUPIED) == 0) {
$sum++ if vec($brd, $p + 2 * $width, 8) & BOX;
}
}
}

    return $sum;
}

sub unlikely_pattern ($brd) {
    my $res = 0;

    for my $p (0 .. $ncells - 1) {
next if (vec($brd, $p, 8) & BOX) == 0;

my $sum = 0;
for my $k (0 .. 7) {
$sum++
if vec($brd,
$p + $delta_p_8[$k], 8)
& OCCUPIED;
}
$res++ if $sum >= 6;
}
    return $res;
}

sub snail_packed ($brd) {
    my @seq;

    for my $i (0 .. $snail_chain_len - 1) {
        $seq[$i] = 1;
    }

    for my $p (0 .. $ncells - 1) {
if (vec($snail_chain, $p, 8)) {
if ((vec($brd, $p, 8) & BOX) == 0) {
$seq[$snail_dist->[$p]] = 0;
}
}
}

    my $i;
    for ($i = 1; $i < $snail_chain_len; $i++) {
        return $i if $seq[$i] == 0;
    }

    return $i;
}

sub fill_snail_scores ($brd, $s, $alg_type) {
    if (vec($brd, $snail_target_y * $width + $snail_target_x, 8) & BOX) {
        $s->{'out_of_plan'} = 1;    # not solved yet
    }
    else {
        $s->{'out_of_plan'} = 0;
    }

    $s->{'dist_to_imagined'} = unlikely_pattern($brd) if $alg_type == 0;

    $s->{'biconnect'} = $global_boxes_in_level - touched_boxes($brd);

    if ($s->{'out_of_plan'} == 1) {    # did not solve yet
        $s->{'hotspots'} = count_101($brd) if $alg_type == 0;
    }
    else {
        $s->{'boxes_on_targets'} = snail_packed($brd);
    }
    return;
}


# netlock code starts here

sub netlock_score ($brd) {
    my $c;
    my $order = [];

    return 0
        if (vec($brd, $snail_target_y * $width + $snail_target_x, 8) & BOX) == 0;

    $c = $brd;

    compute_pull_order($c, $order);

    my $res = $order->[$snail_target_y * $width + $snail_target_x];

    if (vec($brd, $snail_target_y * $width + $snail_target_x, 8) & BOX) {
        return 1000 if $res == -1;
    }

    return $res;
}

sub boxes_on_grid ($brd) {
    my $sum = 0;

    for my $p (0 .. $ncells - 1) {
if (vec($netlock_grid, $p, 8)) {
$sum++ if vec($brd, $p, 8) & BOX;
}
}

    return $sum;
}

sub fill_netlock_scores ($brd, $s, $alg_type) {
    $s->{'connectivity'}     = get_connectivity($brd);
    $s->{'boxes_on_targets'} = netlock_score($brd);
    $s->{'rooms_score'}      = boxes_on_grid($brd);

    if ($s->{'boxes_on_targets'} == 0) {    # solved level
        $s->{'imagine'} = pullable_boxes($brd);

        # an alternative for type 0
        # $s->{'rooms_score'} = ($brd =~ tr/\x06\x16//);
        # $s->{'imagine'}     = count_101($brd);
    }
    else {
        if ($alg_type == 0) {
            $s->{'rooms_score'} = count_101($brd);
            $s->{'imagine'}     = boxes_on_grid($brd);
        }

        $s->{'imagine'} = pullable_boxes($brd) if $alg_type == 2;
    }

    if ($alg_type == 3) {
        $s->{'rooms_score'} = ($brd =~ tr/\x06\x16//);
        $s->{'imagine'}     = count_101($brd);
    }
    return;
}


# ====================================================================
# Games::Sokoban::Fest::Deadlock  (was lib2/Games/Sokoban/Fest/Deadlock.pm)
# ====================================================================

# Port of festival/deadlock.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. Contents:
#   - the 16+9 textfile deadlock patterns, expanded by rotations+flips into
#     runtime pattern records {pat => AoA, y, x, box_shift_y, box_shift_x}
#     matched by exact byte compare ('?' = 0xff wildcard);
#   - set_forbidden_tunnel (wall-flanked tunnels a push/pull may not stop
#     in), mark_deadlock_2x2, deadlock_in_direction (freeze after a push),
#     is_freeze_deadlock, is_3x3_deadlock, is_inefficient_position;
#   - check_deadlock_in_moves: the per-move deadlock dispatcher.
# DEVIATION (documented): pattern matching near the board edge -- the C
# original reads garbage outside the active region (stack padding) which in
# practice never matches; here any non-'?' pattern cell outside the board
# means "no match", and the window anchor must lie inside the board. Same
# net effect, deterministic.
#
# C int-array out-parameter 'valid' becomes the return LIST of
# check_deadlock_in_moves. Cross-module calls resolved at runtime, fully
# qualified (import cycles / not-yet-ported modules):
#   Moves::apply_move Moves::print_move Moves::find_possible_moves
#   Mpdb2::is_mpdb_deadlock  PackingSearch::verify_simple_base_matching
#   Perimeter::is_in_perimeter  KDistDeadlock::sokoban_touches_a_filled_hole
#   Helper::init_helper
#
# Globals ledger:
#   reads:  $height $width $ncells @delta_y @delta_x @delta_p @delta_p_8
#           $inner $index_num $global_initial_sokoban_y/_x
#           Board::$initial_board Distance::@impossible_place
#   writes: $forbidden_push_tunnel $forbidden_pull_tunnel (boards),
# @patterns @pull_patterns (read_deadlock_patterns),

sub set_forbidden_tunnel () {
    my $brd;

    $forbidden_push_tunnel = $ZERO_BOARD;
    $forbidden_pull_tunnel = $ZERO_BOARD;

    $brd = $initial_board &. $NOT_BOX;
    $brd &.= $NOT_SOKOBAN;

    # look for
    # ######
    #
    # ######
    for my $i (1 .. $height - 2) {
        for my $j (1 .. $width - 2) {
            my $p = $i * $width + $j;

            # middle of tunnel
            next
                if vec($brd, $p - $width - 1, 8) == WALL
                and vec($brd, $p - 1, 8) != WALL
                and vec($brd, $p + $width - 1, 8) == WALL;

            my $k = 0;
            while ($k < $width) {
                last if vec($brd, $p - $width + $k, 8) != WALL;
                last if vec($brd, $p + $k, 8) == WALL;
                last if vec($brd, $p + $width + $k, 8) != WALL;
                $k++;
            }
            if ($k >= 2) {
                my $n = $k;

                my ($base, $target) = (0, 0);
                for my $m (0 .. $n - 1) {
                    $base   = 1 if vec($initial_board, $p + $m, 8) & BOX;
                    $target = 1 if vec($brd, $p + $m, 8) & TARGET;
                }

                for my $m (0 .. $n - 1) {
                    vec($forbidden_push_tunnel, $p + $m, 8) = 1;
                    vec($forbidden_pull_tunnel, $p + $m, 8) = 1;
                }

                vec($forbidden_pull_tunnel, $p, 8) = 0 if $base == 0;
                vec($forbidden_push_tunnel, $p, 8) = 0 if $target == 0;
            }
        }
    }

    # look for
    # # #
    # # #
    # # #
    for my $i (1 .. $height - 2) {
        for my $j (1 .. $width - 2) {
            my $p = $i * $width + $j;

            # middle of tunnel
            next
                if vec($brd, $p - $width - 1, 8) == WALL
                and vec($brd, $p - $width, 8) != WALL
                and vec($brd, $p - $width + 1, 8) == WALL;

            my $k = 0;
            while ($k < $height) {
                last if vec($brd, $p + $k * $width - 1, 8) != WALL;
                last if vec($brd, $p + $k * $width, 8) == WALL;
                last if vec($brd, $p + $k * $width + 1, 8) != WALL;
                $k++;
            }
            if ($k >= 2) {
                my $n = $k;

                my ($base, $target) = (0, 0);
                for my $m (0 .. $n - 1) {
                    $base   = 1 if vec($initial_board, $p + $m * $width, 8) & BOX;
                    $target = 1 if vec($brd, $p + $m * $width, 8) & TARGET;
                }

                for my $m (0 .. $n - 1) {
                    vec($forbidden_push_tunnel, $p + $m * $width, 8) = 1;
                    vec($forbidden_pull_tunnel, $p + $m * $width, 8) = 1;
                }

                vec($forbidden_pull_tunnel, $p, 8) = 0 if $base == 0;
                vec($forbidden_push_tunnel, $p, 8) = 0 if $target == 0;
            }
        }
    }

    return;
}

sub is_2x2_deadlock_at_place ($brd, $p) {
    for my $o (0, 1, $width, $width + 1) {
        return 0 if (vec($brd, $p + $o, 8) & OCCUPIED) == 0;
    }

    for my $o (0, 1, $width, $width + 1) {
        my $c = vec($brd, $p + $o, 8);
        return 1 if ($c & BOX) and ($c & TARGET) == 0;
    }
    return 0;
}

sub mark_deadlock_2x2 ($c) {
    $c &.= $NOT_SOKOBAN;

    my $d;
    $d = $ZERO_BOARD;

    for my $i (0 .. $height - 2) {
        for my $j (0 .. $width - 2) {
            my $p = $i * $width + $j;

            # look for patterns composed of 3 boxes/walls such as
            # $?
            # #$

            my ($sum, $stuck) = (0, 0);
            for my $y (0 .. 1) {
                for my $x (0 .. 1) {
                    my $val = vec($c, $p + $y * $width + $x, 8);
                    $sum++ if $val & OCCUPIED;

                    # a box or an empty square, but immobilizing a box there
                    # would be a mistake
                    $stuck++ if $val != WALL and ($val & TARGET) == 0;
                }
            }

            if ($sum == 3 and $stuck) {
                for my $y (0 .. 1) {
                    for my $x (0 .. 1) {
                        vec($d, $p + $y * $width + $x, 8) = 1;
                    }
                }
            }

            # look for pattern
            # #?
            # ?#
            if (vec($c, $p, 8) == WALL and vec($c, $p + $width + 1, 8) == WALL) {
                vec($d, $p + 1, 8) = 1 if vec($c, $p + 1, 8) == 0;
                vec($d, $p + $width, 8) = 1 if vec($c, $p + $width, 8) == 0;
            }

            # look for pattern
            # ?#
            # #?
            if (vec($c, $p + 1, 8) == WALL and vec($c, $p + $width, 8) == WALL) {
                vec($d, $p, 8) = 1 if vec($c, $p, 8) == 0;
                vec($d, $p + $width + 1, 8) = 1
                    if vec($c, $p + $width + 1, 8) == 0;
            }
        }
    }

    return $d;
}

# constants for deadlock_in_direction

sub deadlock_in_direction ($brd, $p, $d) {
    # check if a freeze deadlock will occur after pushing the box in direction d

    my $dp  = $delta_p[$d];
    my $dp2 = $delta_p[($d + 1) & 3];    # sideway
    my $np  = $p + $dp;

    return 1 if vec($inner, $np, 8) == 0;    # guards the table below
    return 1 if $impossible_place[$y_x_to_index_table[$np]];

    Carp::confess('missing box') if (vec($brd, $p, 8) & BOX) == 0;
    Carp::confess('no space') if vec($brd, $np, 8) & OCCUPIED;

    # first, look for two walls:
    #   #
    #  #$
    if ((vec($brd, $np, 8) & TARGET) == 0
        and vec($brd, $np + $dp, 8) == WALL)
    {
        return 1 if vec($brd, $np + $dp2, 8) == WALL;
        return 1 if vec($brd, $np - $dp2, 8) == WALL;
    }

    # check patterns of type
    #   1  #$   2
    #   3   $#  4
    if (vec($brd, $np + $dp, 8) & BOX) {
        my ($wall1, $wall2, $wall3, $wall4) = (0, 0, 0, 0);
        $wall4 = 1 if vec($brd, $np + $dp2, 8) == WALL;
        $wall3 = 1 if vec($brd, $np - $dp2, 8) == WALL;
        $wall2 = 1 if vec($brd, $np + $dp + $dp2, 8) == WALL;
        $wall1 = 1 if vec($brd, $np + $dp - $dp2, 8) == WALL;

        if ($wall1 + $wall4 == 2 or $wall2 + $wall3 == 2) {
            return 1 if (vec($brd, $np, 8) & TARGET) == 0;
            return 1 if (vec($brd, $np + $dp, 8) & TARGET) == 0;
        }
    }

    # temporarily push the box and check 2x2 deadlocks
    vec($brd, $p, 8) &= 0xFF ^ BOX;
    vec($brd, $np, 8) |= BOX;

    my $res_0 = is_2x2_deadlock_at_place($brd, $p + $square_place_p[$d][0]);
    my $res_1 = is_2x2_deadlock_at_place($brd, $p + $square_place_p[$d][1]);

    # restore box
    vec($brd, $np, 8) &= 0xFF ^ BOX;
    vec($brd, $p, 8) |= BOX;

    return 1 if $res_0 or $res_1;
    return 0;
}

sub box_touches_unreachable_square ($brd, $p) {
    for my $i (0 .. 7) {
        my $c = vec($brd, $p + $delta_p_8[$i], 8);
        next if $c & OCCUPIED;
        next if $c & SOKOBAN;
        return 1;
    }
    return 0;
}

sub box_is_pushable ($brd, $p) {
    # a naive check if the box can be pushed vertically or horizontally
    if ((vec($brd, $p - $width, 8) & OCCUPIED) == 0) {
        return 1 if (vec($brd, $p + $width, 8) & OCCUPIED) == 0;
    }
    if ((vec($brd, $p - 1, 8) & OCCUPIED) == 0) {
        return 1 if (vec($brd, $p + 1, 8) & OCCUPIED) == 0;
    }
    return 0;
}

sub is_freeze_deadlock ($brd, $box_p) {
    # eliminate all pushable boxes; a remaining off-target box = frozen cluster
    Carp::confess('check caller') if (vec($brd, $box_p, 8) & BOX) == 0;

    return 0 if box_is_pushable($brd, $box_p);

    my $c = $brd;

    my $changed = 1;
    while ($changed) {
        $changed = 0;

        for my $p (0 .. $ncells - 1) {
            if (vec($c, $p, 8) & BOX) {
                if (box_is_pushable($c, $p)) {
                    vec($c, $p, 8) &= 0xFF ^ BOX;
                    $changed = 1;
                }
            }
        }
    }

    for my $p (0 .. $ncells - 1) {
        if (vec($c, $p, 8) & BOX) {
            return 1 if (vec($c, $p, 8) & TARGET) == 0;
        }
    }
    return 0;
}

sub is_3x3_deadlock ($brd, $box_p) {
    # look for patterns of type
    # OO        OO
    # O O   or  O #
    #  OO       #O
    return 0 if box_touches_unreachable_square($brd, $box_p) == 0;

    for my $dy (-1 .. 1) {
        for my $dx (-1 .. 1) {
            my $p = $box_p + $dy * $width + $dx;
            next if vec($inner, $p, 8) == 0;
            next if vec($brd, $p, 8) & OCCUPIED;
            next if vec($brd, $p, 8) & TARGET;

            # surrounded by four:
            my $open = 0;
            for my $i (0 .. 3) {
                if ((vec($brd, $p + $delta_p[$i], 8) & OCCUPIED) == 0) {$open = 1; last;}
            }
            next if $open;

            # at least one box is not in place
            my $off_target = 0;
            for my $i (0 .. 3) {
                my $c = vec($brd, $p + $delta_p[$i], 8);
                if (($c & BOX) and ($c & TARGET) == 0) {$off_target = 1; last;}
            }
            next unless $off_target;

            # OO
            # O O
            #  OO
            if (vec($brd, $p - $width - 1, 8) & OCCUPIED) {
                return 1 if vec($brd, $p + $width + 1, 8) & OCCUPIED;
            }
            if (vec($brd, $p - $width + 1, 8) & OCCUPIED) {
                return 1 if vec($brd, $p + $width - 1, 8) & OCCUPIED;
            }

            # OO
            # O #
            # #O
            for (my $i = 0; $i < 8; $i += 2) {
                my $val1 = vec($brd, $p + $delta_p_8[$i], 8);
                next if $val1 != WALL;

                my $val2 = vec($brd, $p + $delta_p_8[($i + 3) & 7], 8);
                my $val3 = vec($brd, $p + $delta_p_8[($i + 5) & 7], 8);

                next if ($val2 & OCCUPIED) == 0;
                next if ($val3 & OCCUPIED) == 0;

                return 1 if $val2 == WALL or $val3 == WALL;
            }
        }
    }
    return 0;
}

# ---- textfile pattern machinery -------------------------------------------


# Per-level pattern offsets: each pattern's non-wildcard cells as FLAT
# (offset, byte) pairs for the current $width, so the matcher below runs one
# vec probe per cell with no per-cell bounds tests. maxcy/maxcx (the largest
# non-wildcard row/column) bound the whole placement instead: a placement
# whose farthest real cell falls off the board could never match, which is
# exactly the verdict the old per-cell bounds test produced.
sub prepare_pattern_offsets () {
    for my $pt (@patterns, @pull_patterns) {
        my @f;
        push @f, $_->[0] * $width + $_->[1], $_->[2] for @{ $pt->{'cells'} };
        $pt->{'flat'} = \@f;
    }
    return;
}

sub check_deadlock_pattern ($pt, $brd, $box_y, $box_x) {
    my $start_x = $box_x - $pt->{'x'} + 1;
    my $start_y = $box_y - $pt->{'y'} + 1;

    $start_x = 0 if $start_x < 0;
    $start_y = 0 if $start_y < 0;

    my $shift_y = $pt->{'box_shift_y'};
    my $shift_x = $pt->{'box_shift_x'};
    my $mcx     = $pt->{'maxcx'};
    my $fl      = $pt->{'flat'};

    for my $y ($start_y .. $box_y) {
        last if $y + $pt->{'maxcy'} >= $height;
    X: for my $x ($start_x .. $box_x) {
            last if $x + $mcx >= $width;
            next
                if (vec($brd, ($y + $shift_y) * $width + $x + $shift_x, 8) & BOX) == 0;
            my $base = $y * $width + $x;
            for (my $k = 0; $k < @$fl; $k += 2) {
                next X if vec($brd, $base + $fl->[$k], 8) != $fl->[$k + 1];
            }
            return 1;    # every real cell of the pattern matched
        }
    }
    return 0;
}

sub check_all_patterns ($b_in, $box_p, $pull_mode) {
    return -1 if box_touches_unreachable_square($b_in, $box_p) == 0;

    # the pattern matcher clamps placements against the row edges: the
    # one place the 2-D view survives, behind this single div/mod
    my $box_y = int($box_p / $width);
    my $box_x = $box_p % $width;

    # all pull patterns are <= 4
    return -1 if $pull_mode and (($b_in &. $SOK_ONLY) =~ tr/\x00//c) > 4;

    my $brd;
    _dz_masks(); $brd = $b_in &. $NOT_DZ;

    if ($pull_mode == 0) {
        for my $i (0 .. $#patterns) {
            return $i if check_deadlock_pattern($patterns[$i], $brd, $box_y, $box_x);
        }
    }
    else {
        # in pull mode, it is ok to be confined in a corral containing the
        # start position
        return -1
            if vec($brd,
                $global_initial_sokoban_y * $width + $global_initial_sokoban_x, 8)
            & SOKOBAN;

        for my $i (0 .. $#pull_patterns) {
            return $i
                if check_deadlock_pattern($pull_patterns[$i], $brd, $box_y, $box_x);
        }
    }
    return -1;
}

sub is_inefficient_position ($brd, $box_index, $pull_mode, $search_mode, $h) {
    # positions like
    #  #
    # $
    # ##

    # allow inefficient moves once we reach the perimeter
    return 0 if $h->{'perimeter_found'};
    return 0 if $h->{'enable_inefficient_moves'};

    # allow all pulls in k_dist search, k_dist boards must be accurate
    return 0 if $search_mode == K_DIST_SEARCH;

    my $box_p = $index_to_p[$box_index];
    my $p = $box_p;

    # do not reject positions expected in the plan
    if ($pull_mode == 0) {
        return 0 if vec($h->{'used_in_plan'}, $p, 8);
        return 0
            if $search_mode == HF_SEARCH and vec($h->{'imagined_hf_board'}, $p, 8);
    }
    else {
        return 0
            if $search_mode == REV_SEARCH and vec($h->{'imagined_hf_board'}, $p, 8);
    }

    # never prune moves that push a box to a target or to a base
    if ($pull_mode == 0) {
        return 0 if vec($brd, $p, 8) & TARGET;
    }
    else {
        return 0 if vec($initial_board, $p, 8) & BOX;
    }

    return 1 if $pull_mode == 0 and vec($forbidden_push_tunnel, $p, 8);
    return 1 if $pull_mode and vec($forbidden_pull_tunnel, $p, 8);

    my @val = map {vec($brd, $p + $delta_p_8[$_], 8)} 0 .. 7;

    if ($pull_mode) {
        # check position:
        # #
        #  #
        # $
        # ##
        for (my $j = 0; $j < 8; $j += 2) {
            if (    ($val[$j & 7] & OCCUPIED) == 0
                and $val[($j + 1) & 7] == WALL
                and $val[($j + 3) & 7] == WALL
                and $val[($j + 4) & 7] == WALL)
            {
                return 1 if vec($brd, $p + 2 * $delta_p_8[$j], 8) == WALL;
            }
        }

        # and symmetrical
        for (my $j = 0; $j < 8; $j += 2) {
            if (    ($val[$j & 7] & OCCUPIED) == 0
                and $val[($j + 4) & 7] == WALL
                and $val[($j + 5) & 7] == WALL
                and $val[($j + 7) & 7] == WALL)
            {
                return 1 if vec($brd, $p + 2 * $delta_p_8[$j], 8) == WALL;
            }
        }

        return 0;
    }

    for (my $j = 0; $j < 8; $j += 2) {
        # check positions like
        #  -$#
        #  # #
        # last move must have been up/down, both are silly
        if (    $val[($j + 2) & 7] == WALL
            and $val[($j + 3) & 7] == WALL
            and $val[($j + 5) & 7] == WALL
            and $val[($j + 6) & 7] != WALL
            and ($val[($j + 6) & 7] & SOKOBAN) == 0)
        {
            return 1;
        }

        if (    $val[($j + 3) & 7] == WALL
            and $val[($j + 5) & 7] == WALL
            and $val[($j + 6) & 7] == WALL
            and $val[($j + 2) & 7] != WALL
            and ($val[($j + 2) & 7] & SOKOBAN) == 0)
        {
            return 1;
        }

        # check positions like
        #   @
        #  -$#
        #  # #
        # could just as well park it
        if (    $val[($j + 2) & 7] == WALL
            and $val[($j + 3) & 7] == WALL
            and $val[($j + 5) & 7] == WALL
            and $val[($j + 6) & 7] != WALL
            and $val[$j & 7] & SOKOBAN)
        {
            return 1;
        }

        if (    $val[($j + 3) & 7] == WALL
            and $val[($j + 5) & 7] == WALL
            and $val[($j + 6) & 7] == WALL
            and $val[($j + 2) & 7] != WALL
            and $val[$j & 7] & SOKOBAN)
        {
            return 1;
        }

        # check
        # ???
        # -$$
        # #?#
        if (    $val[($j + 3) & 7] == WALL
            and $val[($j + 5) & 7] == WALL
            and $val[($j + 2) & 7] & BOX
            and ($val[($j + 6) & 7] & SOKOBAN) == 0)
        {
            return 1;
        }

        if (    $val[($j + 3) & 7] == WALL
            and $val[($j + 5) & 7] == WALL
            and $val[($j + 6) & 7] & BOX
            and ($val[($j + 2) & 7] & SOKOBAN) == 0)
        {
            return 1;
        }
    }

    return 0;
}

sub has_pull_continuation ($brd, $search_mode) {
    # check if all boxes are on initial squares
    my $all_boxes_solved = all_boxes_in_place($brd, 1);

    # it is ok to be stuck on initial position.
    if (vec($brd, $global_initial_sokoban_y * $width + $global_initial_sokoban_x, 8)
        & SOKOBAN)
    {
        return 1 if $all_boxes_solved;
    }

    if ($search_mode == K_DIST_SEARCH) {
        return 1 if (($brd &. $SOK_ONLY) =~ tr/\x00//c) > 1;
        # the cloud size could be 1 because a nearby hole (probably garage)
        # was wallified
        return 1
            if sokoban_touches_a_filled_hole($brd);
        return 0;
    }

    for my $p (0 .. $ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;

        for my $k (0 .. 3) {
            my $sp = $p + $delta_p[$k];
            next if (vec($brd, $sp, 8) & SOKOBAN) == 0;

            return 1 if (vec($brd, $sp + $delta_p[$k], 8) & OCCUPIED) == 0;
        }
    }
    return 0;
}


sub check_deadlock_in_moves ($b_in, $moves, $pull_mode, $search_mode, $h) {
    # returns the 'valid' list (C fills an int array instead)
    my @valid;
    my $brd = $b_in;

    # the caller (find_possible_moves) removed all deadlock zone markings,
    # but apply_move, used here, removes boxes out of the zone
    $search_mode = NORMAL if $search_mode == DEADLOCK_SEARCH;

    $brd &.= $NOT_BASE if $pull_mode;

    my @elim = (0) x $index_num;

    if ($pull_mode and $search_mode == BASE_SEARCH) {
        # in reverse mode, mark all eliminating places.
        # if a box gets there, do not prune the move
        for my $p (0 .. $ncells - 1) {
            $elim[$y_x_to_index_table[$p]] = 1 if vec($b_in, $p, 8) & BASE;
        }
    }

    for my $i (0 .. $#$moves) {

        $valid[$i] = 1;

        if ($moves->[$i]{'kill'} == 1) {
            next;
        }

        my $dest = $moves->[$i]{'to'};
        my $dest_p = $index_to_p[$dest];

        # do not prune move into the elimination zone
        next if $pull_mode and $elim[$dest];

        if ($impossible_place[$dest]) {
            $valid[$i] = 0;
            next;
        }

        my $c = $brd;
        $c = apply_move($c, $moves->[$i], $search_mode);

        if (is_mpdb_deadlock($c, $pull_mode)) {
            $valid[$i] = 0;
            next;
        }

        if (is_inefficient_position($c, $moves->[$i]{'to'}, $pull_mode, $search_mode, $h)) {
            $valid[$i] = 0;
            next;
        }

        if ($pull_mode) {
            if (has_pull_continuation($c, $search_mode) == 0) {
                $valid[$i] = 0;
                next;
            }

            if ($elim[$moves->[$i]{'to'}]) {
                # base squares can be on inefficient squares
                Carp::confess('should not be here');
            }

            my $res = check_all_patterns($c, $dest_p, 1);    # 1 - pull mode
            if ($res != -1) {
                $valid[$i] = 0;
                next;
            }

            if ($search_mode == BASE_SEARCH) {
                # check that every base has at least one box (b_in still has
                # the bases)
                if (verify_simple_base_matching(
                        $c, $b_in) == 0)
                {
                    $valid[$i] = 0;
                    next;
                }
            }

            next;
        }    # if pull mode

        # so now we are in push mode

        if (is_freeze_deadlock($c, $dest_p)) {
            $valid[$i] = 0;
            next;
        }

        if (is_3x3_deadlock($c, $dest_p)) {
            $valid[$i] = 0;
            next;
        }

        my $res = check_all_patterns($c, $dest_p, 0);    # 0 - push mode
        if ($res != -1) {
            $valid[$i] = 0;
            next;
        }

    }

    return @valid;
}

# ====================================================================
# Games::Sokoban::Fest::Distance  (was lib2/Games/Sokoban/Fest/Distance.pm)
# ====================================================================

# Port of festival/distance.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription except the table representation:
#   C: int distance_from_to[MAX_INNER][MAX_INNER] (2 x 27 MB static BSS).
#   Perl: ONE packed string per table, 32-bit cells, row stride $index_num,
#   sized index_num * index_num per level -- read with vec() straight at
#   the call sites (the packed string replaces C's direct array indexing;
#   this is the agreed packed-string rule for huge matrices).
#   impossible_place stays a plain flat array (index_num entries).
# The C original's disabled diagnostic loops (commented-out printf over
# unreachable cells) are dropped.
#
# Globals ledger:
#   reads:  $height $width $ncells $inner $index_num
#   writes: $distance_from_to $bfs_distance_from_to (packed strings),
#           @impossible_place -- all three filled by set_distances(),
#           read by graph.cpp/score.cpp/... descendants

sub compute_can_get_to_dest ($brd) {    # returns the can_get_to_dest list
    # collect the goal squares once instead of rescanning the board for
    # every source index (the C original's inner loop)
    my @targets = (grep {vec($brd, $index_to_p[$_], 8) & TARGET} 0 .. $index_num - 1);

    return map {
        my $i = $_;
        (grep {vec($distance_from_to, $i * $index_num + $_, 32) < 1000000} @targets) ? 1 : 0;
    } 0 .. $index_num - 1;
}

sub compute_can_from_start ($brd) {    # returns the can_get_from_start list
    my @boxes = (grep {vec($brd, $index_to_p[$_], 8) & BOX} 0 .. $index_num - 1);

    return map {
        my $i = $_;
        (grep {vec($distance_from_to, $_ * $index_num + $i, 32) < 1000000} @boxes) ? 1 : 0;
    } 0 .. $index_num - 1;
}

sub set_impossible_places ($can_get_to_dest, $can_get_from_start) {
    @impossible_place = map {
        ($can_get_from_start->[$_] and $can_get_to_dest->[$_]) ? 0 : 1
    } 0 .. $index_num - 1;
    return;
}

sub set_bfs_distances ($brd) {
    my @d;

    # flat cell position of every inner index, computed once
    my @p_of = map {
        my $p = $index_to_p[$_];
        $p;
    } 0 .. $index_num - 1;

    $bfs_distance_from_to = '';

    for my $i (0 .. $index_num - 1) {
        @d = (1000000) x $ncells; bfs_from_place($brd, \@d, $p_of[$i], 1);
        # 1 = ignore boxes

        for my $j (0 .. $index_num - 1) {
            vec($bfs_distance_from_to, $i * $index_num + $j, 32) =
                $d[$p_of[$j]];
        }
    }
    return;
}

sub set_distances ($brd) {
    my $board_without_boxes;

    my $gd = allocate_graph();

    $board_without_boxes = $brd &. $NOT_BOX;

    build_graph($board_without_boxes, 0, $gd);    # 0 = push_mode

    $distance_from_to = '';

    for my $from_index (0 .. $index_num - 1) {
        set_graph_weights_to_infinity($gd);
        clear_weight_around_cell($from_index, $gd);
        do_graph_iterations(0, $gd);              # 0 = push mode

        for my $to_index (0 .. $index_num - 1) {
            my $dist = get_weight_around_cell($to_index, $gd);
            vec($distance_from_to, $from_index * $index_num + $to_index, 32) = $dist;
        }
    }

    my @can_get_to_dest    = compute_can_get_to_dest($brd);
    my @can_get_from_start = compute_can_from_start($brd);
    set_impossible_places(\@can_get_to_dest, \@can_get_from_start);

    set_bfs_distances($brd);
    return;
}

sub get_distance_from_targets ($brd, $dist) {    # dist = int_board arrayref
    my ($target_area, $board_without_boxes);

    $target_area = $ZERO_BOARD;
    $board_without_boxes = $brd &. $NOT_BOX;

    for my $p (0 .. $ncells - 1) {
        vec($target_area, $p, 8) = 1 if vec($brd, $p, 8) & TARGET;
    }

    # 1 - pull mode
    find_distance_from_a_group($board_without_boxes, $target_area, $dist, 1);
    return;
}

# ====================================================================
# Games::Sokoban::Fest::Corral  (was lib2/Games/Sokoban/Fest/Corral.pm)
# ====================================================================

# Port of festival/corral.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. A corral = a player-unreachable area; a PI-corral
# is one where EVERY boundary box can only be pushed inward and the player
# stands ready at every such push -- then the search may restrict itself
# to pushes on the corral's boxes (detect_corral marks them in
# corral_options). corral_data is a hashref {corral (board),
# corral_d (int_board arrayref), corral_component_used (array),
# corral_sokoban_comp, corral_comps_num, corral_candidates (array)}.
#
# Exports follow corral.h (detect_corral); everything else is internal.
#
# Globals ledger:
#   reads:  $height $width $ncells @delta_y @delta_x @delta_p_8 $inner
#   writes: nothing global ( toggle only)

sub get_direction_from_pusher_dest ($pusher_p, $dest_p) {
    # returns (direction, box_p); the four flat deltas are distinct, so
    # the difference identifies the direction unambiguously
    for my $i (0 .. 3) {
        return ($i, $pusher_p + $delta_p[$i])
            if $pusher_p + $delta_p[$i] * 2 == $dest_p;
    }
    Carp::confess('no direction');
}

sub get_corral_boxes ($orig_b, $cd) {
    # get all the boxes that touch the corral; mark the corral area as sokoban

    my $corral_boxes;
    $corral_boxes = $orig_b &. $NOT_BOX;
    $corral_boxes &.= $NOT_SOKOBAN;

    for my $p (0 .. $ncells - 1) {
next if vec($cd->{'corral'}, $p, 8) == 0;

vec($corral_boxes, $p, 8) |= SOKOBAN;

for my $k (0 .. 7) {
vec($corral_boxes, $p + $delta_p_8[$k], 8) |= BOX
if vec($orig_b, $p + $delta_p_8[$k], 8) & BOX;
}
}

    return $corral_boxes;
}

sub is_possible_push_into_corral ($brd, $pp, $dp, $cd) {

    return 0 if vec($brd, $pp, 8) == WALL;
    return 0 if vec($brd, $dp, 8) & OCCUPIED;

    # only look for pushes into the corral
    return 0 if vec($cd->{'corral'}, $pp, 8);
    return 0 if vec($cd->{'corral'}, $dp, 8) == 0;

    my ($direction, $box_p) = get_direction_from_pusher_dest($pp, $dp);

    return 0 if deadlock_in_direction($brd, $box_p, $direction);
    return 1;
}

sub is_possible_push_aside_corral ($brd, $pp, $dp, $cd) {

    # can't push if occupied
    return 0 if vec($brd, $pp, 8) & OCCUPIED;
    return 0 if vec($brd, $dp, 8) & OCCUPIED;

    return 0 if vec($cd->{'corral'}, $pp, 8);
    return 0 if vec($cd->{'corral'}, $dp, 8);

    my ($direction, $box_p) = get_direction_from_pusher_dest($pp, $dp);

    return 0 if deadlock_in_direction($brd, $box_p, $direction);
    return 1;
}

sub is_corral_active ($b_in, $cd) {
    # still work to do inside corral
    my $corral_boxes;
    $corral_boxes = get_corral_boxes($b_in, $cd);
    # gets the boxes around the corral, AND marks inner corral with sokoban

    for my $p (0 .. $ncells - 1) {
        if (vec($cd->{'corral'}, $p, 8)) {
            Carp::confess('debug corral')
                if vec($corral_boxes, $p, 8) == TARGET;

            # a target that is not occupied
            return 1 if vec($corral_boxes, $p, 8) == (TARGET | SOKOBAN);
        }

        return 1 if vec($corral_boxes, $p, 8) == BOX;    # a box not on a target
    }
    return 0;
}

sub set_corral_options ($b_in, $cd) {
    # mark the boxes that can be pushed

    my $corral_boxes;
    $corral_boxes = get_corral_boxes($b_in, $cd);

    my $corral_options;
    $corral_options = $b_in &. $NOT_BOX;

    for my $p (0 .. $ncells - 1) {
        next if (vec($corral_boxes, $p, 8) & BOX) == 0;

        for my $k (0 .. 3) {
            my $pusher_p = $p + $delta_p[$k];

            if (is_possible_push_into_corral(
                    $corral_boxes, $pusher_p, $p - $delta_p[$k], $cd))
            {
                vec($corral_options, $p, 8) |= BOX
                    if vec($b_in, $pusher_p, 8) & SOKOBAN;
            }
        }
    }

    return $corral_options;
}

sub get_corral_candidates ($brd, $cd) {
    # find areas that are touched by sokoban.
    my @corral_d;
    $cd->{'corral_comps_num'} = mark_connectivities($brd, \@corral_d);
    $cd->{'corral_d'}         = \@corral_d;

    $cd->{'corral_sokoban_comp'} = $corral_d[get_sokoban_position($brd)];

    $cd->{'corral_candidates'} = [(0) x $cd->{'corral_comps_num'}];

    for my $p (0 .. $ncells - 1) {
next if (vec($brd, $p, 8) & BOX) == 0;

for my $k (0 .. 3) {
if ($corral_d[$p + $delta_p[$k]]
== $cd->{'corral_sokoban_comp'})
{
my $other =
$corral_d[$p - $delta_p[$k]];
$cd->{'corral_candidates'}[$other] = 1
if $other != 1000000
and $other != $cd->{'corral_sokoban_comp'};
}
}
}


    return;
}

sub init_corral_with_comp ($comp1, $comp2, $b_in, $cd) {
    $cd->{'corral'} = $ZERO_BOARD;

    $cd->{'corral_component_used'} = [(0) x $cd->{'corral_comps_num'}];

    $cd->{'corral_component_used'}[$comp1] = 1;
    $cd->{'corral_component_used'}[$comp2] = 1;

    for my $p (0 .. $ncells - 1) {
        if (   $cd->{'corral_d'}[$p] == $comp1
            or $cd->{'corral_d'}[$p] == $comp2)
        {
            vec($cd->{'corral'}, $p, 8) = 1;
        }
    }

    return is_corral_active($b_in, $cd);
}

sub update_corral_with_comp ($comp1, $cd) {
    $cd->{'corral_component_used'}[$comp1] = 1;

    for my $p (0 .. $ncells - 1) {
        vec($cd->{'corral'}, $p, 8) = 1 if $cd->{'corral_d'}[$p] == $comp1;
    }
    return;
}

sub box_touches_corral_and_non_corral ($brd, $p, $corral) {

    my ($touches_corral, $touches_non_corral) = (0, 0);

    for my $i (0 .. 3) {
        my $np = $p + $delta_p[$i];

        $touches_corral = 1 if vec($corral, $np, 8);

        if ((vec($brd, $np, 8) & OCCUPIED) == 0) {
            $touches_non_corral = 1 if vec($corral, $np, 8) == 0;
        }
    }

    return $touches_corral & $touches_non_corral;
}

sub should_add_component_to_corral ($corral_boxes, $cd) {
    # returns (found, component)
    for my $p (0 .. $ncells - 1) {
next if (vec($corral_boxes, $p, 8) & BOX) == 0;

next
if box_touches_corral_and_non_corral(
$corral_boxes, $p, $cd->{'corral'}) == 0;

for my $k (0 .. 3) {
my $pusher_p = $p + $delta_p[$k];
my $dest_p   = $p - $delta_p[$k];

my $can_push_inside = is_possible_push_into_corral(
$corral_boxes, $pusher_p, $dest_p, $cd);
$can_push_inside = 0
if vec($corral_boxes, $pusher_p, 8) & OCCUPIED;

my $can_push_aside = is_possible_push_aside_corral(
$corral_boxes, $pusher_p, $dest_p, $cd);

next if $can_push_inside == 0 and $can_push_aside == 0;

# by previous check, we know that pusher is outside the corral

if ($can_push_inside) {
my $d = $cd->{'corral_d'}[$pusher_p];

# could be a box in front of the corral
if ($d != 1000000) {
return (1, $d)
if $d != $cd->{'corral_sokoban_comp'}
and $cd->{'corral_component_used'}[$d] == 0;
}
}

if ($can_push_aside) {
my $d = $cd->{'corral_d'}[$dest_p];

Carp::confess('this is strange') if $d == 1000000;
return (1, $d)
if $d != $cd->{'corral_sokoban_comp'}
and $cd->{'corral_component_used'}[$d] == 0;
}
}    # k
}
    return (0, undef);
}

sub can_push_box_out_of_corral ($brd, $corral) {
    for my $p (0 .. $ncells - 1) {
next if (vec($brd, $p, 8) & BOX) == 0;
next if vec($inner, $p, 8) == 0;

for my $k (0 .. 3) {
my $pusher_p = $p + $delta_p[$k];
my $dest_p   = $p - $delta_p[$k];

# can't push if occupied
next if vec($brd, $pusher_p, 8) & OCCUPIED;
next if vec($brd, $dest_p, 8) & OCCUPIED;

next if deadlock_in_direction($brd, $p, ($k + 2) & 3);

if (vec($corral, $pusher_p, 8) == 0) {
if (vec($corral, $dest_p, 8) == 0) {
return 1;
}
}
}
}
    return 0;
}

sub check_pi_corral ($corral_boxes, $b_in, $cd) {
    # verify that all the boxes on the corral boundary can actually be
    # pushed inside
    for my $p (0 .. $ncells - 1) {
next if (vec($corral_boxes, $p, 8) & BOX) == 0;

for my $k (0 .. 3) {
my $pusher_p = $p + $delta_p[$k];
my $dest_p   = $p - $delta_p[$k];

next
if is_possible_push_into_corral(
$corral_boxes, $pusher_p, $dest_p, $cd) == 0;

# the box is not on the corral boundary
next if vec($corral_boxes, $pusher_p, 8) & OCCUPIED;

Carp::confess('not right1')
if vec($cd->{'corral'}, $dest_p, 8) == 0;
Carp::confess('not right2')
if vec($cd->{'corral'}, $pusher_p, 8) == 1;

return 0 if (vec($b_in, $pusher_p, 8) & SOKOBAN) == 0;
}
}
    return 1;
}

sub expand_corral ($b_in, $cd) {
    # given the current corral, try to expand it by adding components,
    # until it can be proven to be a pi-corral. Or report that it's not a
    # pi-corral once the expansions stop.
    my $corral_boxes;
    my $res;

    do {
        $corral_boxes = get_corral_boxes($b_in, $cd);


        (my $found, my $d) = should_add_component_to_corral($corral_boxes, $cd);
        $res = $found;
        if ($res) {
            update_corral_with_comp($d, $cd);
        }
    } while ($res);

    return 0 if can_push_box_out_of_corral($corral_boxes, $cd->{'corral'});

    return 0 if check_pi_corral($corral_boxes, $b_in, $cd) == 0;

    return 1;
}

sub init_touches_two_comps ($brd, $cd) {    # returns AoA hashref-free matrix
    my @touches;

    # Pre-zeroed to the number of components there actually are. The C original
    # sized this by MAX_CORRALS_NUM because the array had to be declared; here
    # it is an AoA that grows, and its only reader (detect_corral) never looks
    # past corral_comps_num, so the fixed 70x70 was 4900 assignments to serve at
    # most a few dozen.
    my $ncomp = $cd->{'corral_comps_num'};
    for my $i (0 .. $ncomp - 1) {
        for my $j (0 .. $ncomp - 1) {
            $touches[$i][$j] = 0;
        }
    }

    for my $p (0 .. $ncells - 1) {
next if (vec($brd, $p, 8) & BOX) == 0;

for my $k (0 .. 3) {
for my $l (0 .. 3) {
my $d1 = $cd->{'corral_d'}
[$p + $delta_p[$k]];
my $d2 = $cd->{'corral_d'}
[$p + $delta_p[$l]];

$touches[$d1][$d2] = 1
if $d1 != 1000000 and $d2 != 1000000;
}
}
}
    return \@touches;
}

sub detect_corral ($brd) {

    my $cd = {
        'corral'                => '',
        'corral_d'              => [],
        'corral_component_used' => [],
        'corral_sokoban_comp'   => -1,
        'corral_comps_num'      => 0,
        'corral_candidates'     => [],
    };


    get_corral_candidates($brd, $cd);

    for my $i (0 .. $cd->{'corral_comps_num'} - 1) {
        next if $cd->{'corral_candidates'}[$i] == 0;

        next if init_corral_with_comp($i, $i, $brd, $cd) == 0;

        if (expand_corral($brd, $cd) == 1) {
            return (1, set_corral_options($brd, $cd));
        }
    }

    my $touches_two_comps = init_touches_two_comps($brd, $cd);

    # look for two-rooms corral
    for my $i (0 .. $cd->{'corral_comps_num'} - 1) {
        next if $i == $cd->{'corral_sokoban_comp'};

        for my $j ($i + 1 .. $cd->{'corral_comps_num'} - 1) {
            next if $j == $cd->{'corral_sokoban_comp'};

            if ($cd->{'corral_candidates'}[$j] == 0) {
                next if $cd->{'corral_candidates'}[$i] == 0;
            }

            next if $touches_two_comps->[$i][$j] == 0;

            next if init_corral_with_comp($i, $j, $brd, $cd) == 0;

            if (expand_corral($brd, $cd) == 1) {
                return (1, set_corral_options($brd, $cd));
            }
        }
    }

    return (0, undef);
}

# ====================================================================
# Games::Sokoban::Fest::Hotspot  (was lib2/Games/Sokoban/Fest/Hotspot.pm)
# ====================================================================

# Port of festival/hotspot.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 translation: P1 (the index->position table replaces
# index_to_y_x + y*width+x wherever only the flat position was wanted --
# @index_to_p is exported from Board since its v0.04 for exactly this),
# P4 (count_targets_on_mask is one flat scan; it stays a loop rather than
# a tr/// count because its predicate reads TWO boards), and P5 in
# find_hotspots, which now reuses Board::get_indices_of_boxes instead of
# re-scanning the board for the same list.
#
# Transcribed as-is except the two huge matrices:
#   C: int blocks_place[MAX_INNER][MAX_INNER], completely_blocks[...]
#      (2 x 27 MB static BSS).
#   Perl: packed strings sized per level -- blocks_place 32-bit cells,
#   completely_blocks 8-bit cells (0/1), row stride $index_num; read with
#   vec() straight at the call sites (agreed packed-string rule).
# A hotspot is a box position that blocks another box's way to ANY target;
# blocks_place counts how many targets the blocker takes away.
# TRAP: init_hotspots() has a time fuse (hotspots_take_too_much_time,
# aborts after time_limit/4 seconds since $start_time) -- callers that
# want a deterministic run must set $start_time = time() first (the gate
# and fest_g1 do).
#
# Exports follow hotspot.h (+ the two accessors); count_targets_on_mask,
# clear_hotspots_data, hotspots_take_too_much_time and the
# targets_reachable_from array stay package-internal.
#
# Globals ledger:
#   reads:  $height $width $ncells $inner $index_num $start_time
# $time_limit Distance::@impossible_place
#   writes: $blocks_place $completely_blocks (packed strings),
#           @targets_reachable_from (init_hotspots)

sub hotspots_score ($brd) {
    my ($h, $weights);
    ($h, $weights) = find_hotspots($brd);
    return unpack('%32C*', $h);
}

sub count_targets_on_mask ($brd, $mask) {
    # P4: one flat scan. Stays a loop rather than a tr/// count (P2): the
    # predicate reads TWO boards, which the byte-set rule excludes.
    my $sum = 0;

    for my $p (0 .. $ncells - 1) {
        next unless vec($mask, $p, 8);
        $sum++ if vec($brd, $p, 8) & TARGET;
    }
    return $sum;
}

sub hotspots_take_too_much_time () {
    my $t = time() - $start_time;

    return 0 if $t < $time_limit / 4;

    $Hotspots_incomplete = 1;    # this analysis must not be claimed for reuse
    $blocks_place = "\0" x ($index_num * $index_num * 4); $completely_blocks = "\0" x ($index_num * $index_num);
    return 1;
}

sub init_hotspots ($brd) {
    my ($empty, $targets, $board_with_blocker);

    $Hotspots_incomplete = 0;
    my $gd = allocate_graph();

    $blocks_place = "\0" x ($index_num * $index_num * 4); $completely_blocks = "\0" x ($index_num * $index_num);

    $empty = $brd &. $NOT_BOX;

    build_graph($empty, 0, $gd);
    for my $p (0 .. $index_num - 1) {
        my $p2 = $index_to_p[$p];

        $targets = find_targets_of_place_without_init_graph($p2, $gd);

        $targets_reachable_from[$p] = count_targets_on_mask($brd, $targets);
    }

    for my $blocker (0 .. $index_num - 1) {
        # abort hotspots calculation if it is too heavy
        return if hotspots_take_too_much_time();

        next if $impossible_place[$blocker];

        my $blocker_p = $index_to_p[$blocker];    # P1

        # if a box reached a target, don't consider it as a blocker
        next if vec($brd, $blocker_p, 8) & TARGET;

        $board_with_blocker = $empty;
        vec($board_with_blocker, $blocker_p, 8) = WALL;

        build_graph($board_with_blocker, 0, $gd);

        for my $p (0 .. $index_num - 1) {
            next if $impossible_place[$p];

            next if $p == $blocker;

            # if the blocked box is on target, don't consider it to be blocked
            next if vec($brd, $index_to_p[$p], 8) & TARGET;    # P1

            my $p2 = $index_to_p[$p];
            $targets = find_targets_of_place_without_init_graph($p2, $gd);

            # how many targets without the blocker minus with the blocker
            my $updated_targets = count_targets_on_mask($brd, $targets);
            vec($blocks_place, $p * $index_num + $blocker, 32) =
                $targets_reachable_from[$p] - $updated_targets;

            vec($completely_blocks, $p * $index_num + $blocker, 8) = 1
                if $updated_targets == 0;
        }
    }
    return;
}

sub double_blocking ($index1, $index2) {
    return 0 if vec($completely_blocks, $index1 * $index_num + $index2, 8) == 0;
    return 0 if vec($completely_blocks, $index2 * $index_num + $index1, 8) == 0;
    return 1;
}

sub find_hotspots ($brd) {
    # given a board, find the active hotspots

    my ($h, $hotspot_weights);

    $h = $ZERO_BOARD;
    $hotspot_weights = $ZERO_BOARD;

    # P5: Board already collects exactly this list (inner indexes carrying a
    # box, in ascending index order == the C original's row-major order, and
    # an inner index is by definition an inner cell) -- reuse it instead of
    # re-scanning the board here.
    my @boxes_indices = (grep {vec($brd, $index_to_p[$_], 8) & BOX} 0 .. $index_num - 1);

    for my $i (0 .. $#boxes_indices) {
        my $bp = $index_to_p[$boxes_indices[$i]];    # P1

        for my $j (0 .. $#boxes_indices) {
            next if $j == $i;

            # i is blocking j
            if (vec($blocks_place, $boxes_indices[$j] * $index_num + $boxes_indices[$i], 32)) {
                vec($h, $bp, 8) = 1;
                vec($hotspot_weights, $bp, 8)++;
            }
        }
    }

    return ($h, $hotspot_weights);
}

# ====================================================================
# Games::Sokoban::Fest::Oop  (was lib2/Games/Sokoban/Fest/Oop.pm)
# ====================================================================

# Port of festival/oop.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 translation: P1 at four sites (plan target and move endpoints
# turned into cell positions by table lookup). The remaining y/x scan is
# kept: it needs the cell -> index direction for the impossible-place
# test, and that table is not exported flat.
#
# Out-of-plan zones: for every plan step, the
# cells a box must NOT occupy once the step's permanent boxes are parked
# (walls of parked boxes block the push graph; whatever cannot reach any
# remaining plan target is out of plan). get_out_of_plan_score counts
# boxes inside the current step's zone; new_oop_advisor picks the move
# that best walks an offending box out of the zone (along the zone's
# distance field). The oop data lives in the helper
# ({'oop'}{'oop_zone_for_step'} boards / {'oop_zone_distance_for_step'}
# int_boards). The commented-out C variants are not transcribed.
#
# Globals ledger:
#   reads:  $height $width $inner Board::$initial_board
#           Distance::@impossible_place distance_from_to
#   writes: nothing global (all state in the helper)


sub count_boxes_in_oop_zone ($brd, $oop) {
    my $sum = 0;

    for my $p (0 .. $ncells - 1) {
        if (vec($oop, $p, 8)) {
            $sum++ if vec($brd, $p, 8) & BOX;
        }
    }

    return $sum;
}

sub get_out_of_plan_score ($brd, $parked_num, $h) {
    Carp::confess('missing oop3') unless defined $h->{'oop'};
    my $oop_zone_for_step = $h->{'oop'}{'oop_zone_for_step'};

    my $res = count_boxes_in_oop_zone($brd, $oop_zone_for_step->[$parked_num]);
    return $res;
}


# ====================================================================
# Games::Sokoban::Fest::Moves  (was lib2/Games/Sokoban/Fest/Moves.pm)
# ====================================================================

# Port of festival/moves.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. The move generator: for every pushable box run
# the box-move graph BFS (find_box_moves), sieve the results through the
# deadlock dispatcher, apply mode-specific reducers, honor a detected
# PI-corral. A 'move' is the hashref {from, to, sokoban_position, kill,
# base, pull, attr => {weight, advisor, reversible}} (see Graph.pm).
#
# Signature conventions:
#   find_possible_moves($brd, $pull_mode, \$has_corral, $search_mode, $h)
#     returns the move LIST (C fills a moves array + out-flag);
#   find_box_moves(...) likewise returns a list.
# Runtime-qualified calls (their modules come with M5+/M7):
#   CorralDeadlock::check_for_deadlock_zone_moves (DEADLOCK_SEARCH)
#   KDistDeadlock::check_for_k_dist_moves         (K_DIST_SEARCH)
#   Wobblers::reduce_moves_in_wobblers_search     (WOBBLERS_SEARCH)
#   RoomsDeadlock::reduce_moves_in_rooms_deadlock_search
#   XyDeadlock::reduce_moves_in_xy_search         (XY_SEARCH)
#   Heuristics::mark_sink_squares_moves + compute_possible_from_bases
#                                                 (BASE_SEARCH)
# All of those return adjusted move lists in the Perl port.
#
# Globals ledger:
#   reads:  $height $width $ncells @delta_y @delta_x @delta_p $inner
# $index_num Distance::@impossible_place
#   writes: $global_fail_reason ("Too many moves")

sub box_can_be_moved ($brd, $index, $pull_mode) {
    my $p = $index_to_p[$index];

    if ($pull_mode == 0) {
        for my $i (0 .. 3) {
            next if vec($brd, $p + $delta_p[$i], 8) & OCCUPIED;
            next if (vec($brd, $p - $delta_p[$i], 8) & SOKOBAN) == 0;
            next if deadlock_in_direction($brd, $p, $i);
            return 1;
        }
        return 0;
    }

    # pull mode
    for my $i (0 .. 3) {
        next if (vec($brd, $p + $delta_p[$i], 8) & SOKOBAN) == 0;
        next if vec($brd, $p + 2 * $delta_p[$i], 8) & OCCUPIED;
        return 1;
    }
    return 0;
}

sub find_box_moves ($brd, $index, $pull_mode, $search_mode, $possible_board, $gd) {
    # returns the move list
    Carp::confess("box can't be moved")
        if box_can_be_moved($brd, $index, $pull_mode) == 0;

    my $p = $index_to_p[$index];

    # find situation-specific deadlocks, in addition to the level deadlocks
    set_current_impossible($brd, $p, $pull_mode, $search_mode,
        $possible_board, $gd);

    mark_box_moves_in_graph($brd, $index, $pull_mode, $gd);

    find_reversible_moves($brd, $index, $pull_mode, $gd)
        if $search_mode == NORMAL or $search_mode == WOBBLERS_SEARCH;

    my @moves = get_box_moves_from_graph($index, $gd);

    $_->{'pull'} = $pull_mode for @moves;

    return @moves;
}

sub get_possible_places ($brd, $pull_mode, $search_mode) {
    # set situation-specific possible places for boxes

    my $possible = $inner;

    if ($pull_mode == 0) {
        # get_srcs_of_all_targets REPLACES the buffer (zero_board first in C)
        $possible = get_srcs_of_all_targets($brd);
        return $possible;
    }

    if ($search_mode == BASE_SEARCH) {
        $possible = compute_possible_from_bases($brd);
    }

    return $possible;
}

sub remove_deadlocked_moves ($brd, $moves, $pull_mode, $search_mode, $h) {
    # returns the surviving move list (C: valid[] + keep_valid_moves)
    my @valid =
        check_deadlock_in_moves($brd, $moves, $pull_mode, $search_mode, $h);

    return map {$moves->[$_]} grep {$valid[$_]} 0 .. $#$moves;
}

sub detect_kill_moves ($b_in, $brd, $moves, $pull_mode, $search_mode, $h) {
    # returns the adjusted move list
    my @m = @$moves;

    @m = check_for_deadlock_zone_moves(
        $b_in, \@m)
        if $search_mode == DEADLOCK_SEARCH;

    @m = check_for_k_dist_moves($brd, \@m, $h)
        if $search_mode == K_DIST_SEARCH;

    @m = reduce_moves_in_wobblers_search(\@m)
        if $search_mode == WOBBLERS_SEARCH;

    @m = reduce_moves_in_rooms_deadlock_search(
        \@m, $h)
        if $search_mode == ROOMS_DEADLOCK_SEARCH;

    @m = reduce_moves_in_xy_search($brd, \@m)
        if $search_mode == XY_SEARCH;

    return @m;
}

sub find_possible_moves ($b_input, $pull_mode, $has_corral_ref, $search_mode, $h) {

    my @moves;
    my ($brd, $c, $corral_options, $possible_board);
    my $use_corral = 1;

    my $gd = allocate_graph();    # allocate once here for all box moves

    $$has_corral_ref = 0;

    if ($pull_mode == 0) {
        _dz_masks(); $c = $b_input &. $NOT_DZ;
        $brd = turn_fixed_boxes_into_walls($c);
    }
    else {
        _dz_masks(); $brd = $b_input &. $NOT_DZ;
    }

    $possible_board = get_possible_places($brd, $pull_mode, $search_mode);

    # areas behind the deadlock zone might have packed boxes; removed in the
    # deadlock search, making the targets seem empty - so there seems to be
    # work in the corral even if there isn't
    $use_corral = 0 if $search_mode == DEADLOCK_SEARCH;

    $use_corral = 0 if $search_mode == ROOMS_DEADLOCK_SEARCH;    # same issue
    $use_corral = 0 if $search_mode == MINI_SEARCH;
    $use_corral = 0 if $search_mode == XY_SEARCH;
    $use_corral = 0 if $search_mode == K_DIST_SEARCH;

    if ($search_mode == IGNORE_CORRAL) {
        $use_corral  = 0;
        $search_mode = NORMAL;
    }

    $use_corral = 0 if $h->{'perimeter_found'};
    $use_corral = 0 if $h->{'enable_inefficient_moves'};

    if ($use_corral and $pull_mode == 0) {
        ($$has_corral_ref, $corral_options) = detect_corral($brd);
    }

    for my $i (0 .. $index_num - 1) {
        my $p = $index_to_p[$i];

        if ($$has_corral_ref) {
            next if (vec($corral_options, $p, 8) & BOX) == 0;
        }

        if ($search_mode == REV_SEARCH and $pull_mode and $h->{'perimeter_found'} == 0) {
            # box was wallified by the forward search
            next if vec($h->{'wallified'}, $p, 8);
        }

        next if (vec($brd, $p, 8) & BOX) == 0;
        next if box_can_be_moved($brd, $i, $pull_mode) == 0;

        my @box_moves =
            find_box_moves($brd, $i, $pull_mode, $search_mode, $possible_board, $gd);

        @box_moves =
            remove_deadlocked_moves($brd, \@box_moves, $pull_mode, $search_mode, $h);

        @box_moves =
            detect_kill_moves($b_input, $brd, \@box_moves, $pull_mode, $search_mode, $h);

        if (@box_moves == 1 and $box_moves[0]{'kill'}) {
            @moves = ($box_moves[0]);
            last;
        }

        push @moves, @box_moves;

    }

    if ($search_mode == BASE_SEARCH) {
        @moves =
            mark_sink_squares_moves($brd, \@moves);
    }

    return @moves;
}

sub apply_move ($brd, $m, $search_type) {

    Carp::confess('search type not initialized') if $search_type == -1;

    if ($m->{'kill'}) {
        my $p2 = $index_to_p[$m->{'from'}];
        vec($brd, $p2, 8) &= 0xFF ^ BOX;
        $brd = expand_sokoban_cloud($brd);

        $brd = update_deadlock_zone($brd, $m->{'pull'})
            if $search_type == DEADLOCK_SEARCH;
        return $brd;
    }

    $brd &.= $NOT_SOKOBAN;

    my $p = $index_to_p[$m->{'from'}];    # box to push: initial position

    Carp::confess('missing box2') if (vec($brd, $p, 8) & BOX) == 0;
    vec($brd, $p, 8) &= 0xFF ^ BOX;

    $p = $index_to_p[$m->{'to'}];         # box to push: final position

    Carp::confess('occupied place') if vec($brd, $p, 8) & OCCUPIED;

    vec($brd, $p, 8) |= BOX;

    if ($m->{'base'} == 1) {
        vec($brd, $p, 8) &= 0xFF ^ BOX;
        Carp::confess('no base in apply') if (vec($brd, $p, 8) & BASE) == 0;
        vec($brd, $p, 8) &= 0xFF ^ BASE;
    }

    vec($brd, $p + $delta_p[$m->{'sokoban_position'}], 8) |= SOKOBAN;

    $brd = expand_sokoban_cloud($brd);

    $brd = update_deadlock_zone($brd, $m->{'pull'}) if $search_type == DEADLOCK_SEARCH;
    return $brd;
}


# ====================================================================
# Games::Sokoban::Fest::Mpdb2  (was lib2/Games/Sokoban/Fest/Mpdb2.pm)
# ====================================================================

# Port of festival/mpdb2.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. The "mini pattern DB": pairs of cells such that
# two boxes standing on them together are a proven deadlock. build_mpdb2()
# enumerates double-blocking pairs (hotspots' completely_blocks both ways)
# and confirms each by the mini search; is_mpdb_deadlock() is the cheap
# runtime test. The pull side confirms candidates with the xy-projection
# search instead.
#
# Runtime-qualified calls (modules ported later):
#   MiniSearch::can_put_all_on_targets  XyDeadlock::is_xy_deadlock
#
# Globals ledger:
#   reads:  $height $width $ncells @delta_p $index_num
#           $global_boxes_in_level Board::$initial_board
#           Distance::@impossible_place Distance::bfs_distance_from_to
#   writes: @mpdb_list $mpdb_board @pull_mpdb_list $pull_mpdb_board

sub add_to_mpdb ($index1, $index2) {
    push @mpdb_list, [$index1, $index2];

    my $p = $index_to_p[$index1];
    vec($mpdb_board, $p, 8) = 1;
    $p = $index_to_p[$index2];
    vec($mpdb_board, $p, 8) = 1;

    return;
}

sub is_mpdb_deadlock ($brd, $pull_mode) {
    return is_pull_mpdb_deadlock($brd) if $pull_mode;

    for my $pair (@mpdb_list) {
        my $p = $index_to_p[$pair->[0]];
        next if (vec($brd, $p, 8) & BOX) == 0;

        $p = $index_to_p[$pair->[1]];
        next if (vec($brd, $p, 8) & BOX) == 0;

        return 1;
    }
    return 0;
}

sub two_near_wall ($b_in) {
    for my $i (0 .. $height - 2) {
        for my $j (0 .. $width - 2) {
            my ($n_box, $n_wall) = (0, 0);
            for my $yy (0 .. 1) {
                for my $xx (0 .. 1) {
                    my $c = vec($b_in, ($i + $yy) * $width + $j + $xx, 8);
                    $n_wall++ if $c == WALL;
                    $n_box++  if $c & BOX;
                }
            }
            return 1 if $n_box == 2 and $n_wall == 2;
        }
    }
    return 0;
}

sub check_known_deadlock ($brd) {
    for my $p (0 .. $ncells - 1) {
next if (vec($brd, $p, 8) & BOX) == 0;

return 1 if check_all_patterns($brd, $p, 0) != -1;    # 0 - push mode
}
    return 0;
}

sub build_mpdb2 () {
    my ($empty_board, $brd);

    @mpdb_list = ();
    $mpdb_board = $ZERO_BOARD;

    return if $global_boxes_in_level == 1;

    $empty_board = $initial_board &. $NOT_BOX;
    $empty_board &.= $NOT_SOKOBAN;

    for my $i (0 .. $index_num - 1) {
        next if $impossible_place[$i];
        my $p = $index_to_p[$i];
        next if vec($forbidden_push_tunnel, $p, 8);

        for my $j ($i + 1 .. $index_num - 1) {
            next if $impossible_place[$j];
            $p = $index_to_p[$j];
            next if vec($forbidden_push_tunnel, $p, 8);

            next if double_blocking($i, $j) == 0;

            $brd = $empty_board;
            $p = $index_to_p[$i];
            vec($brd, $p, 8) |= BOX;
            $p = $index_to_p[$j];
            vec($brd, $p, 8) |= BOX;

            next if all_boxes_in_place($brd, 0);

            next if get_connectivity($brd) > 1;    # can't know side of sokoban

            next if two_near_wall($brd);

            next if check_known_deadlock($brd);

            $brd = put_sokoban_everywhere($brd);

            # main search; a "-1" result means search aborted
            next if can_put_all_on_targets($brd, 100);


            add_to_mpdb($i, $j);
        }
    }
    return;
}

sub add_to_pull_mpdb ($index1, $index2) {
    push @pull_mpdb_list, [$index1, $index2];

    my $p = $index_to_p[$index1];
    vec($pull_mpdb_board, $p, 8) = 1;
    $p = $index_to_p[$index2];
    vec($pull_mpdb_board, $p, 8) = 1;

    return;
}

sub very_pullable ($brd, $y, $x) {
    my $p   = $y * $width + $x;
    my $sum = 0;
    for my $i (0 .. 3) {
        if ((vec($brd, $p + $delta_p[$i], 8) & OCCUPIED) == 0) {
            $sum++ if (vec($brd, $p + 2 * $delta_p[$i], 8) & OCCUPIED) == 0;
        }
    }
    return $sum == 4 ? 1 : 0;
}

sub build_pull_mpdb2 () {
    my ($empty_board, $brd);

    @pull_mpdb_list = ();
    $pull_mpdb_board = $ZERO_BOARD;

    return if $global_boxes_in_level == 1;

    $empty_board = $initial_board &. $NOT_BOX;
    $empty_board &.= $NOT_SOKOBAN;

    for my $i (0 .. $index_num - 1) {
        next if $impossible_place[$i];
        my ($y1, $x1) = index_to_y_x($i);
        next if vec($forbidden_pull_tunnel, $y1 * $width + $x1, 8);

        for my $j ($i + 1 .. $index_num - 1) {
            next if $impossible_place[$j];
            my ($y2, $x2) = index_to_y_x($j);
            next if vec($forbidden_pull_tunnel, $y2 * $width + $x2, 8);

            next if $y1 != $y2 and $x1 != $x2;

            my $d = abs($y1 - $y2) + abs($x1 - $x2);
            next if $d == 1;
            next if $d >= 10;
            next if vec($bfs_distance_from_to, $i * $index_num + $j, 32) != $d;

            $brd = $empty_board;
            vec($brd, $y1 * $width + $x1, 8) |= BOX;
            vec($brd, $y2 * $width + $x2, 8) |= BOX;

            next if very_pullable($brd, $y1, $x1) and very_pullable($brd, $y2, $x2);

            next if all_boxes_in_place($brd, 1);

            next if get_connectivity($brd) > 1;    # can't know side of sokoban

            $brd = put_sokoban_everywhere($brd);

            next if is_xy_deadlock($brd, 1) == 0;


            add_to_pull_mpdb($i, $j);
        }
    }
    return;
}

sub is_pull_mpdb_deadlock ($brd) {
    for my $pair (@pull_mpdb_list) {
        my $p = $index_to_p[$pair->[0]];
        next if (vec($brd, $p, 8) & BOX) == 0;

        $p = $index_to_p[$pair->[1]];
        next if (vec($brd, $p, 8) & BOX) == 0;

        return 1;
    }
    return 0;
}

# ====================================================================
# Games::Sokoban::Fest::Score  (was lib2/Games/Sokoban/Fest/Score.pm)
# ====================================================================

# Port of festival/score.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. A score_element is a hashref with the C field
# names (connectivity, rooms_score, packed_boxes, boxes_on_targets,
# boxes_in_level, dist_to_targets, dist_to_imagined, hotspots,
# out_of_plan, overlap, imagine, value, biconnect); score_board() fills
# the caller's hashref (C shape), is_better_score() is the NORMAL/BASE
# lexicographic comparator with mode dispatch.
#
# Runtime-qualified calls (their modules come with M5+/M7/M8):
#   Naive/Snail/HfSearch/Wobblers/Girl/KDistDeadlock comparators+fillers,
#   ParkOrder::score_parked_boxes, Oop::get_out_of_plan_score,
#   Imagine::imagine_score, HfSearch::set_score_in_rev_mode
#
# Globals ledger:
#   reads:  $height $width $ncells $index_num $global_boxes_in_level
#           Distance::distance_from_to
#   writes: nothing global (scored_distance lives in the helper)


sub get_scored_distance ($brd, $h) {
    my $sum = 0;
    for my $p (0 .. $ncells - 1) {
        $sum += $h->{'scored_distance'}[$p] if vec($brd, $p, 8) & BOX;
    }
    return $sum;
}


sub score_board ($brd, $s, $pull_mode, $search_mode, $h) {    # fills $s hashref
    $s->{'boxes_on_targets'} = 0;
    $s->{'dist_to_targets'}  = 0;
    $s->{'dist_to_imagined'} = 0;
    $s->{'boxes_in_level'}   = $global_boxes_in_level;
    $s->{'connectivity'}     = 0;
    $s->{'rooms_score'}      = 0;
    $s->{'packed_boxes'}     = 0;
    $s->{'hotspots'}         = 0;
    $s->{'out_of_plan'}      = 0;
    $s->{'overlap'}          = 0;
    $s->{'imagine'}          = 0;
    $s->{'value'}            = 0;
    $s->{'biconnect'}        = 0;

    if ($search_mode == NAIVE_SEARCH) {
        $s->{'packed_boxes'} = boxes_on_bases($brd);
        return;
    }
    if ($search_mode == SNAIL_SEARCH) {
        fill_snail_scores($brd, $s, $h->{'alg_type'});
        return;
    }
    if ($search_mode == NETLOCK_SEARCH) {
        fill_netlock_scores($brd, $s, $h->{'alg_type'});
        return;
    }

    $s->{'boxes_on_targets'} = ($brd =~ tr/\x06\x16//);
    $s->{'connectivity'}     = get_connectivity($brd);
    $s->{'boxes_in_level'}   = (($brd &. $BOX_ONLY) =~ tr/\x00//c);

    return if $search_mode == K_DIST_SEARCH;

    if ($search_mode == REV_SEARCH) {
        set_score_in_rev_mode($brd, $s, $pull_mode, $h);
        return;
    }

    return if $search_mode == XY_SEARCH;
    return if $search_mode == MINI_SEARCH;

    if ($search_mode == DEADLOCK_SEARCH) {
        $s->{'hotspots'} = size_of_deadlock_zone($brd);
        return;
    }

    if (   $search_mode == HF_SEARCH
        or $search_mode == BICON_SEARCH
        or $search_mode == MAX_DIST_SEARCH
        or $search_mode == MAX_DIST_SEARCH2)
    {
        fill_hf_scores($brd, $s, $pull_mode,
            $search_mode, $h);
        return;
    }

    if ($search_mode == WOBBLERS_SEARCH or $search_mode == ROOMS_DEADLOCK_SEARCH) {
        $s->{'boxes_on_targets'} = ($pull_mode == 0 ? ($brd =~ tr/\x06\x16//) : boxes_on_bases($brd));
        return;
    }

    if ($search_mode == GIRL_SEARCH) {
        fill_girl_scores($brd, $s, $pull_mode, $h);
        return;
    }

    if ($search_mode != NORMAL) {
        if ($search_mode != BASE_SEARCH) {
            Carp::confess('verify search mode')
                if $search_mode != FORWARD_WITH_BASES;
        }
    }

    $s->{'rooms_score'}     = score_rooms($brd);
    $s->{'dist_to_targets'} = get_scored_distance($brd, $h);

    if ($pull_mode == 0) {
        $s->{'packed_boxes'} =
            score_parked_boxes($brd, $h);
        $s->{'hotspots'} = hotspots_score($brd);
        $s->{'out_of_plan'} =
            get_out_of_plan_score($brd,
                $s->{'packed_boxes'}, $h);
        $s->{'imagine'} =
            imagine_score($brd, $search_mode, $h);
    }
    return;
}

# ====================================================================
# Games::Sokoban::Fest::AdvancedDeadlock  (was lib2/Games/Sokoban/Fest/AdvancedDeadlock.pm)
# ====================================================================

# Port of festival/advanced_deadlock.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. move_is_deadlocked() = the per-move gate the
# searches call after APPLYING a candidate move: matching feasibility
# (every box must still reach some target -- Hungarian on a 0/1 cost
# matrix), retrograde pull-elimination (try_pulling_all_zones /
# free_pull_deadlock), then the deep battery. The deep battery lives in
# the M7 modules -- runtime-qualified until they exist:
#   Stuck::is_stuck_deadlock  CorralDeadlock::corral_deadlock
#   KDistDeadlock::is_k_dist_deadlock  Wobblers::is_wobblers_deadlock
#   Wobblers::wobblers_search_actual  RoomsDeadlock::is_rooms_deadlock
# (a dragonfly gate therefore needs M7 first -- noted in the plan).
# The C original's commented-out stuck_after_pull() is omitted.
#
# Globals ledger:
#   reads:  $height $width $ncells @delta_y @delta_x $inner $index_num
#           Board::$initial_board Distance::distance_from_to
#   writes: nothing global


sub check_matching_deadlock ($b_in, $pull_mode, $search_mode) {
    my (@box_places, @target_places);
    my @cost;
    my $sol = {};

    # dragonfly uses the distance to bases, no match problems here
    return 0 if $search_mode == DRAGONFLY;

    # see if this is BASE_SEARCH
    my $has_bases = 0;
    for my $p (0 .. $ncells - 1) {
        $has_bases = 1 if vec($b_in, $p, 8) & BASE;
    }

    my $brd;
    if ($pull_mode == 0) {
        $brd = turn_fixed_boxes_into_walls($b_in);

        for my $i (0 .. $index_num - 1) {
            my $p2 = $index_to_p[$i];
            my $c = vec($brd, $p2, 8);
            push @box_places,    $i if $c & BOX;
            push @target_places, $i if $c & TARGET;
        }
    }
    else {
        for my $i (0 .. $index_num - 1) {
            my $p = $index_to_p[$i];

            if ($has_bases == 0) {
                push @box_places, $i if vec($initial_board, $p, 8) & BOX;
            }
            else {
                push @box_places, $i if vec($b_in, $p, 8) & BASE;
            }

            push @target_places, $i if vec($b_in, $p, 8) & BOX;
        }
    }

    my $box_num    = scalar @box_places;
    my $target_num = scalar @target_places;

    if ($pull_mode == 0) {    # in pull mode boxes can be eliminated
        return 1 if $box_num != $target_num;
    }


    for my $i (0 .. $box_num - 1) {
        for my $j (0 .. $box_num - 1) {
            $cost[$i][$j] = 1;
        }
    }

    if ($pull_mode == 0) {
        # update the graph by the updated board
        my $gd = allocate_graph();

        my $empty;
        $empty = $brd &. $NOT_BOX;
        build_graph($empty, 0, $gd);

        # don't allow positions where the player is closed in a hole
        make_holes_inactive($brd, $gd);

        for my $i (0 .. $box_num - 1) {
            my $p2 = $index_to_p[$box_places[$i]];

            my $targets;
            $targets = find_targets_of_place_without_init_graph($p2, $gd);

            for my $j (0 .. $target_num - 1) {
                $p2 = $index_to_p[$target_places[$j]];
                $cost[$i][$j] = 0 if vec($targets, $p2, 8);
            }
        }
    }
    else {
        for my $i (0 .. $box_num - 1) {
            for my $j (0 .. $target_num - 1) {
                $cost[$i][$j] = 0
                    if vec($distance_from_to, $box_places[$i] * $index_num + $target_places[$j], 32) < 1000000;
            }
        }
    }

    my $hc = {'prev_c' => [], 'prev_sol' => {}, 'prev_n' => -1};    # dummy, just for interface
    solve_hungarian($box_num, \@cost, $sol, $hc);

    if ($pull_mode == 0) {
        return 0 if $sol->{'weight'} == 0;
    }
    else {
        return 0 if $sol->{'weight'} == $box_num - $target_num;
    }

    return 1;    # deadlock
}

sub verify_simple_base_matching ($brd, $board_with_bases) {
    # check that every base has at least one box
    my (@box_places, @bases_places);

    for my $i (0 .. $index_num - 1) {
        my $p = $index_to_p[$i];

        push @bases_places, $i if vec($board_with_bases, $p, 8) & BASE;
        push @box_places,   $i if vec($brd, $p, 8) & BOX;
    }

    if (@bases_places != @box_places) {
        Carp::confess('Num box mismatch');
    }

    for my $base_index (@bases_places) {
        my $found = 0;
        for my $box_index (@box_places) {
            if (vec($distance_from_to, $base_index * $index_num + $box_index, 32) != 1000000) {
                $found = 1;
                last;
            }
        }
        return 0 unless $found;
    }
    return 1;
}


# ====================================================================
# Games::Sokoban::Fest::Positions  (was lib2/Games/Sokoban/Fest/Positions.pm)
# ====================================================================

# Port of festival/positions.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 translation: set_place_in_positions builds a Perl hash instead
# of walking every stored position against every new move behind a 14-bit
# bitmap pre-filter (the C hash substitute the USER named as the textbook
# case for this file). Rationale and the uniqueness argument that makes it
# equivalent are at the function.
#
# NOT converted, deliberately:
# - find_hash_in_positions stays a linear scan. Replacing it needs a map
#   that OUTLIVES the call, and the positions array plus its length are
#   owned by the caller (MiniSearch, XyDeadlock, KDistDeadlock,
#   CorralDeadlock, Wobblers, RoomsDeadlock). A package-level map would
#   break, because these sub-searches NEST (a corral proof runs a mini
#   search). Doing it properly means changing what allocate_positions
#   returns, i.e. a six-module contract change -- for a file measured at
#   0.1% of runtime (NYTProf, game 16899). Belongs to a later step.
# - direct_other_sons_to_position keeps its per-position hash_indicators
#   bitmaps: those index a position's CHILD hashes, which is the opposite
#   direction from a position->index map, and would need a child-hash
#   index maintained across calls.
#
# The flat position-array search representation
# used by the sub-searches (mini/deadlock/k-dist/xy/wobblers): every
# expanded position keeps its full move list, per-move scores and hashes;
# place_in_positions[j] points (Perl: holds the hashref of) the expanded
# child; deadlock knowledge propagates bottom-up through mark_deadlocks.
# A position is a hashref with the C field names; 'board' is the compact
# byte string (identical to the board representation here).
# The C pointer fixups become hashref assignments; struct COPIES
# (position_score, best_score) become {%$hashref} clones -- sharing the
# ref would alias later mutation.
# The hash bitmap tricks (>> 50 / >> 52) run on the unsigned 64-bit view;
# Perl's plain >> on IVs already shifts the raw two's-complement pattern.
#
# Globals ledger:
#   reads:  $height $width (+ everything Moves/Score read)
#   writes: nothing global

sub position_is_solved ($p) {
    my $brd = $p->{'board'};

    if ($p->{'search_mode'} == DEADLOCK_SEARCH and $p->{'pull_mode'} == 0) {
        # also check that targets are occupied
        return work_left_in_deadlock_zone($brd) ^ 1;
    }

    # in this mode we only check if we can exit/enlarge the deadlock zone;
    # other routines will verify if there is work left outside the zone
    return 0 if $p->{'search_mode'} == DEADLOCK_SEARCH and $p->{'pull_mode'};

    return board_is_solved($brd, $p->{'pull_mode'});
}

sub mark_deadlocks ($positions, $pos_num) {
    my $changed;

    do {
        $changed = 0;

        for my $i (0 .. $pos_num - 1) {
            my $pi = $positions->[$i];

            next if $pi->{'position_deadlocked'};    # already detected

            # a son became deadlocked?
            for my $j (0 .. $pi->{'moves_num'} - 1) {
                my $t = $pi->{'place_in_positions'}[$j];
                if (defined $t and $pi->{'move_deadlocked'}[$j] == 0
                    and $t->{'position_deadlocked'})
                {
                    $pi->{'move_deadlocked'}[$j] = 1;
                    $changed = 1;

                }
            }

            # all sons became deadlocked?
            my $all = 1;
            for my $j (0 .. $pi->{'moves_num'} - 1) {
                if ($pi->{'move_deadlocked'}[$j] == 0) {$all = 0; last;}
            }

            if ($all) {

                if (position_is_solved($pi) == 0) {
                    $pi->{'position_deadlocked'} = 1;
                    $changed = 1;
                }
            }
        }
    } while ($changed == 1);
    return;
}


sub find_hash_in_positions ($hash, $positions, $pos_num) {
    for my $i (0 .. $pos_num - 1) {
        return $i if $positions->[$i]{'position_hash'} == $hash;
    }
    return -1;
}

sub assert_board_after_move ($p, $move_index, $next) {
    my $brd = $p->{'board'};
    $brd = apply_move($brd, $p->{'moves'}[$move_index], $p->{'search_mode'});

    Carp::confess('hash error')
        if (substr($brd, 0, ($height * $width)) eq substr($next->{'board'}, 0, ($height * $width)) ? 1 : 0) == 0;
    return;
}

sub set_place_in_positions ($p, $positions, $pos_num) {
    # direct new children to existing nodes.
    # C walks every stored position against every new move, with a 14-bit
    # bitmap of the moves' hashes as a cheap pre-filter -- the whole thing
    # is a hand-built substitute for a lookup by hash. One Perl hash
    # replaces both, and turns the nested walk into two flat passes.
    # Safe because a position hash occurs AT MOST ONCE in the array:
    # expand_position refuses to store a position whose hash is already
    # there (find_hash_in_positions guard), so the C walk can match each
    # move against one stored position only -- the same one this map
    # returns.
    my %pos_by_hash;
    for my $i (0 .. $pos_num - 1) {
        $pos_by_hash{$positions->[$i]{'position_hash'}} = $positions->[$i];
    }

    for my $j (0 .. $p->{'moves_num'} - 1) {
        my $t = $pos_by_hash{$p->{'hashes'}[$j]};

        $p->{'place_in_positions'}[$j] = $t;    # undef when not stored yet
        next unless defined $t;

        assert_board_after_move($p, $j, $t);

        $p->{'move_deadlocked'}[$j] = 1 if $t->{'position_deadlocked'};
    }
    return;
}

sub allocate_position_structures ($p) {
    # Perl arrays grow on demand; kept for call-site parity
    $p->{'moves'}              = [];
    $p->{'hashes'}             = [];
    $p->{'scores'}             = [];
    $p->{'place_in_positions'} = [];
    $p->{'move_deadlocked'}    = [];
    return;
}

sub set_hash_indicators ($p) {
    # prepare a bitmap showing which hashes are possible
    $p->{'hash_indicators'} = [(0) x 64];

    for my $i (0 .. $p->{'moves_num'} - 1) {
        my $upper = ($p->{'hashes'}[$i] >> 52) & 0xFFF;
        $p->{'hash_indicators'}[$upper >> 6] |= 1 << ($upper & 0x3F);
    }
    return;
}

sub set_scores_to_moves ($brd, $moves, $scores, $hashes, $pull_mode, $search_mode, $h) {
    for my $i (0 .. $#$moves) {
        my $c;
        $c = $brd;
        $c = apply_move($c, $moves->[$i], $search_mode);

        $hashes->[$i] = get_board_hash($c);

        $scores->[$i] = {};
        score_board($c, $scores->[$i], $pull_mode, $search_mode, $h);
    }
    return;
}

sub fill_position_structures ($p, $brd, $moves, $pull_mode, $positions, $pos_num, $h) {
    my $moves_num = $p->{'moves_num'};

    for my $i (0 .. $moves_num - 1) {
        $p->{'moves'}[$i]           = $moves->[$i];
        $p->{'move_deadlocked'}[$i] = 0;
    }

    set_scores_to_moves($brd, $moves, $p->{'scores'}, $p->{'hashes'},
        $pull_mode, $p->{'search_mode'}, $h);

    set_hash_indicators($p);

    set_place_in_positions($p, $positions, $pos_num);

    # if a son points to a deadlocked node, mark it now
    for my $i (0 .. $moves_num - 1) {
        my $q = $p->{'place_in_positions'}[$i];
        if (defined $q) {
            $p->{'move_deadlocked'}[$i] = 1 if $q->{'position_deadlocked'};
        }
    }
    return;
}

sub set_first_position ($input_board, $pull_mode, $positions, $search_mode, $h) {
    Carp::confess("positions should be allocated\n") unless defined $positions;

    my $brd;
    $brd = $input_board;

    my $p = $positions->[0];

    $p->{'father'}      = undef;
    $p->{'depth'}       = 0;
    $p->{'weight'}      = 0;
    $p->{'pull_mode'}   = $pull_mode;
    $p->{'search_mode'} = $search_mode;
    $p->{'has_corral'}  = 0;

    $p->{'board'} = $brd;

    my @moves = find_possible_moves($brd, $pull_mode, \$p->{'has_corral'},
        $search_mode, $h);
    $p->{'moves_num'} = scalar @moves;

    $p->{'position_score'} = {};
    score_board($brd, $p->{'position_score'}, $pull_mode, $search_mode, $h);

    allocate_position_structures($p);
    fill_position_structures($p, $brd, \@moves, $pull_mode, $positions, 0, $h);

    $p->{'position_hash'} = get_board_hash($brd);

    $p->{'position_deadlocked'} = 0;

    if ($p->{'moves_num'} == 0) {
        if (position_is_solved($p) == 0) {
            $p->{'position_deadlocked'} = 1;
        }
    }
    return;
}

sub direct_other_sons_to_position ($pos, $positions, $pos_num) {
    my $hash = $pos->{'position_hash'};

    my $upper = ($hash >> 52) & 0xFFF;
    my $lower = $upper & 0x3F;
    $upper >>= 6;

    for my $i (0 .. $pos_num - 1) {
        my $p = $positions->[$i];

        next unless ($p->{'hash_indicators'}[$upper] >> $lower) & 1;

        for my $j (0 .. $p->{'moves_num'} - 1) {
            next if $p->{'hashes'}[$j] != $hash;

            next if defined $p->{'place_in_positions'}[$j];    # son already directed

            $p->{'place_in_positions'}[$j] = $pos;

            assert_board_after_move($p, $j, $pos);
        }
    }
    return;
}

sub all_sons_are_deadlocked ($p) {
    for my $i (0 .. $p->{'moves_num'} - 1) {
        next if $p->{'move_deadlocked'}[$i];

        my $q = $p->{'place_in_positions'}[$i];
        return 0 unless defined $q;    # move not explored yet

        Carp::confess('move_deadlocked error') if $q->{'position_deadlocked'};

        return 0 if $q->{'position_deadlocked'} == 0;
    }
    return 1;
}

sub expand_position ($node, $son, $pull_mode, $positions, $pos_num, $h) {
    if (find_hash_in_positions($node->{'hashes'}[$son], $positions, $pos_num) != -1) {
        Carp::confess('trying to expand known position');
    }

    my $brd = $node->{'board'};

    $brd = apply_move($brd, $node->{'moves'}[$son], $node->{'search_mode'});

    my $hash = get_board_hash($brd);
    Carp::confess('different hash than expected')
        if $hash != $node->{'hashes'}[$son];
    Carp::confess('position already exists?!')
        if find_hash_in_positions($hash, $positions, $pos_num) != -1;

    my $p = $positions->[$pos_num];

    $p->{'father'}      = $node;
    $p->{'pull_mode'}   = $pull_mode;
    $p->{'search_mode'} = $node->{'search_mode'};
    $p->{'has_corral'}  = 0;

    $p->{'board'} = $brd;

    my @moves = find_possible_moves($brd, $pull_mode, \$p->{'has_corral'},
        $node->{'search_mode'}, $h);
    $p->{'moves_num'} = scalar @moves;

    # struct copy in C -> clone
    $p->{'position_score'} = {%{ $node->{'scores'}[$son] }};

    allocate_position_structures($p);
    fill_position_structures($p, $brd, \@moves, $pull_mode, $positions, $pos_num, $h);

    $p->{'weight'} = $node->{'weight'} + $node->{'moves'}[$son]{'attr'}{'weight'};

    $p->{'position_hash'} = get_board_hash($brd);
    $p->{'depth'}         = $node->{'depth'} + 1;
    $node->{'place_in_positions'}[$son] = $p;

    direct_other_sons_to_position($p, $positions, $pos_num);

    $p->{'position_deadlocked'} = 0;

    if (all_sons_are_deadlocked($p)) {
        if (position_is_solved($p) == 0) {
            $p->{'position_deadlocked'} = 1;
            mark_deadlocks($positions, $pos_num + 1);
        }
    }
    return;
}


sub estimate_uniqe_moves ($positions, $pos_num) {
    my @hash = (0) x 1024;
    my $sum  = 0;

    for my $i (0 .. $pos_num - 1) {
        for my $j (0 .. $positions->[$i]{'moves_num'} - 1) {
            $hash[$positions->[$i]{'hashes'}[$j] & 0x3FF] = 1;
        }
    }

    $sum += $_ for @hash;
    return $sum;
}


# ====================================================================
# Games::Sokoban::Fest::KDistDeadlock  (was lib2/Games/Sokoban/Fest/KDistDeadlock.pm)
# ====================================================================

# Port of festival/k_dist_deadlock.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. The k-dist deadlock: for a given wall skeleton
# (fixed boxes wallified, target holes wallified, boxes+sokoban removed)
# a PULL search from the final position removes boxes whose pull distance
# is at least k (h->k_dist_value); whatever survives in EVERY reachable
# position is "forced" (a box must always be there), and adj_4/adj_9 keep
# per-cell lower bounds on the number of adjacent boxes. A position that
# misses a forced box, or has fewer adjacent boxes than the bound, is a
# proven deadlock. Verdict skeletons are memoized in the module-own
# k_dist hash (C: fixed array of 500 entries, linear scan -- kept).
#
# Globals ledger:
#   reads:  $height $width Board::$initial_board @delta_p
#           @delta_p_8 Distance::bfs_distance_from_to
#           ($debug_k_dist_deadlock toggle only)

# k_dist_entry: {'hash','b','forced','adj_4','adj_9'} (adj = lower bound
# on the number of adjacent boxes)


sub sokoban_touches_a_filled_hole ($brd) {
    # this is used when the sokoban cloud is of size 1.
    # although the player seems surrounded, a pull move might be possible!
    # if one of the surrounding walls is a filled garage
    my $p = get_sokoban_position($brd);

    for my $i (0 .. 3) {
        my $q = $p + $delta_p[$i];
        if (vec($brd, $q, 8) == WALL) {
            return 1 if vec($initial_board, $q, 8) != WALL;
        }
    }
    return 0;
}


sub check_for_k_dist_moves ($brd, $moves, $h) {    # returns the adjusted move list
    for my $i (0 .. $#$moves) {
        my $from = $moves->[$i]{'from'};
        my $to   = $moves->[$i]{'to'};

        if (vec($bfs_distance_from_to, $to * $index_num + $from, 32) >= $h->{'k_dist_value'}) {
            # allow a killing move only if the player can return to the pulled box
            # (not in a corral)
            my $c;
            $c = $brd;
            $c = apply_move($c, $moves->[$i], NORMAL);
            my $p = $index_to_p[$from];

            if (vec($c, $p, 8) & SOKOBAN) {
                my $kill = {%{ $moves->[$i] }};
                $kill->{'kill'} = 1;
                return ($kill);
            }
        }
    }
    return @$moves;
}


# ====================================================================
# Games::Sokoban::Fest::MiniSearch  (was lib2/Games/Sokoban/Fest/MiniSearch.pm)
# ====================================================================

# Port of festival/mini_search.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. A bounded greedy search over the flat position
# array: always expand the not-yet-expanded move with the most boxes on
# targets (connectivity as tie-break). can_put_all_on_targets() answers
# 1 = the position can be finished, 0 = proven stuck, -1 = unknown
# (aborted on max_size or a move explosion) -- the confirmation engine
# behind mpdb pairs and envelope rings.
#
# Globals ledger:
#   reads:  (via Positions prints)
#   writes: nothing global ( toggle only)

sub get_move_with_most_packing ($positions, $pos_num, $son_ref) {
    my $max_boxes_on_targets = -1;
    my $best_pos             = -1;
    my $best_connectivity    = 1000000;

    for my $i (0 .. $pos_num - 1) {
        my $p = $positions->[$i];
        next if $p->{'position_deadlocked'};

        for my $j (0 .. $p->{'moves_num'} - 1) {
            next if $p->{'move_deadlocked'}[$j];
            next if defined $p->{'place_in_positions'}[$j];

            next if $p->{'scores'}[$j]{'boxes_on_targets'} < $max_boxes_on_targets;

            if ($p->{'scores'}[$j]{'boxes_on_targets'} > $max_boxes_on_targets) {
                $max_boxes_on_targets = $p->{'scores'}[$j]{'boxes_on_targets'};
                $best_pos             = $i;
                $$son_ref             = $j;
                $best_connectivity    = $p->{'scores'}[$j]{'connectivity'};
                next;
            }

            Carp::confess('bad flow')
                if $p->{'scores'}[$j]{'boxes_on_targets'} != $max_boxes_on_targets;

            if ($p->{'scores'}[$j]{'connectivity'} < $best_connectivity) {
                $best_pos          = $i;
                $$son_ref          = $j;
                $best_connectivity = $p->{'scores'}[$j]{'connectivity'};
            }
        }
    }
    return $best_pos;
}

sub has_a_move_with_all_boxes_packed ($p) {
    # this routine is needed because the winning position can be the first
    # position. But get_move_with_most_packing can't choose an existing
    # position.
    my $brd = $p->{'board'};
    my $boxes_in_search = (($brd &. $BOX_ONLY) =~ tr/\x00//c);

    for my $i (0 .. $p->{'moves_num'} - 1) {
        return 1 if $p->{'scores'}[$i]{'boxes_on_targets'} == $boxes_in_search;
    }
    return 0;
}

sub can_put_all_on_targets ($brd, $max_size) {
    my $res = 0;
    my $son;

    my $h = init_helper();

    my $positions = [map {{'board' => undef, 'moves_num' => 0}} 1 .. $max_size];
    set_first_position($brd, 0, $positions, MINI_SEARCH, $h);
    my $pos_num = 1;

    while (1) {
        # for large levels the search may explode even with a limited "max_size"
        if ($positions->[$pos_num - 1]{'moves_num'} > 1000) {
            $res = -1;
            last;
        }

        if (has_a_move_with_all_boxes_packed($positions->[$pos_num - 1])) {
            $res = 1;
            last;
        }

        my $pos = get_move_with_most_packing($positions, $pos_num, \$son);

        if ($pos == -1) {
            $res = 0;
            last;
        }


        expand_position($positions->[$pos], $son, 0, $positions, $pos_num, $h);
        $pos_num++;


        my $c = $positions->[$pos_num - 1]{'board'};
        if (all_boxes_in_place($c, 0)) {
            $res = 1;
            last;
        }

        if ($pos_num == $max_size) {
            $res = -1;
            last;
        }
    }

    return $res;
}

# ====================================================================
# Games::Sokoban::Fest::RoomsDeadlock  (was lib2/Games/Sokoban/Fest/RoomsDeadlock.pm)
# ====================================================================

# Port of festival/rooms_deadlock.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. Room-local deadlock: when a push lands in a SMALL
# room (room+its corridor mouths, precomputed by init_rooms_deadlock),
# keep only that room's boxes and run the bounded position search
# restricted to pushes inside the room (other pushes become kill moves);
# exhaustion = the room's boxes alone are stuck. Cache-wrapped.
#
# Globals ledger:
#   reads:  $height $width $ncells @delta_y @delta_x
#           Rooms::$rooms_board Rooms::$rooms_num Board::$initial_board
#   writes: @room_with_corridors @room_size (init_rooms_deadlock)

sub init_rooms_deadlock () {
    my $brd;
    $brd = $initial_board;
    $brd &.= $NOT_BOX;

    @room_with_corridors = ();
    @room_size           = ();

    for my $t (0 .. $rooms_num - 1) {
        $room_with_corridors[$t] = $ZERO_BOARD;
        my $rr = \$room_with_corridors[$t];

        for my $p (0 .. $ncells - 1) {
if ($rooms_board->[$p] == $t) {
vec($$rr, $p, 8) = 1;

for my $k (0 .. 3) {
my $np = $p + $delta_p[$k];
vec($$rr, $np, 8) = 1
if (vec($brd, $np, 8) & OCCUPIED) == 0;
}
}
}

        $room_size[$t] = unpack('%32C*', $room_with_corridors[$t]);
    }
    return;
}

sub reduce_moves_in_rooms_deadlock_search ($moves, $h) {
    # returns the adjusted move list
    for my $i (0 .. $#$moves) {
        my $p = $index_to_p[$moves->[$i]{'to'}];

        next if $rooms_board->[$p] == 1000000;

        if ($rooms_board->[$p] != $h->{'tested_deadlock_room'}) {
            my $m = {%{ $moves->[$i] }};
            $m->{'kill'} = 1;
            return ($m);
        }
    }

    return @$moves;
}


# ====================================================================
# Games::Sokoban::Fest::Wobblers  (was lib2/Games/Sokoban/Fest/Wobblers.pm)
# ====================================================================

# Port of festival/wobblers.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. A "wobbler" = a box whose last move is trivially
# reversible (push/pull it back right away) -- such boxes are relaxed away
# (remove_wobblers turns them into player floor), and the bounded position
# search then asks whether the remaining rigid skeleton can still be
# finished; exhaustion = deadlock. Only used in pull mode
# (is_wobblers_deadlock returns 0 for push -- "not cost-effective").
# Cache-wrapped like the xy search.
#
# Globals ledger:
#   reads:  $height $width @delta_y @delta_x @delta_p @delta_p_8
# $global_boxes_in_level
#   writes: nothing global ( toggle only)

sub reduce_moves_in_wobblers_search ($moves) {    # returns the adjusted move list
    for my $i (0 .. $#$moves) {
        my $kill = 0;

        $kill = 1 if $moves->[$i]{'attr'}{'reversible'};    # a wobbler

        my $from = $moves->[$i]{'from'};
        my $to   = $moves->[$i]{'to'};

        if (abs($index_to_y[$from] - $index_to_y[$to]) >= 2) {
            $kill = 1 if abs($index_to_x[$from] - $index_to_x[$to]) >= 2;
        }

        if ($kill) {
            my $m = {%{ $moves->[$i] }};
            $m->{'kill'} = 1;
            return ($m);
        }
    }

    return @$moves;
}


# ====================================================================
# Games::Sokoban::Fest::XyDeadlock  (was lib2/Games/Sokoban/Fest/XyDeadlock.pm)
# ====================================================================

# Port of festival/xy_deadlock.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. The XY-projection deadlock: a box that (with the
# player behind it) can move both horizontally AND vertically is "free"
# and gets eliminated (kill move); the bounded position search then asks
# whether the remaining boxes can all reach their places -- exhausting the
# tree without success = proven deadlock. Results are memoized in the
# deadlock cache (0/1/2 = no/yes/search exceeded).
#
# Globals ledger:
#   reads:  $height $width $index_num
#   writes: nothing global ( toggle only)

sub mark_hv_indices ($brd, $moves) {    # returns the indices list
    my (@h_indices, @v_indices, @con_ok, @indices);

    for my $i (0 .. $#$moves) {
        $con_ok[$i] = 0;
        my $c = $brd;
        $c = apply_move($c, $moves->[$i], NORMAL);

        my $from_p = $index_to_p[$moves->[$i]{'from'}];

        $con_ok[$i] = 1 if vec($c, $from_p, 8) & SOKOBAN;
    }

    for my $i (0 .. $index_num - 1) {
        $h_indices[$i] = $v_indices[$i] = 0;
    }

    for my $i (0 .. $#$moves) {
        next if $con_ok[$i] == 0;

        my $from = $moves->[$i]{'from'};
        my $to   = $moves->[$i]{'to'};

        $v_indices[$from] = 1 if $index_to_y[$to] != $index_to_y[$from];
        $h_indices[$from] = 1 if $index_to_x[$to] != $index_to_x[$from];
    }

    for my $i (0 .. $index_num - 1) {
        $indices[$i] = $v_indices[$i] & $h_indices[$i];
    }
    return @indices;
}

sub reduce_moves_in_xy_search ($brd, $moves) {    # returns the adjusted move list
    my @hv_indices = mark_hv_indices($brd, $moves);

    for my $i (0 .. $#$moves) {
        if ($hv_indices[$moves->[$i]{'from'}]) {
            my $kill = {%{ $moves->[$i] }};
            $kill->{'kill'} = 1;
            return ($kill);
        }
    }
    return @$moves;
}

sub is_better_xy_score ($new_score, $old_score) {
    return 1 if $new_score->{'boxes_in_level'} < $old_score->{'boxes_in_level'};
    return 0 if $new_score->{'boxes_in_level'} > $old_score->{'boxes_in_level'};

    return 1 if $new_score->{'connectivity'} < $old_score->{'connectivity'};
    return 0 if $new_score->{'connectivity'} > $old_score->{'connectivity'};

    return 1 if $new_score->{'boxes_on_targets'} > $old_score->{'boxes_on_targets'};
    return 0 if $new_score->{'boxes_on_targets'} < $old_score->{'boxes_on_targets'};

    return 0;
}

sub get_best_xy_move ($positions, $pos_num, $son_ref) {
    my $best_pos = -1;
    my $best_score;

    for my $i (0 .. $pos_num - 1) {
        my $p = $positions->[$i];
        next if $p->{'position_deadlocked'};

        for my $j (0 .. $p->{'moves_num'} - 1) {
            next if $p->{'move_deadlocked'}[$j];
            next if defined $p->{'place_in_positions'}[$j];

            if ($best_pos == -1
                or is_better_xy_score($p->{'scores'}[$j], $best_score))
            {
                $best_pos   = $i;
                $$son_ref   = $j;
                $best_score = {%{ $p->{'scores'}[$j] }};    # struct copy
            }
        }
    }

    return $best_pos;
}


sub xy_search_actual ($brd, $pull_mode, $max_positions) {
    my $res = 0;
    my $son;

    my $h = init_helper();

    return NOT_DEADLOCK if all_boxes_in_place($brd, $pull_mode);

    my $positions = [map {{'board' => undef, 'moves_num' => 0}} 1 .. $max_positions];

    set_first_position($brd, $pull_mode, $positions, XY_SEARCH, $h);
    my $pos_num = 1;

    while (1) {
        my $total_leaves = estimate_uniqe_moves($positions, $pos_num);
        if ($total_leaves > $max_positions) {
            $res = SEARCH_EXCEEDED;
            last;
        }

        my $pos = get_best_xy_move($positions, $pos_num, \$son);

        if ($pos == -1) {
            $res = IS_DEADLOCK;
            last;
        }


        expand_position($positions->[$pos], $son, $pull_mode, $positions,
            $pos_num, $h);
        $pos_num++;


        my $c = $positions->[$pos_num - 1]{'board'};
        if (all_boxes_in_place($c, $pull_mode)) {

            $res = NOT_DEADLOCK;
            last;
        }

        if ($pos_num == $max_positions) {
            $res = SEARCH_EXCEEDED;
            last;
        }
    }


    return $res;
}

sub xy_deadlock_search ($brd, $pull_mode) {
    # this is a cache wrapper for xy_search_actual
    my $hash = get_board_hash($brd);

    my $res = (($cache{join '/', $hash, $pull_mode, XY_SEARCH} // $CACHE_MISS)->[0]);

    return $res if $res >= 0 and $res <= 2;


    $res = xy_search_actual($brd, $pull_mode, MAX_XY_DEADLOCK_SEARCH);

    insert_to_deadlock_cache($hash, $res, $pull_mode, XY_SEARCH);

    if ($res == 2) {
    }

    return $res;
}


sub is_xy_deadlock ($b_in, $pull_mode) {
    my $brd;


    if ($pull_mode == 0) {
        $brd = turn_fixed_boxes_into_walls($b_in);
    }
    else {
        $brd = $b_in;
        $brd &.= $NOT_BASE;
    }

    my $res = xy_deadlock_search($brd, $pull_mode);

    return 1 if $res == IS_DEADLOCK;
    return 0;
}

# ====================================================================
# Games::Sokoban::Fest::Heuristics  (was lib2/Games/Sokoban/Fest/Heuristics.pm)
# ====================================================================

# Port of festival/heuristics.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 translation: P1 at six sites (an index turned into a cell now
# reads the flat position from the table).
# NOT converted, deliberately: boxes_in_different_rooms keeps its y/x
# pair, because its last test compares the two ROWS and the two COLUMNS
# separately -- a diagonal test, where the axes genuinely mean different
# things. The remaining y/x scans go the other way, cell -> index, and
# that table is not exported flat (same note as Order.pm).
#
# The BASE_SEARCH (sink squares) machinery:
# - compute_bases_scc: strongly-connected component of bases in the push
#   graph -- boxes pulled into the biggest SCC can be "eliminated";
# - mark_sink_squares_moves: flag pulls into the SCC as base (kill) moves
#   and keep one eliminating pull per box (returns the adjusted list);
# - packing_search_advisor: the pull-mode pack advisor -- prefer a base
#   pull (floater first), else a reasonable pull off a target
#   (pick_pull_advisor_normal with the kill-zone/connectivity/room/
#   pull-length lexicographic candidate compare);
# - compute_possible_from_bases: the BASE move-generator filter.
# get_kill_zone keeps the C quirk of breaking after the FIRST kill square.
#
# Globals ledger:
#   reads:  $height $width $index_num Board::$initial_board
#           Distance::bfs_distance_from_to distance_from_to
#           Rooms::$rooms_board  RoomsDeadlock::@room_with_corridors
#           Holes::$target_holes
#   writes: nothing global

sub boxes_in_different_rooms ($index1, $index2) {
    my $index1_has_room = 0;
    my $index2_has_room = 0;

    return 1 if vec($bfs_distance_from_to, $index1 * $index_num + $index2, 32) >= BIG_DISTANCE;

    my $box1_p = $index_to_p[$index1];
    my $box2_p = $index_to_p[$index2];

    my $r1 = $rooms_board->[$box1_p];
    my $r2 = $rooms_board->[$box2_p];

    if ($r1 != 1000000 and $r2 != 1000000) {
        return 1 if $r1 != $r2;
    }

    if ($r1 != $r2) {
        if ($r1 != 1000000) {
            return 0 if vec($room_with_corridors[$r1], $box2_p, 8);
        }

        if ($r2 != 1000000) {
            return 0 if vec($room_with_corridors[$r2], $box1_p, 8);
        }

        return 1
            if $index_to_y[$index1] != $index_to_y[$index2]
            and $index_to_x[$index1] != $index_to_x[$index2];
    }

    return 0;
}


sub get_bases_as_board ($brd) {
    my $bases = $ZERO_BOARD;
    for my $p (0 .. $ncells - 1) {
        vec($bases, $p, 8) = 1 if vec($brd, $p, 8) & BASE;
    }
    return $bases;
}

sub compute_possible_from_bases ($brd) {
    # this routine is used by the moves generator.
    # A move that puts a box in a place unreachable from bases should be pruned.
    my ($bases, $board_without_boxes);

    $board_without_boxes = $initial_board &. $NOT_BOX;
    $bases = get_bases_as_board($brd);
    return find_targets_of_a_board_input($board_without_boxes, $bases);
}

sub test_base_matching ($brd, $from, $to) {
    my $c;

    my $from_p = $index_to_p[$from];    # P1
    my $to_p   = $index_to_p[$to];

    Carp::confess('no box') if (vec($brd, $from_p, 8) & BOX) == 0;
    Carp::confess('no base in matching') if (vec($brd, $to_p, 8) & BASE) == 0;

    $c = $brd;
    vec($c, $from_p, 8) &= 0xFF ^ BOX;
    vec($c, $to_p, 8)   &= 0xFF ^ BASE;

    my $res = check_matching_deadlock($c, 1, BASE_SEARCH);    # 1 = pull mode

    return 0 if $res == 1;

    return 1;
}

sub unreachable_area_contains_elim ($brd, $elim) {
    for my $p (0 .. $ncells - 1) {
        if (vec($elim, $p, 8)) {
            return 1 if (vec($brd, $p, 8) & SOKOBAN) == 0;
        }
    }
    return 0;
}

sub compute_bases_scc ($b_in) {
    my @mat;
    my $bases_num = 0;
    my (@bases, @scc, @scc_size);
    my ($brd, $targets);

    $brd = $b_in;
    $brd = turn_boxes_into_walls($brd);

    for my $p (0 .. $ncells - 1) {
$bases[$bases_num++] = $y_x_to_index_table[$p]
if vec($brd, $p, 8) & BASE;
}

    for my $i (0 .. $bases_num - 1) {
        for my $j (0 .. $bases_num - 1) {
            $mat[$i][$j] = 0;
        }
    }

    my $gd = allocate_graph();
    build_graph($brd, 0, $gd);    # 0 - push mode

    for my $i (0 .. $bases_num - 1) {
        my $p2 = $index_to_p[$bases[$i]];    # the callee wants y/x

        $targets = find_targets_of_place_without_init_graph($p2, $gd);

        Carp::confess('no self')                             # P1
            if vec($targets, $index_to_p[$bases[$i]], 8) == 0;

        for my $j (0 .. $bases_num - 1) {
            $mat[$i][$j] = 1 if vec($targets, $index_to_p[$bases[$j]], 8);
        }
    }

    for my $i (0 .. $bases_num - 1) {
        Carp::confess('bad diag') if $mat[$i][$i] != 1;
    }

    # compute the scc

    for my $i (0 .. $bases_num - 1) {
        $scc[$i] = -1;
    }

    my $current_scc = 0;
    for my $i (0 .. $bases_num - 1) {
        next if $scc[$i] != -1;    # node already associated with an SCC

        $scc[$i] = $current_scc;

        for my $j ($i .. $bases_num - 1) {
            $scc[$j] = $current_scc if $mat[$i][$j] & $mat[$j][$i];
        }

        $current_scc++;
    }

    # find the biggest scc

    for my $i (0 .. $bases_num - 1) {
        $scc_size[$i] = 0;
        for my $j ($i .. $bases_num - 1) {
            $scc_size[$i]++ if $scc[$j] == $scc[$i];
        }
    }

    my $max_size = 0;
    for my $i (0 .. $bases_num - 1) {
        $max_size = $scc_size[$i] if $scc_size[$i] > $max_size;
    }

    my $scc_out = $ZERO_BOARD;

    for my $i (0 .. $bases_num - 1) {
        next if $scc_size[$i] != $max_size;

        for my $j ($i .. $bases_num - 1) {
            if ($scc[$j] == $scc[$i]) {
                vec($scc_out, $index_to_p[$bases[$j]], 8) = 1;    # P1
            }
        }
    }
    return $scc_out;
}

sub mark_sink_squares_moves ($brd, $moves) {    # returns the adjusted move list
    my $has_base_move = 0;
    my @tmp;
    my $elim;
    my @move_tested;

    my $moves_num = scalar @$moves;

    $elim = compute_bases_scc($brd);

    return @$moves if unreachable_area_contains_elim($brd, $elim);

    # first step: find if there is a sink move.

    for my $i (0 .. $moves_num - 1) {
        $move_tested[$i] = 0;
    }

    for my $i (0 .. $moves_num - 1) {
        $move_tested[$i] = 1;

        next if vec($elim, $index_to_p[$moves->[$i]{'to'}], 8) == 0;    # P1

        next
            if boxes_in_different_rooms($moves->[$i]{'from'}, $moves->[$i]{'to'})
            == 0;
        next
            if test_base_matching($brd, $moves->[$i]{'from'}, $moves->[$i]{'to'})
            == 0;

        $moves->[$i]{'base'} = 1;
        $has_base_move = 1;
        last;
    }

    if ($has_base_move == 0) {
        for my $i (0 .. $moves_num - 1) {
            $moves->[$i]{'base'} = 0;
        }
        return @$moves;
    }

    # second step: find only one legitimate sink move for each box
    # keep only eliminating moves. keep just one source

    my @box_was_pulled = (0) x $index_num;

    for my $i (0 .. $moves_num - 1) {
        if ($move_tested[$i]) {
            next if $moves->[$i]{'base'} == 0;    # already checked and found bad
        }

        if ($moves->[$i]{'base'} == 1) {    # already tested and found good
            push @tmp, $moves->[$i];
            $box_was_pulled[$moves->[$i]{'from'}] = 1;
            next;
        }

        next if $box_was_pulled[$moves->[$i]{'from'}];

        next if vec($elim, $index_to_p[$moves->[$i]{'to'}], 8) == 0;    # P1
        next
            if boxes_in_different_rooms($moves->[$i]{'from'}, $moves->[$i]{'to'})
            == 0;

        # this test is the heaviest, so we keep it last
        next
            if test_base_matching($brd, $moves->[$i]{'from'}, $moves->[$i]{'to'})
            == 0;

        $moves->[$i]{'base'} = 1;
        push @tmp, $moves->[$i];
        $box_was_pulled[$moves->[$i]{'from'}] = 1;
    }
    return @tmp;
}


# ====================================================================
# Games::Sokoban::Fest::HfSearch  (was lib2/Games/Sokoban/Fest/HfSearch.pm)
# ====================================================================

# Port of festival/hf_search.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 pass: one P1 site. The whole-board scans stay y/x: they call
# helpers that take y/x, and one of them probes TWO cells out in a
# direction, which flat arithmetic would obscure.
#
# The HF ("hotspot-free") search family: score
# positions mainly by connectivity, rooms and "hotspots" = boxes that block
# their surroundings (a box no player side can reach, or a box touching an
# occupied cell where the imagined board has none). The REV strategy runs a
# forward search first, freezes its best reached board as the imagined
# board (setup_rev_board), and then scores the backward search by the
# Hungarian matching distance to that board (set_rev_distance).
#
# Globals ledger:
#   reads:  $height $width @delta_y @delta_x
#           Board::$initial_board Board::$inner Holes::$target_holes
#           Distance::$distance_from_to (packed string, passed through)
#   writes: nothing global (fills helper fields imagined_hf_board/wallified)

sub can_be_accessed_from_some_direction ($brd, $p) {
    for my $i (0 .. 3) {
        next if vec($brd, $p + $delta_p[$i], 8) == WALL;
        next if vec($brd, $p + $delta_p[$i] * 2, 8) & OCCUPIED;

        return 1;
    }

    return 0;
}

sub hf_hotspots ($brd, $pull_mode, $h) {
    my $sum = 0;

    if ($pull_mode) {
        for my $p (0 .. $ncells - 1) {
if (vec($brd, $p, 8) & BOX) {
$sum++
if can_be_accessed_from_some_direction($brd, $p) == 0;
}
}
        return $sum;
    }

    my $img = $h->{'imagined_hf_board'};

    for my $p (0 .. $ncells - 1) {

if ((vec($brd, $p, 8) & BOX) and ((vec($img, $p, 8) & BOX) == 0)) {
for my $k (0 .. 3) {
if (vec($brd, $p + $delta_p[$k], 8)
& OCCUPIED)
{
$sum++;
last;
}
}
}

if ((vec($img, $p, 8) & BOX) and ((vec($brd, $p, 8) & BOX) == 0)) {
$sum++ if can_be_accessed_from_some_direction($brd, $p) == 0;
}
}

    return $sum;
}


sub can_be_pushed_to_direction ($brd, $p, $d) {
    return 0 if vec($brd, $p + $delta_p[$d], 8) & OCCUPIED;
    return 0 if vec($brd, $p + $delta_p[($d + 2) & 3], 8) & OCCUPIED;

    return 0 if deadlock_in_direction($brd, $p, $d);

    return 1;
}

sub get_rev_hotspots ($brd) {
    # count boxes that can't be pushed
    my $hs = $ZERO_BOARD;

    for my $p (0 .. $ncells - 1) {
if (vec($brd, $p, 8) & BOX) {
next if vec($brd, $p, 8) & TARGET;
# no need to be pushed

my $k;
for ($k = 0; $k < 4; $k++) {
last if can_be_pushed_to_direction($brd, $p, $k);
}

vec($hs, $p, 8) = 1 if $k == 4;
}
}
    return $hs;
}

sub rev_hotspots_distance ($brd, $h) {
    my ($hs, $b2);
    my $dist = [];
    my $sum  = 0;

    $hs = get_rev_hotspots($brd);

    if (unpack('%32C*', $hs) == 0) {
        return get_scored_distance($brd, $h);
    }
    # no hotspots. With nothing better to do, push away from targets

    # find BFS distance from hotspots
    $b2 = $initial_board &. $NOT_BOX;
    $hs = expand_group($b2, $hs, $dist);

    for my $p (0 .. $ncells - 1) {
$sum += $dist->[$p]
if vec($brd, $p, 8) & BOX;
}
    return $sum;
}

sub rev_hotspots ($brd) {
    my $hs;

    $hs = get_rev_hotspots($brd);

    return unpack('%32C*', $hs);
}

sub set_score_in_rev_mode ($brd, $s, $pull_mode, $h) {
    if ($pull_mode == 0) {
        $s->{'rooms_score'}     = score_rooms($brd);
        $s->{'hotspots'}        = rev_hotspots($brd);
        $s->{'dist_to_targets'} = rev_hotspots_distance($brd, $h);

        return;
    }

    $s->{'boxes_on_targets'} = compare_to_imagined_hf($brd, $h);
    $s->{'dist_to_targets'}  = get_scored_distance($brd, $h);
    return;
}

sub compare_to_imagined_hf ($brd, $h) {
    my $sum = 0;

    my $img = $h->{'imagined_hf_board'};

    for my $p (0 .. $ncells - 1) {
if (vec($brd, $p, 8) & BOX) {
$sum++ if vec($img, $p, 8) & BOX;
}
}
    return $sum;
}

sub get_distance_in_hf_search ($brd, $s, $h) {
    my ($untouched, $tmp);
    my $dist = [];
    my $sum  = 0;

    # if ($s->{'connectivity'} == 1)  # TODO : help hotspots
    return get_scored_distance($brd, $h);

    # the C original leaves the untouched-areas variant below dead
    # (the if above it is commented out there too); kept for fidelity
    $untouched = get_untouched_areas($brd);

    $tmp = $initial_board &. $NOT_BOX;
    $untouched = expand_group($tmp, $untouched, $dist);

    for my $p (0 .. $ncells - 1) {
$sum += $dist->[$p]
if vec($brd, $p, 8) & BOX;
}
    return $sum;
}

sub fill_hf_scores ($brd, $s, $pull_mode, $search_mode, $h) {
    $s->{'boxes_on_targets'} = 0;
    # we don't use this feauture in hf, so don't partition cells by it

    $s->{'hotspots'} = hf_hotspots($brd, $pull_mode, $h);

    if ($pull_mode == 0) {
        $s->{'imagine'} = compare_to_imagined_hf($brd, $h);
        return;
    }

    if (($search_mode == BICON_SEARCH) or ($search_mode == MAX_DIST_SEARCH)) {
        $s->{'biconnect'} = biconnect_score($brd, 0);
    }

    $s->{'rooms_score'} = score_rooms($brd);

    # $s->{'dist_to_targets'} = get_scored_distance($brd, $h);
    $s->{'dist_to_targets'} = get_distance_in_hf_search($brd, $s, $h);
    return;
}

# ====================================================================
# Games::Sokoban::Fest::ParkOrder  (was lib2/Games/Sokoban/Fest/ParkOrder.pm)
# ====================================================================

# Port of festival/park_order.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 translation: P1 in get_boxes_in_place. Two y/x scans are kept
# on purpose: the board printer needs rows to place its newlines, and the
# initial-box collector goes cell -> index via y_x_to_index, whose
# out-of-range check is a tripwire that a flat rewrite would drop (see
# the same note in Order.pm).
#
# The parking plan: conclude_parking walks the
# best backward-search node up to its root and turns the pull moves into
# a forward parking order (from/to/until hashrefs; from = -2 marks a box
# already on board at the plan start, until = the step that moves it
# away, -1 = stays forever). fix_consecutive_pushes concatenates a->b
# b->c chains, keep_only_perm/reduce_parking_order trim the plan when no
# boxes get removed, score_parked_boxes scores a board against the plan
# (the packed_boxes feature), next_parking_place names the next box the
# plan wants placed (the opener's blocker).
# DEVIATION: next_parking_place's init scan is bounded by
# parking_order_num (C reads past the array when the plan has no -2
# entries).
#
# Cross-module calls resolved at runtime, fully qualified:
#   Girl::find_best_RL_parking_node (GIRL mode only)
#
# Globals ledger:
#   reads:  $height $width $index_num $inner
#           Board::$initial_board $global_boxes_in_level
#   writes: nothing global (all state in the helper)


sub mandatory_inits_missing ($has_box, $init_num, $h) {
    my $parking_order = $h->{'parking_order'};

    for my $i (0 .. $init_num - 1) {
        if ($parking_order->[$i]{'until'} == -1) {
            # box is there from the init to the end
            return 1 if $has_box->[$i] == 0;
        }
    }
    return 0;
}

sub get_number_of_mandatory_inits ($has_box, $init_num, $h) {
    my $n = 0;
    my $parking_order = $h->{'parking_order'};

    for my $i (0 .. $init_num - 1) {
        if ($parking_order->[$i]{'until'} == -1) {
            $n++ if $has_box->[$i];
        }
    }
    return $n;
}

sub get_boxes_in_place ($brd, $has_box, $h) {    # fills the $has_box aref
    my $parking_order = $h->{'parking_order'};

    for my $i (0 .. $h->{'parking_order_num'} - 1) {
        $has_box->[$i] =                                                  # P1
            (vec($brd, $index_to_p[$parking_order->[$i]{'to'}], 8) & BOX ? 1 : 0);
    }
    return;
}

sub score_parked_boxes ($brd, $h) {
    my @has_box;
    my $init_num  = 0;
    my $good_init = 0;
    my $parking_order = $h->{'parking_order'};

    get_boxes_in_place($brd, \@has_box, $h);

    for my $i (0 .. $h->{'parking_order_num'} - 1) {
        $init_num++ if $parking_order->[$i]{'from'} == -2;
    }

    if (mandatory_inits_missing(\@has_box, $init_num, $h)) {
        return get_number_of_mandatory_inits(\@has_box, $init_num, $h);
    }

    my $packed = $h->{'parking_order_num'};

    # We check if "packed" boxes are in place.
    # Some boxes are allowed to be missing if they were moved later on
    # (in "until" move)

    for my $i (reverse $init_num .. $h->{'parking_order_num'} - 1) {
        next if $has_box[$i];    # box is in place, "packed" not contradicted

        # so box is not in place.

        if ($parking_order->[$i]{'until'} == -1) {
            $packed = $i;
        }
        else {
            $packed = $i if $parking_order->[$i]{'until'} >= $packed;
        }
    }

    for my $i (0 .. $init_num - 1) {
        $good_init++
            if $has_box[$i] or $parking_order->[$i]{'until'} < $packed;
    }

    $packed -= ($init_num - $good_init);

    return $packed;
}


# ====================================================================
# Games::Sokoban::Fest::CorralDeadlock  (was lib2/Games/Sokoban/Fest/CorralDeadlock.pm)
# ====================================================================

# Port of festival/corral_deadlock.cpp (Festival 3.1, Yaron Shoham).
# Slavish transcription. The corral deadlock prover: split the board into
# player-connectivity components (with fixed boxes wallified), build a
# deadlock zone from one component (or a pair of components touching the
# same box), keep only the boxes of that zone, and run the bounded
# DEADLOCK_SEARCH: if no move sequence can shrink connectivity / free the
# zone, the corral is a proven deadlock. Verdicts (incl. every deadlocked
# inner position and the break-free father chain) go to the shared
# deadlock cache; SEARCH_EXCEEDED entries are re-evaluated with a bigger
# budget once their query count reaches a power of two (should_reevaluate).
# mini_corral: small corrals (<=5 boxes) queried 100 times get the exact
# can_put_all_on_targets check and may be learned as Stuck patterns.
# The commented-out C code (corral_deadlock_search_actual_2,
# learn_pull_deadlock) is not transcribed.
#
# DEVIATION: C reuses int_board (stride MAX_SIZE) for the 'checked'
# component-pair matrix; components are NOT cells, so with the dynamic
# stride-$width representation that indexing would collide -- 'checked'
# is a plain local 2D array here (same values, different storage).
#
# Globals ledger:
#   reads:  $height $width Board::$global_boxes_in_level @delta_p
#   writes: nothing global ( toggle only)

sub check_for_deadlock_zone_moves ($brd, $moves) {    # returns the adjusted move list
    # if a box can be sent outside the deadlock zone, it is better than other moves

    for my $i (0 .. $#$moves) {
        my $p = $index_to_p[$moves->[$i]{'to'}];
        next if vec($brd, $p, 8) & DEADLOCK_ZONE;

        my $kill = {%{ $moves->[$i] }};
        $kill->{'kill'} = 1;
        return ($kill);
    }

    return @$moves;
}


# In this example the deadlock zone gets bigger (in pull mode) after pulling the box.
# ########
# # $    #
# #$     #
# # $    #
# #  $@  #
# ########


# ====================================================================
# Games::Sokoban::Fest::Girl  (was lib2/Games/Sokoban/Fest/Girl.pm)
# ====================================================================

# Port of festival/girl.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 translation: P4 in the two whole-board scans (a maximum
# and a sum do not care about visit order). Everything else was already
# flat.
#
# GIRL mode = "reinforcement-learning" value search:
# each position is scored by a fixed linear formula -- a handful of features
# (packed boxes, boxes on targets, connectivity, distance to targets,
# overlap, a 0.95^k decay of the remaining boxes) normalized to [0,1] and
# multiplied by hand-tuned weight vectors (separate for pull/push mode).
# The epsilon-greedy descent (Greedy.pm) then walks the tree by these
# values, and find_best_RL_parking_node picks the backward node whose value
# chain seeds the parking plan.
#
# DEVIATION (storage width): C stores node values as 32-bit floats
# ((float)score_to_value); Perl numbers are doubles, so every stored value
# goes through unpack 'f', pack 'f' -- without this the greedy
# tie behavior would diverge from the exe in the last bits.
#
# Globals ledger:
#   reads:  $height $width Global::$global_boxes_in_level
#   writes: $girl_distance $max_push_dist @gamma_table $inv_n_boxes
#           $dist_normalizer (module-own, set by init_girl_variables)

sub init_girl_distance ($brd) {
    get_distance_from_targets($brd, $girl_distance);


    # init max_push_dist (P4: one flat scan -- a maximum does not care
    # about visit order)
    $max_push_dist = 0;
    for my $p (0 .. $ncells - 1) {
        my $d = $girl_distance->[$p];
        next if $d == 1000000;
        $max_push_dist = $d if $d > $max_push_dist;
    }
    return;
}

sub get_girl_distance ($brd) {
    my $sum = 0;

    for my $p (0 .. $ncells - 1) {    # P4: a sum does not care about order
        $sum += $girl_distance->[$p] if vec($brd, $p, 8) & BOX;
    }
    return $sum;
}

sub init_gamma_table () {
    my $gamma_val = 0.95;

    for my $i (0 .. $global_boxes_in_level) {
        $gamma_table[$i] = $gamma_val**$i;
    }
    return;
}

sub init_girl_variables ($brd) {
    init_girl_distance($brd);
    init_gamma_table();

    $inv_n_boxes     = 1 / $global_boxes_in_level;
    $dist_normalizer = 1 / ($global_boxes_in_level * $max_push_dist);

    return;
}


# constants for the next routine


sub fill_girl_scores ($brd, $s, $pull_mode, $h) {
    $s->{'dist_to_targets'} = get_girl_distance($brd);

    if ($pull_mode == 0) {
        $s->{'packed_boxes'} = score_parked_boxes($brd, $h);
        $s->{'overlap'}      = overlap_score($brd, $h);
    }
    return;
}

# ====================================================================
# Games::Sokoban::Fest::Imagine  (was lib2/Games/Sokoban/Fest/Imagine.pm)
# ====================================================================

# Port of festival/imagine.cpp (Festival 3.1, Yaron Shoham).
# Phase-2 pass: POD only. The phase-1 code was already flat -- the three
# index_to_y_x calls here feed routines that genuinely want y/x.
#
# Imagined boards: replay the FULL parking plan
# and snapshot the board just before every permanent placement; a search
# position is then scored by how many of its boxes already sit on the
# imagined board of its progress stage (packed boxes excluded).
# imagine_score REQUIRES a complete plan (parking_order_num ==
# global_boxes_in_level) -- the C original exits with "debug order"
# otherwise, which is why a forward NORMAL search cannot run planless.
# The imagine data lives in the helper ({'imagine'}{'imagined_boards'} /
# {'fixed_at_step'} boards, {'imagine_packed_num'}, 'imagined_boards_num').
# compute_imagine_distance lives in MatchDistance.pm (match_distance.cpp).
#
# Globals ledger:
#   reads:  $height $width Board::$initial_board $global_boxes_in_level
#   writes: nothing global (all state in the helper)


sub get_imagined_board ($brd, $relevant_board_ref, $h) {

    Carp::confess('imagine not allocated') unless defined $h->{'imagine'};

    my $im = $h->{'imagine'};

    my $packed_boxes = score_parked_boxes($brd, $h);

    if ($packed_boxes == $global_boxes_in_level) {    # level is solved
        $$relevant_board_ref = $im->{'imagined_boards_num'} - 1;
        return $brd;
    }

    my $i;
    for ($i = 0; $i < $im->{'imagined_boards_num'}; $i++) {
        last if $im->{'imagine_packed_num'}[$i] > $packed_boxes;
    }

    $$relevant_board_ref = $i;

    return $im->{'imagined_boards'}[$i];
}

sub imagine_score ($brd, $search_mode, $h) {
    my $relevant_board;
    my $imagined;
    my $sum = 0;

    Carp::confess('imagine not allocated') unless defined $h->{'imagine'};

    return 0
        if $search_mode == FORWARD_WITH_BASES
        or $h->{'boxes_were_removed'}
        or $search_mode == GIRL_SEARCH;

    return compare_to_imagined_hf($brd, $h)
        if $search_mode == HF_SEARCH;

    Carp::confess("why here?\n") if $search_mode != NORMAL;

    Carp::confess('debug order')
        if $h->{'parking_order_num'} != $global_boxes_in_level;

    $imagined = get_imagined_board($brd, \$relevant_board, $h);

    my $im = $h->{'imagine'};

    for my $p (0 .. $ncells - 1) {
        if (vec($brd, $p, 8) & BOX) {
            if (vec($im->{'imagined_boards'}[$relevant_board], $p, 8) & BOX) {
                # don't count packed boxes
                $sum++
                    if vec($im->{'fixed_at_step'}[$relevant_board], $p, 8) == 0;
            }
        }
    }

    return $sum;
}


# ====================================================================
# Games::Sokoban::Fest  (was lib2/Games/Sokoban/Fest.pm)
# ====================================================================

# Top of the Festival->Perl port ( tree): the strategy
# scheduler of festival/sokoban_solver.cpp (solve_with_alg + the single-core
# time control) plus a solve() wrapper with the same signature and contract
# as Games::Sokoban::Festival (the C exe pipe wrapper):
#
#   solve($gameid, $code, $limit) -> ($reason, $path, $doba)
#     $reason = 'SOLVED' | 'TIMEOUT' (time limit exceeded)
#             | 'FAILED' (gave up early; $LastFail holds the reason)
#
# Input is game_blob.code (digit schema), converted to XSB here, so the
# returned LURD path lives in the same code-space as every stored path.
# DB-free by design (the solve() caller contract).
#
# Scheduler = the C original verbatim: 8 strategies A-H, each = backward
# packing search (1/3 of the slice) -> parking plan -> forward search on the
# rest; run one after another, each getting 1/(strategies left) of the time
# still remaining ($forced_alg pins a single strategy for the full slice).
#   strategy:  A            B          C     D   E      F         G    H
#   backward:  BASE         MAX_DIST2  GIRL  HF  BICON  MAX_DIST  REV  DRAGONFLY
#   forward:   FWD_W_BASES  HF         GIRL  HF  HF     HF        REV  NAIVE
#
# DEVIATIONS (documented in place):
#   - single-core only: the C pthread paths (2/4/8 cores) are not ported,
#     cores_num != 1 is refused. One search tree, one helper.
#   - $LOG_SIZE default 20, not the C 23 (~1.5 GB/core): Perl nodes are far
#     heavier; the size feeds only the hash table and the capacity fuses,
#     not the search order (proved by the M4-M7 gates running log 16).
#   - setup_plan_features pre-zeroes the oop zone boards: C leaves the step
#     past the last written one as malloc garbage; Perl undef would die.
#   - solution extraction returns the LURD string (mirror of the C -pipe
#     emit_pipe_solution) instead of appending to solutions.sok.
#   - the "imagined board" pair, two halves of ONE fix (2026-08-08), the
#     first place where the port deliberately behaves BETTER than the exe:
#       (a) reset_helper clears imagined_hf_board + wallified, so a board
#           cannot survive into the next strategy or the next LEVEL;
#       (b) forward_search_control skips an HF or REV second half whose
#           board the first half never produced (a starved time budget makes
#           the first half's slice round down to zero).
#     C dies in both situations and, because its error path is
#     printf + getch, HANGS instead of reporting. Regression gate:
#     ai/t_fest_short_limit.pl. The oracle gate may diverge here.
#
# Globals ledger:
#   reads:  $height $width
# writes: $time_limit $start_time $end_time
# $global_fail_reason (via preprocess), (forced to 1)


# Read-only seam for the harnesses: the helper holds everything a strategy
# produced -- above all the parking plan (parking_order/parking_order_num and
# the untrimmed full_parking_order). $Helper is a lexical because nothing may
# WRITE it from outside. It used to be read from outside too -- that is how the
# plan gates got a plan out after a solve pinned to one strategy -- but that line
# of investigation settled as a negative and its gates went in 2026-08-26's
# sweep.

sub preprocess_level ($brd) {
    $global_fail_reason = 'Unknown reason';

    return (0, $brd) if ($height == 0) or ($width == 0);

    # The deadlock memo is a record of what a search DID, not of what the level
    # is, so it starts empty for every level.
    %cache = (); $total_deadlock_cache_entries = 0;

    # The analysis of THIS level is already loaded: keep it, and only clear the
    # library the search learns as it goes ($Analysed_key above says why this is
    # safe, and which two gates prove it).
    my $key = $width . ':' . $brd;
    if ($key eq $Analysed_key) {
        return (1, expand_sokoban_cloud($brd));
    }

    # From here the maps are being rebuilt, so nothing may claim the old level:
    # a run that dies in analyse_rooms below must not leave a key pointing at
    # half of one analysis and half of another.
    $Analysed_key = '';

    prepare_pattern_offsets();

    init_inner($brd);
    init_index_x_y();

    save_initial_board($brd);
    $brd = expand_sokoban_cloud($brd);

    set_forbidden_tunnel();
    mark_target_holes($brd);


    set_distances($brd);

    my $res = analyse_rooms($brd);
    return (0, $brd) if $res == 0;

    init_rooms_deadlock();

    init_hotspots($brd);

    build_mpdb2();
    build_pull_mpdb2();

    init_envelope_patterns();

    init_girl_variables($brd);

    detect_snail_level($brd);

    # Claim the level -- unless the hotspot table was thrown away, in which case
    # this analysis is an accident of the clock and the next solve rebuilds it.
    $Analysed_key = $key unless $Hotspots_incomplete;

    return (1, $brd);
}

# ---- the stored level analysis (Games::Sokoban::Festival_Parser) ------------
# The four tables above are a function of the LEVEL, not of where the boxes
# stand, so they can be built once and kept. These three subs are the whole
# seam: the parser asks for them, a driver stores them, and a campaign hands
# them back before it solves.
#
# They live HERE and not in the parser because the tables are file lexicals --
# from outside the module they read as empty, which is a failure that looks
# like a result (it already fooled one of this project's own gates).
#
# The handed-back analysis itself lives in $Analysis, declared up beside
# $Analysed_key because preprocess_level reads it.

# THE ANALYSIS STATE, in ONE list. Both directions are generated from it, so a
# variable that is exported but never installed -- or installed but never
# exported -- cannot happen: there is a single place that knows the names, and
# it is this one. Adding a map to the analysis means adding a line here and
# NOTHING else.
#
# The third field is who needs it: 'core' is read by every search, the rest name
# the strategy that alone reads them, and initvars_<MODE>() installs those. The
# list is not trusted to be complete because it was written carefully -- it is
# proved complete by running the engine on an installed analysis and comparing
# it with the same engine on a computed one -- a forgotten line then shows up as
# a divergence rather than as a slightly worse solver. The pin that did this by
# expansion-order fingerprint was retired 2026-08-26 with the transcription era;
# ai/eq_fest_promote.pl asks the same question of the answer instead.
@ANALYSIS_STATE = (
    # geometry and terrain
    ['core', 'height',            \$height, 0],
    ['core', 'width',             \$width, 0],
    ['core', 'ncells',            \$ncells, 0],
    ['core', 'delta_p',           \@delta_p],
    ['core', 'delta_p_8',         \@delta_p_8],
    ['core', 'zero_board',        \$ZERO_BOARD, ''],
    ['core', 'dz_len',            \$DZ_len, -1],
    ['core', 'square_place_p',    \@square_place_p],
    ['core', 'inner',             \$inner, ''],
    ['core', 'index_num',         \$index_num, 0],
    ['core', 'y_x_to_index',      \@y_x_to_index_table],
    ['core', 'index_to_x',        \@index_to_x],
    ['core', 'index_to_y',        \@index_to_y],
    ['core', 'index_to_p',        \@index_to_p],
    ['core', 'base_graph',        \@base_graph],

    # the level as it starts
    ['core', 'initial_board',     \$initial_board, ''],
    ['core', 'sok_y',             \$global_initial_sokoban_y, 0],
    ['core', 'sok_x',             \$global_initial_sokoban_x, 0],
    ['core', 'boxes_in_level',    \$global_boxes_in_level, 0],

    # holes and tunnels
    ['core', 'target_holes',      \$target_holes, ''],
    ['core', 'semi_holes',        \$semi_holes, ''],
    ['core', 'push_tunnel',       \$forbidden_push_tunnel, ''],
    ['core', 'pull_tunnel',       \$forbidden_pull_tunnel, ''],

    # distances
    ['core', 'distance',          \$distance_from_to, ''],
    ['core', 'bfs_distance',      \$bfs_distance_from_to, ''],
    ['core', 'impossible_place',  \@impossible_place],

    # rooms
    ['core', 'rooms_board',       \$rooms_board, []],
    ['core', 'rooms_num',         \$rooms_num, 0],
    ['core', 'room_corridors',    \@room_with_corridors],
    ['core', 'room_size',         \@room_size],

    # hotspots
    ['core', 'blocks_place',      \$blocks_place, ''],
    ['core', 'completely_blocks', \$completely_blocks, ''],
    ['core', 'targets_from',      \@targets_reachable_from],

    # pair deadlocks and envelopes
    ['core', 'mpdb_list',         \@mpdb_list],
    ['core', 'mpdb_board',        \$mpdb_board, ''],
    ['core', 'pull_mpdb_list',    \@pull_mpdb_list],
    ['core', 'pull_mpdb_board',   \$pull_mpdb_board, ''],
    ['core', 'envelope',          \@new_envelope_patterns],

    # read by ONE strategy each -- installed by initvars_<MODE>()
    ['FF_GIRL', 'girl_distance',   \$girl_distance, []],
    ['FF_GIRL', 'max_push_dist',   \$max_push_dist, 0],
    ['FF_GIRL', 'gamma_table',     \@gamma_table],
    ['FF_GIRL', 'inv_n_boxes',     \$inv_n_boxes, 0],
    ['FF_GIRL', 'dist_normalizer', \$dist_normalizer, 0],

    ['snail',   'snail_detected',  \$snail_level_detected, 0],
    ['snail',   'snail_target_y',  \$snail_target_y, 0],
    ['snail',   'snail_target_x',  \$snail_target_x, 0],
    ['snail',   'snail_dist',      \$snail_dist, []],
    ['snail',   'snail_chain',     \$snail_chain, ''],
    ['snail',   'snail_chain_len', \$snail_chain_len, 0],
    ['snail',   'netlock_detected', \$netlock_level_detected, 0],
    ['snail',   'netlock_grid',    \$netlock_grid, ''],
);

# WIPE THE LOT. Firstbet::clearvars() is not decoration (USER): a level's maps
# have to start from nothing, or a smaller level inherits the tail of a bigger
# one. Three of these were doing exactly that -- @base_graph, @targets_reachable_from
# and @gamma_table are FILLED but were never emptied, and each is only ever read
# up to the current level's count, so the leftovers were invisible in a running
# process and only surfaced when the analysis was stored and compared. The
# analysis has to be a function of its level and of nothing else.
#
# Generated from @ANALYSIS_STATE, so unlike a hand-written clearvars() it cannot
# fall behind the list it is supposed to cover.
sub clearvars () {
    for my $e (@ANALYSIS_STATE) {
        my (undef, undef, $r, $empty) = @$e;
        if (ref $r eq 'ARRAY') {@$r = ()}
        else                   {$$r = ref $empty eq 'ARRAY' ? [] : $empty}
    }

    # ...and the engine now holds no level at all, which is the whole point:
    # leaving this set would let preprocess_level take its warm early return and
    # hand the caller the state we have just emptied.
    $Analysed_key = '';
    return;
}

# Everything the analysis produced, ready to be frozen into game_blob.fest.
# Called by Games::Sokoban::Festival_Parser and by nothing else.
sub export_analysis () {
    my %a;
    for my $e (@ANALYSIS_STATE) {
        my (undef, $k, $r) = @$e;
        $a{$k} = ref $r eq 'ARRAY' ? [@$r] : $$r;
    }
    return \%a;
}

# ============================================================================
# THE API -- everything above this line is machinery, everything below is what
# a caller uses.
# ============================================================================

# The analysis's own time budget in seconds, when parse() is given none: the
# Sokoban project's figure, generous because there it was spent once per level
# and a hotspot table that finishes was the whole point. A program that
# analyses a level when it solves it passes its own.
our $BUDGET = 36_000;

# Stamped into every hash and checked on thaw. Bump it whenever this analysis
# changes what it PRODUCES -- a frozen hash that no longer matches the code
# reading it is the one failure here that no result would reveal.
our $STAMP = 'fest-analysis-1';

# parse($code, $budget) -> the analysis hash: the digit board (rows joined by
# commas) as Games::Sokoban::Solver::Code returns it, and the budget in
# seconds. Dies if the level will not analyse. The two fuses are reported, not
# fatal: hotspots_incomplete says the hotspot table was thrown away after a
# quarter of the budget, envelopes_incomplete that the envelope analysis
# stopped at half of it; the rest of the analysis is complete either way.
sub parse ($code, $budget = $BUDGET) {
    clearvars();    # no level may inherit the tail of the one analysed before it

    my @rows = split /,/, $code;
    my $brd  = set_board_from_code(\@rows, scalar @rows);
    my $key  = $width . ':' . $brd;

    $time_limit = $budget;
    $start_time = time();

    my ($pre_ok, undef) = preprocess_level($brd);

    # preprocess_level said no. That is not a level to skip quietly: either the
    # code is malformed or the analysis has a defect, and both want finding.
    Carp::confess("parse: the engine refused to analyse this level ($global_fail_reason)")
        unless $pre_ok == 1;

    my $a = export_analysis();
    $a->{'hotspots_incomplete'}  = $Hotspots_incomplete  ? 1 : 0;
    $a->{'envelopes_incomplete'} = $Envelopes_incomplete ? 1 : 0;
    $a->{'key'}                  = $key;
    $a->{'stamp'}                = $STAMP;
    $a->{'ver'}                  = $VERSION;
    return $a;
}

# The blok table of the Parser's analysis, copied into this one under the key
# the engine reads when its $BLOK_REPLACES is on (without the key it refuses to
# run that way). The engine's own tables know nothing of the bloks, which is
# why the copy is made here and not in export_analysis.
sub with_blok ($fest, $blok) {
    Carp::confess('with_blok: not an analysis hash') unless ref $fest eq 'HASH';
    Carp::confess('with_blok: the blok table is a hash') unless ref $blok eq 'HASH';
    $fest->{'blok'} = Storable::dclone($blok);
    return $fest;
}

# compress(nfreeze()) -- NETWORK order, never freeze(): native-order Storable
# is not portable, and a frozen analysis may be kept and read elsewhere.
sub freeze ($fest) {
    Carp::confess('freeze: not an analysis hash') unless ref $fest eq 'HASH';
    Carp::confess('freeze: analysis carries no key') unless length($fest->{'key'} // q{});
    return compress(nfreeze($fest));
}

sub thaw ($blob) {
    Carp::confess('thaw: the frozen analysis is empty') unless defined $blob && length $blob;

    my $raw  = uncompress($blob);
    my $fest = defined $raw ? Storable::thaw($raw) : undef;
    Carp::confess('thaw: the frozen analysis does not unpack -- it is corrupt')
        unless ref $fest eq 'HASH';

    Carp::confess(sprintf(
        "thaw: this analysis is stamped '%s', the code reads '%s' -- analyse the level again",
        $fest->{'stamp'} // '(none)', $STAMP))
        unless ($fest->{'stamp'} // q{}) eq $STAMP;

    return $fest;
}

1;
