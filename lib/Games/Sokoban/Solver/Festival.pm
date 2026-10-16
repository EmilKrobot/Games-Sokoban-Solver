package Games::Sokoban::Solver::Festival;
our $VERSION = '0.01';
use v5.42;
use warnings FATAL => 'uninitialized';
no warnings 'recursion';
use Carp           ();
use Storable       ();
use Time::HiRes    ();
use Term::ANSIColor ();
use Compress::Zlib  ();
use Digest::MD5     ();
use Games::Sokoban::Solver::Console ('backline', 'backlinen');
use Games::Sokoban::Solver::Data    ();
use Games::Sokoban::Solver::Memory  ();
use Games::Sokoban::Solver::Munkres ();
use Games::Sokoban::Solver::Path    ();
use constant {
    WALL                         => 1,
    BOX                          => 2,
    TARGET                       => 4,
    SOKOBAN                      => 8,
    BASE                         => 16,
    DEADLOCK_ZONE                => 32,
    OCCUPIED                     => 3,
    PACKED_BOX                   => 6,
    SPACE                        => 0,
    MAX_SOL_LEN                  => 1500,
    NORMAL                       => 0,
    DEADLOCK_SEARCH              => 1,
    BASE_SEARCH                  => 2,
    K_DIST_SEARCH                => 3,
    MINI_SEARCH                  => 4,
    FORWARD_WITH_BASES           => 5,
    GIRL_SEARCH                  => 6,
    REV_SEARCH                   => 7,
    DRAGONFLY                    => 8,
    WOBBLERS_SEARCH              => 9,
    HF_SEARCH                    => 10,
    ROOMS_DEADLOCK_SEARCH        => 11,
    NAIVE_SEARCH                 => 12,
    XY_SEARCH                    => 13,
    MINI_CORRAL                  => 14,
    IGNORE_CORRAL                => 15,
    BICON_SEARCH                 => 16,
    MAX_DIST_SEARCH              => 17,
    MAX_DIST_SEARCH2             => 18,
    SNAIL_SEARCH                 => 19,
    NETLOCK_SEARCH               => 20,
    OPTIMIZE_PACKED              => 0,
    OPTIMIZE_CONNECTIVITY        => 1,
    OPTIMIZE_ROOMS               => 2,
    OPTIMIZE_HOTSPOTS            => 3,
    OPTIMIZE_OUT_OF_PLAN         => 4,
    K_DIST_MAX_POSITIONS         => 600,
    MAX_K_DIST_HASH_SIZE         => 500,
    NOT_DEADLOCK                 => 0,
    IS_DEADLOCK                  => 1,
    SEARCH_EXCEEDED              => 2,
    MAX_ROOMS_DEADLOCK_SEARCH    => 200,
    MAX_WOBBLERS_DEADLOCK_SEARCH => 50,
    MAX_XY_DEADLOCK_SEARCH       => 500,
    BIG_DISTANCE                 => 6,
    MAX_STUCK_PATTERN_SIZE       => 12,
    DISTILL_ON_TARGETS           => 0,
    DISTILL_XY                   => 1,
    MAX_DEADLOCK_SEARCH          => 50,
    MAX_DRAGONFLY_ROOTS          => 200,
    MOVE_WEIGHT                  => 3 << 30,
    SC_BOXES_IN_LEVEL            => 1,
    SC_DIST_TO_IMAGINED          => 4,
    SC_DIST_TO_TARGETS           => 5,
    SC_VALUE                     => 12,
    SCORE_KEYS                   => [
        qw(biconnect boxes_in_level boxes_on_targets connectivity dist_to_imagined dist_to_targets
            hotspots imagine out_of_plan overlap packed_boxes rooms_score value)
    ],
    ADVISOR_KEYS                 => [qw(pack connectivity rooms hotspots opener out_of_plan explorer imagine)],
    FEST_STAMP                   => 'fest-analysis-1',
    ENDING                       => '%-12s %5d %3d %4d %-10s %6d %6d %12.4f %8s %8s %8s %8s %9s',
    PROGRESS                     => '%-12s %5d ... %12d %9d %-4s %12.2f %12.0f %9d',
};
my (
    $Abort_reason,                 $Allocated,               $Any_core_solved,        $BOX_ONLY,
    $Bfs_distance_from_to,         $Blocks_place,            $Blok_boxes,             $Blok_usable,
    $CACHE_MISS,                   $Completely_blocks,       $DZ_ONLY,                $DZ_len,
    $Dist_normalizer,              $Distance_from_to,        $Dragonfly_nodes,
    $Dragonfly_nodes_num,          $Dragonfly_roots_num,     $Forbidden_pull_tunnel,  $Forbidden_push_tunnel,
    $Girl_distance,                $Global_boxes_in_level,   $Global_fail_reason,     $Global_initial_sokoban_x,
    $Global_initial_sokoban_y,     $HELPER_TEMPLATE,         $Height,                 $Helper,
    $INNER_ONLY,                   $Index_num,               $Initial_board,          $Initial_sokoban_p,
    $Inner,                        $Inv_epsilon,             $Inv_n_boxes,            $K_dist_hash_num,
    $Log_deadlock_cache,           $Log_perimeter_size,      $Max_push_dist,          $Mpdb_board,
    $NOT_BASE,                     $NOT_BOX,                 $NOT_DZ,                 $NOT_SOKOBAN,
    $Ncells,                       $Netlock_grid,            $Netlock_level_detected, $Next_poll,
    $OCC_ONLY,                     $PATTERNS,                $Pull_mpdb_board,        $Rooms_board,
    $Rooms_num,                    $SOK_ONLY,                $Semi_holes,             $Snail_chain,
    $Snail_chain_len,              $Snail_dist,              $Snail_level_detected,   $Snail_target_x,
    $Snail_target_y,               $Solve_nseen,             $Target_holes,           $Tick,
    $Time_limit,                   $Total_deadlock_cache_entries,
    $Total_perimeter_entries,      $Tree,                    $Width,
    $ZERO_BOARD,                   %Blok_sets,               %Cache,                  %Dragonfly_q,
    %FF_MODE,                      %Perimeter,               %Progress,               @ANALYSIS_STATE,
    @Base_graph,                   @Base_indices,            @Delta_p,                @Delta_p_8,
    @Delta_x,                      @Delta_x_8,               @Delta_y,                @Delta_y_8,
    @Dragonfly_roots,              @FF_NAME,                 @Gamma_table,            @Impossible_place,
    @Index_to_p,                   @Index_to_x,              @Index_to_y,             @K_dist_hash,
    @Mpdb_list,                    @New_envelope_patterns,   @Patterns,               @Pull_mpdb_list,
    @Pull_patterns,                @Pull_weights,            @Push_weights,           @Room_size,
    @Room_with_corridors,          @Square_place_p,          @Square_place_x,         @Square_place_y,
    @Stuck_patterns,               @Target_indices,          @Targets_reachable_from, @Y_x_to_index_table,
   );
our ($BLOK_REPLACES, $LastFail, $MAX_GB, $QUIET, $RACE_FLAG, $RACE_GID);
$Time_limit                   = 600;
$Height                       = 0;
$Width                        = 0;
@Delta_y                      = (-1,  0, 1,  0);
@Delta_x                      = ( 0,  1, 0, -1);
@Delta_y_8                    = (-1, -1, 0, 1, 1,  1,  0, -1);
@Delta_x_8                    = ( 0,  1, 1, 1, 0, -1, -1, -1);
$Global_boxes_in_level        = 0;
$Any_core_solved              = 0;
$Global_fail_reason           = '';
$Ncells                       = 0;
@Delta_p                      = ();
@Delta_p_8                    = ();
$ZERO_BOARD                   = '';
$Initial_board                = '';
$Inner                        = '';
$Index_num                    = 0;
$CACHE_MISS                   = [-1, 0];
$Total_deadlock_cache_entries = 0;
$Log_deadlock_cache           = 22;
$Target_holes                 = '';
$Semi_holes                   = '';
$DZ_len                       = -1;
$Rooms_board                  = [];
$Rooms_num                    = 0;
$Snail_level_detected         = 0;
$Netlock_level_detected       = 0;
$Netlock_grid                 = '';
$Snail_dist                   = [];
$Snail_chain                  = '';
$Snail_chain_len              = 0;
$Forbidden_push_tunnel        = '';
$Forbidden_pull_tunnel        = '';
$PATTERNS                     = Games::Sokoban::Solver::Data::load('fest_patterns.stor');
@Patterns                     = @{ $PATTERNS->{'patterns'} };
@Pull_patterns                = @{ $PATTERNS->{'pull_patterns'} };
@Square_place_y               = ([-2, -2], [-1, 0], [1, 1], [-1, 0]);
@Square_place_x               = ([-1, 0], [1, 1], [-1, 0], [-2, -2]);
$Distance_from_to             = '';
$Bfs_distance_from_to         = '';
$Blocks_place                 = '';
$Completely_blocks            = '';
$Mpdb_board                   = '';
$Pull_mpdb_board              = '';
$Total_perimeter_entries      = 0;
$Log_perimeter_size           = 25;
$K_dist_hash_num              = 0;
$Inv_epsilon                  = 20;
$Girl_distance                = [];
$Max_push_dist                = 0;
$Inv_n_boxes                  = 0;
$Dist_normalizer              = 0;
@Pull_weights                 = (-0.185353, -0.217472, 0.154112, 0.382115, 0.471096, 0.195508);
@Push_weights                 = (0.468630, -0.177816, -0.233347, 0.052064, 0.326019, 0.164538, 0.348762, -0.141263);
$Dragonfly_nodes              = [];
$Dragonfly_nodes_num          = 0;
$Dragonfly_roots_num          = 0;
$LastFail                     = '';
$MAX_GB                       = 0;
$QUIET                        = 0;
$BLOK_REPLACES                = 0;
$Blok_usable                  = 0;
$Abort_reason                 = '';
$Next_poll                    = 0;
$Tick                         = 0;
$Solve_nseen                  = 0;
$Allocated                    = 0;
($Global_initial_sokoban_y, $Global_initial_sokoban_x) = (0, 0);
($Snail_target_y, $Snail_target_x)                     = (0, 0);
$HELPER_TEMPLATE = {
    'alg_type'                 => 0,
    'boxes_were_removed'       => 0,
    'enable_inefficient_moves' => 0,
    'full_parking_order'       => [],
    'full_parking_order_num'   => 0,
    'imagine'                  => {},
    'imagined_hf_board'        => '',
    'k_dist_value'             => 0,
    'level_solved'             => 0,
    'my_core'                  => 0,
    'oop'                      => {},
    'parking_order'            => [],
    'parking_order_num'        => 0,
    'perimeter_found'          => 0,
    'request'                  => {},
    'scored_distance'          => [],
    'sol_len'                  => 0,
    'sol_move'                 => [],
    'tested_deadlock_room'     => 0,
    'used_in_plan'             => '',
    'wallified'                => '',
    'weighted_search'          => 1,
};
%FF_MODE = (
    'FF_BASE'      => 0,
    'FF_MAXDIST2'  => 1,
    'FF_GIRL'      => 2,
    'FF_HF'        => 3,
    'FF_BICON'     => 4,
    'FF_MAXDIST'   => 5,
    'FF_REV'       => 6,
    'FF_DRAGONFLY' => 7,
);
@FF_NAME        = sort {$FF_MODE{$a} <=> $FF_MODE{$b}} keys %FF_MODE;
@ANALYSIS_STATE = (
    ['core',    'height',            \$Height],
    ['core',    'width',             \$Width],
    ['core',    'ncells',            \$Ncells],
    ['core',    'delta_p',           \@Delta_p],
    ['core',    'delta_p_8',         \@Delta_p_8],
    ['core',    'zero_board',        \$ZERO_BOARD],
    ['core',    'dz_len',            \$DZ_len],
    ['core',    'square_place_p',    \@Square_place_p],
    ['core',    'inner',             \$Inner],
    ['core',    'index_num',         \$Index_num],
    ['core',    'y_x_to_index',      \@Y_x_to_index_table],
    ['core',    'index_to_x',        \@Index_to_x],
    ['core',    'index_to_y',        \@Index_to_y],
    ['core',    'index_to_p',        \@Index_to_p],
    ['core',    'base_graph',        \@Base_graph],
    ['core',    'initial_board',     \$Initial_board],
    ['core',    'sok_y',             \$Global_initial_sokoban_y],
    ['core',    'sok_x',             \$Global_initial_sokoban_x],
    ['core',    'boxes_in_level',    \$Global_boxes_in_level],
    ['core',    'target_holes',      \$Target_holes],
    ['core',    'semi_holes',        \$Semi_holes],
    ['core',    'push_tunnel',       \$Forbidden_push_tunnel],
    ['core',    'pull_tunnel',       \$Forbidden_pull_tunnel],
    ['core',    'distance',          \$Distance_from_to],
    ['core',    'bfs_distance',      \$Bfs_distance_from_to],
    ['core',    'impossible_place',  \@Impossible_place],
    ['core',    'rooms_board',       \$Rooms_board],
    ['core',    'rooms_num',         \$Rooms_num],
    ['core',    'room_corridors',    \@Room_with_corridors],
    ['core',    'room_size',         \@Room_size],
    ['core',    'blocks_place',      \$Blocks_place],
    ['core',    'completely_blocks', \$Completely_blocks],
    ['core',    'targets_from',      \@Targets_reachable_from],
    ['core',    'mpdb_list',         \@Mpdb_list],
    ['core',    'mpdb_board',        \$Mpdb_board],
    ['core',    'pull_mpdb_list',    \@Pull_mpdb_list],
    ['core',    'pull_mpdb_board',   \$Pull_mpdb_board],
    ['core',    'envelope',          \@New_envelope_patterns],
    ['core',    'max_push_dist',     \$Max_push_dist],
    ['core',    'gamma_table',       \@Gamma_table],
    ['core',    'inv_n_boxes',       \$Inv_n_boxes],
    ['core',    'dist_normalizer',   \$Dist_normalizer],
    ['core',    'snail_detected',    \$Snail_level_detected],
    ['core',    'snail_target_y',    \$Snail_target_y],
    ['core',    'snail_target_x',    \$Snail_target_x],
    ['core',    'snail_dist',        \$Snail_dist],
    ['core',    'snail_chain',       \$Snail_chain],
    ['core',    'snail_chain_len',   \$Snail_chain_len],
    ['core',    'netlock_detected',  \$Netlock_level_detected],
    ['core',    'netlock_grid',      \$Netlock_grid],
    ['FF_GIRL', 'girl_distance',     \$Girl_distance],
);

sub progress () {
    my $doba = Time::HiRes::time() - $Progress{'t0'};
    $doba = 0.000001 if $doba < 0.000001;
    backline(sprintf PROGRESS,
        $Progress{'label'}, $Progress{'gameid'}, $Solve_nseen, $Tree->{'expansions_num'} // 0,
        $Progress{'phase'}, $doba, $Solve_nseen / $doba, $Total_perimeter_entries);
    return;
}

sub run_aborted () {
    return 1 if $Abort_reason;
    my $now = time;
    if ($now != $Tick) {
        $Tick = $now;
        if ($RACE_FLAG && $RACE_GID && $RACE_FLAG->{$RACE_GID}) {
            $Abort_reason = 'IGNORE';
            return 1;
        }
    }
    return 0 if $now < $Next_poll;
    $Next_poll = $now + 8;
    progress() unless $QUIET;
    $Abort_reason = 'MEMCAP' if $MAX_GB && Games::Sokoban::Solver::Memory::used_gb() > $MAX_GB;
    return $Abort_reason ? 1 : 0;
}
sub barva($reason,$ending) {
   return if $QUIET > 1;
   state $colour = {'SOLVED', 'bright_green', 'TIMEOUT', 'bright_yellow', 'IGNORE', 'white' };
   my $color = $colour->{$reason} // 'bright_red';
   backlinen(Term::ANSIColor::colored($ending,$color));
}

sub in_group ($val, $group) {
    for my $g (@$group) {
        return 1 if $g == $val;
    }
    return 0;
}

sub time_limit_exceeded ($time_allocation, $local_start_time) {
    my $running_time = time() - $local_start_time;
    if ($running_time > $time_allocation) {
        return 1;
    }
    return 0;
}

sub init_board_geometry () {
    Carp::confess('init_board_geometry: no level dimensions')
        if $Height == 0 or $Width == 0;
    for my $d (0 .. 3) {
        $Square_place_p[$d] = [map {$Square_place_y[$d][$_] * $Width + $Square_place_x[$d][$_]} 0, 1];
    }
    $Ncells      = $Height * $Width;
    @Delta_p     = (-$Width, 1, $Width, -1);
    @Delta_p_8   = map {$Delta_y_8[$_] * $Width + $Delta_x_8[$_]} 0 .. 7;
    $ZERO_BOARD  = "\0" x $Ncells;
    $NOT_BOX     = chr(0xFF ^ BOX) x $Ncells;
    $NOT_SOKOBAN = chr(0xFF ^ SOKOBAN) x $Ncells;
    $NOT_BASE    = chr(0xFF ^ BASE) x $Ncells;
    $BOX_ONLY    = chr(BOX) x $Ncells;
    $SOK_ONLY    = chr(SOKOBAN) x $Ncells;
    $OCC_ONLY    = chr(OCCUPIED) x $Ncells;
    return;
} ## end sub init_board_geometry

sub get_sokoban_position ($brd) {
    my $t = $brd&.$SOK_ONLY;
    return $-[0] if $t =~ /[^\0]/;
    Carp::confess("sokoban not found\n");
}

sub turn_boxes_into_walls ($brd) {
    for my $p (0 .. $Ncells - 1) {
        vec($brd, $p, 8) = WALL if vec($brd, $p, 8) & BOX;
    }
    return $brd;
}

sub flood_mask ($free, $cloud) {
    my $pad1 = "\0";
    my $padw = "\0" x $Width;
    while (1) {
        my $grown = $pad1 . substr($cloud, 0, -1);
        $grown|.= substr($cloud, 1) . $pad1;
        $grown|.=$padw . substr($cloud, 0, -$Width);
        $grown|.= substr($cloud, $Width) . $padw;
        $grown&.=$free;
        $grown|.=$cloud;
        last if $grown eq $cloud;
        $cloud = $grown;
    }
    return $cloud;
} ## end sub flood_mask

sub expand_sokoban_cloud ($brd, $seed = undef) {
    my $free = ($brd&.$OCC_ONLY) =~ tr/\x00\x01\x02\x03/\xFF\x00\x00\x00/r;
    my $cloud;
    if (defined $seed) {
        $cloud = $ZERO_BOARD;
        vec($cloud, $seed, 8) = 0xFF;
    }
    else {
        $cloud = ($brd&.$SOK_ONLY) =~ tr/\x08/\xFF/r;
    }
    my $pad1 = "\0";
    my $padw = "\0" x $Width;
    while (1) {
        my $grown = $pad1 . substr($cloud, 0, -1);
        $grown|.= substr($cloud, 1) . $pad1;
        $grown|.=$padw . substr($cloud, 0, -$Width);
        $grown|.= substr($cloud, $Width) . $padw;
        $grown&.=$free;
        $grown|.=$cloud;
        last if $grown eq $cloud;
        $cloud = $grown;
    }
    return $brd|. ($cloud&.$SOK_ONLY);
} ## end sub expand_sokoban_cloud

sub get_board_hash ($brd) {
    return unpack('q', Digest::MD5::md5($brd));
}

sub all_boxes_in_place ($brd, $pull_mode) {
    for my $p (0 .. $Ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;
        if ($pull_mode == 0) {
            return 0 if (vec($brd, $p, 8) & TARGET) == 0;
        }
        else {
            return 0 if (vec($Initial_board, $p, 8) & BOX) == 0;
        }
    }
    return 1;
}

sub board_is_solved ($brd, $pull_mode) {
    if ($pull_mode) {
        return 0 if (vec($brd, $Initial_sokoban_p, 8) & SOKOBAN) == 0;
    }
    return all_boxes_in_place($brd, $pull_mode);
}

sub enter_reverse_mode ($brd, $mark_bases) {
    $brd&.=$NOT_SOKOBAN;
    for my $p (0 .. $Ncells - 1) {
        my $c = vec($brd, $p, 8);
        vec($brd, $p, 8) = 0            if $c == BOX;
        vec($brd, $p, 8) = BOX | TARGET if $c == TARGET;
        next unless ($mark_bases);
        vec($brd, $p, 8) |= BASE if vec($Initial_board, $p, 8) & BOX;
    }
    return $brd;
}

sub boxes_on_bases ($brd) {
    my $sum = 0;
    for my $p (0 .. $Ncells - 1) {
        next   if (vec($brd, $p, 8) & BOX) == 0;
        $sum++ if vec($Initial_board, $p, 8) & BOX;
    }
    return $sum;
}

sub turn_targets_into_walls ($brd) {
    for my $p (0 .. $Ncells - 1) {
        vec($brd, $p, 8) = WALL if vec($brd, $p, 8) & TARGET;
    }
    return $brd;
}

sub turn_targets_into_packed ($brd) {
    for my $p (0 .. $Ncells - 1) {
        vec($brd, $p, 8) = PACKED_BOX if vec($brd, $p, 8) & TARGET;
    }
    return $brd;
}

sub go_to_final_position_with_given_walls ($brd) {
    for my $p (0 .. $Ncells - 1) {
        my $c = vec($brd, $p, 8);
        next if $c == WALL;
        if ($c & TARGET) {vec($brd, $p, 8) |= BOX;}
        else             {vec($brd, $p, 8) &= 0xFF ^ BOX;}
    }
    return $brd;
}

sub put_sokoban_in_zone ($brd, $zones, $z) {
    $brd&.=$NOT_SOKOBAN;
    for my $p (0 .. $Ncells - 1) {
        next unless $zones->[$p] == $z;
        vec($brd, $p, 8) |= SOKOBAN if (vec($brd, $p, 8) & OCCUPIED) == 0;
    }
    $brd = expand_sokoban_cloud($brd);
    return $brd;
}

sub get_untouched_areas ($brd) {
    my $untouched = $ZERO_BOARD;
    for my $p (0 .. $Ncells - 1) {
        next                       if vec($Inner, $p, 8) == 0;
        next                       if vec($brd,   $p, 8) & OCCUPIED;
        vec($untouched, $p, 8) = 1 if (vec($brd, $p, 8) & SOKOBAN) == 0;
    }
    return $untouched;
}

sub allocate_deadlock_cache () {
    $Log_deadlock_cache           = 22;
    %Cache                        = ();
    $Total_deadlock_cache_entries = 0;
    return;
}

sub deadlock_cache_is_full () {
    my $limit = 1 << ($Log_deadlock_cache - 1);
    return 0 if $Total_deadlock_cache_entries < $limit;
    return 1;
}

sub insert_to_deadlock_cache ($hash, $res, $pull_mode, $alg) {
    return if deadlock_cache_is_full();
    my $key = "$hash/$pull_mode/$alg";
    my $e   = $Cache{$key};
    if (defined $e) {
        Carp::confess('different cache value!') if ($e->[0] ^ $res) == 1;
        $e->[0] = $res                          if $e->[0] == 2;
    }
    else {
        $Cache{$key} = [$res, 0];
        $Total_deadlock_cache_entries++;
    }
    return;
}

sub dragonfly_init_queue ($q, $n) {
    $q->{'elements'}  = [];
    $q->{'heap_size'} = 0;
    $q->{'n'}         = $n;
    return;
}

sub is_better_dragonfly_score ($e1, $e2) {
    return 1 if $e1->{'dist'} < $e2->{'dist'};
    return 0 if $e1->{'dist'} > $e2->{'dist'};
    return 1 if $e1->{'packed'} > $e2->{'packed'};
    return 0 if $e1->{'packed'} < $e2->{'packed'};
    return 0;
}

sub dragonfly_is_better_element ($q, $first, $second) {
    my $e1 = $q->{'n'}[$first];
    my $e2 = $q->{'n'}[$second];
    return 1 if is_better_dragonfly_score($e1, $e2);
    return 0 if is_better_dragonfly_score($e2, $e1);
    return 1 if $first < $second;
    return 0;
}

sub dragonfly_heapify ($q, $i) {
    return if $q->{'heap_size'} == 0;
    my $elements = $q->{'elements'};
    my $l        = ($i * 2 + 1);
    my $r        = ($i * 2 + 2);
    my $largest  = $i;
    if ($l < $q->{'heap_size'}) {
        $largest = $l
            if dragonfly_is_better_element($q, $elements->[$l], $elements->[$i]);
    }
    if ($r < $q->{'heap_size'}) {
        $largest = $r
            if dragonfly_is_better_element($q, $elements->[$r], $elements->[$largest]);
    }
    if ($largest != $i) {
        @$elements[$i, $largest] = @$elements[$largest, $i];
        dragonfly_heapify($q, $largest);
    }
    return;
} ## end sub dragonfly_heapify

sub dragonfly_extarct_max ($q) {
    return -1 if $q->{'heap_size'} == 0;
    my $res = $q->{'elements'}[0];
    $q->{'elements'}[0] = $q->{'elements'}[$q->{'heap_size'} - 1];
    $q->{'heap_size'}--;
    dragonfly_heapify($q, 0);
    return $res;
}

sub dragonfly_heap_insert ($q, $val) {
    $q->{'heap_size'}++;
    my $i = $q->{'heap_size'} - 1;
    while ($i > 0
        and dragonfly_is_better_element($q, $val, $q->{'elements'}[int(($i - 1) / 2)]))
    {
        $q->{'elements'}[$i] = $q->{'elements'}[int(($i - 1) / 2)];
        $i = int(($i - 1) / 2);
    }
    $q->{'elements'}[$i] = $val;
    return;
}

sub init_pack_requets ($h) {
    $h->{'request'}{'pack_requests'} //= [];
    $h->{'request'}{'pack_requests_num'} = 0;
    $h->{'request'}{'pack_requests_pos'} = 0;
    $h->{'request'}{'pack_index_of'}     = {};
    return;
}

sub init_requests ($h) {
    $h->{'request'}{'requests'} //= [];
    $h->{'request'}{'requests_num'} = 0;
    $h->{'request'}{'requests_pos'} = 0;
    $h->{'request'}{'index_of'}     = {};
    return;
}

sub set_pack_request_from_score ($p, $s) {
    $p->{'boxes_in_level'}   = $s->{'boxes_in_level'};
    $p->{'boxes_on_targets'} = $s->{'boxes_on_targets'};
    $p->{'connectivity'}     = $s->{'connectivity'};
    $p->{'rooms_score'}      = $s->{'rooms_score'};
    return;
}

sub set_request_from_score ($p, $s) {
    $p->{'packed_boxes'} = $s->{'packed_boxes'};
    $p->{'connectivity'} = $s->{'connectivity'};
    $p->{'out_of_plan'}  = $s->{'out_of_plan'};
    $p->{'imagine'}      = $s->{'imagine'};
    return;
}

sub add_pack_request ($s, $h) {
    my $r = $h->{'request'};
    my $i = (
        $h->{'request'}{'pack_index_of'}{ join ',', $s->{'boxes_in_level'}, $s->{'boxes_on_targets'}, $s->{'connectivity'},
            $s->{'rooms_score'} } // -1);
    return if $i != -1;
    $r->{'pack_requests'}[$r->{'pack_requests_num'}] //= {};
    set_pack_request_from_score($r->{'pack_requests'}[$r->{'pack_requests_num'}], $s);
    $r->{'pack_index_of'}
        { join(',', $s->{'boxes_in_level'}, $s->{'boxes_on_targets'}, $s->{'connectivity'}, $s->{'rooms_score'}) } =
        $r->{'pack_requests_num'};
    $r->{'pack_requests_pos'} = $r->{'pack_requests_num'};
    $r->{'pack_requests_num'}++;
    return;
} ## end sub add_pack_request

sub add_request ($s, $h) {
    my $r = $h->{'request'};
    my $i =
        ($h->{'request'}{'index_of'}{ join ',', $s->{'packed_boxes'}, $s->{'connectivity'}, $s->{'out_of_plan'}, $s->{'imagine'} }
            // -1);
    return if $i != -1;
    $r->{'requests'}[$r->{'requests_num'}] //= {};
    set_request_from_score($r->{'requests'}[$r->{'requests_num'}], $s);
    $r->{'index_of'}{ join(',', $s->{'packed_boxes'}, $s->{'connectivity'}, $s->{'out_of_plan'}, $s->{'imagine'}) } =
        $r->{'requests_num'};
    $r->{'requests_pos'} = $r->{'requests_num'};
    $r->{'requests_num'}++;
    return;
}

sub get_next_pack_request ($p, $h) {
    my $r = $h->{'request'};
    %$p = %{ $r->{'pack_requests'}[$r->{'pack_requests_pos'}] };
    $r->{'pack_requests_pos'}++;
    $r->{'pack_requests_pos'} = 0
        if $r->{'pack_requests_pos'} == $r->{'pack_requests_num'};
    return;
}

sub get_next_request ($p, $h) {
    my $r = $h->{'request'};
    %$p = %{ $r->{'requests'}[$r->{'requests_pos'}] };
    $r->{'requests_pos'}++;
    $r->{'requests_pos'} = 0 if $r->{'requests_pos'} == $r->{'requests_num'};
    return;
}

sub get_pack_request_of_score ($p, $s, $h) {
    my $r = $h->{'request'};
    my $i = (
        $h->{'request'}{'pack_index_of'}{ join ',', $s->{'boxes_in_level'}, $s->{'boxes_on_targets'}, $s->{'connectivity'},
            $s->{'rooms_score'} } // -1);
    Carp::confess("can't find pack request") if $i == -1;
    %$p = %{ $r->{'pack_requests'}[$i] };
    return;
}

sub get_request_of_score ($p, $s, $h) {
    my $r = $h->{'request'};
    my $i =
        ($h->{'request'}{'index_of'}{ join ',', $s->{'packed_boxes'}, $s->{'connectivity'}, $s->{'out_of_plan'}, $s->{'imagine'} }
            // -1);
    Carp::confess("can't find request") if $i == -1;
    %$p = %{ $r->{'requests'}[$i] };
    return;
}

sub set_next_pack_request_to_score ($s, $h) {
    my $r = $h->{'request'};
    my $i = (
        $h->{'request'}{'pack_index_of'}{ join ',', $s->{'boxes_in_level'}, $s->{'boxes_on_targets'}, $s->{'connectivity'},
            $s->{'rooms_score'} } // -1);
    Carp::confess("can't find pack request") if $i == -1;
    $r->{'pack_requests_pos'} = $i;
    return;
}

sub set_next_request_to_score ($s, $h) {
    my $r = $h->{'request'};
    my $i =
        ($h->{'request'}{'index_of'}{ join ',', $s->{'packed_boxes'}, $s->{'connectivity'}, $s->{'out_of_plan'}, $s->{'imagine'} }
            // -1);
    Carp::confess("can't find request") if $i == -1;
    $r->{'requests_pos'} = $i;
    return;
}

sub get_label_of_score ($s, $pull_mode, $h) {
    return $pull_mode == 0
        ? (
            $h->{'request'}{'index_of'}{ join ',', $s->{'packed_boxes'}, $s->{'connectivity'}, $s->{'out_of_plan'},
                $s->{'imagine'} } // -1)
        : (
            $h->{'request'}{'pack_index_of'}{ join ',', $s->{'boxes_in_level'}, $s->{'boxes_on_targets'}, $s->{'connectivity'},
                $s->{'rooms_score'} } // -1);
}

sub get_label_of_request ($p, $h) {
    my $s = {
        'packed_boxes' => $p->{'packed_boxes'},
        'connectivity' => $p->{'connectivity'},
        'out_of_plan'  => $p->{'out_of_plan'},
        'imagine'      => $p->{'imagine'},
    };
    return get_label_of_score($s, 0, $h);
}

sub get_label_of_pack_request ($p, $h) {
    my $s = {
        'boxes_in_level'   => $p->{'boxes_in_level'},
        'boxes_on_targets' => $p->{'boxes_on_targets'},
        'connectivity'     => $p->{'connectivity'},
        'rooms_score'      => $p->{'rooms_score'},
    };
    return get_label_of_score($s, 1, $h);
}

sub bfs_from_place ($brd, $dist, $start_p, $ignore_boxes) {
    my $occupied_mask = $ignore_boxes ? WALL : OCCUPIED;
    my @current       = ($start_p);
    $dist->[$start_p] = 0;
    my $d = 0;
    while (@current) {
        my @next;
        for my $p (@current) {
            for my $delta (@Delta_p) {
                my $np = $p + $delta;
                next unless ((vec($brd, $np, 8) & $occupied_mask) == 0 and $dist->[$np] == 1000000);
                $dist->[$np] = $d + 1;
                push @next, $np;
            }
        }
        $d++;
        @current = @next;
    }
    return;
} ## end sub bfs_from_place

sub get_connectivity ($brd) {
    my $free = ($brd&.$OCC_ONLY) =~ tr/\x00\x01\x02\x03/\xFF\x00\x00\x00/r;
    my $todo = $free&.$INNER_ONLY;
    my $c    = 0;
    while ($todo =~ /[^\0]/g) {
        my $cloud = $ZERO_BOARD;
        vec($cloud, $-[0], 8) = 0xFF;
        $todo&.=~. flood_mask($free, $cloud);
        $c++;
    }
    return $c;
}

sub mark_connectivities ($brd, $dist) {
    my @local_dist;
    my $c = 0;
    @{$dist} = (1000000) x $Ncells;
    for my $p (0 .. $Ncells - 1) {
        next if vec($Inner, $p, 8) == 0;
        next if $dist->[$p] != 1000000;
        next if vec($brd, $p, 8) & OCCUPIED;
        @{ (\@local_dist) } = (1000000) x $Ncells;
        bfs_from_place($brd, \@local_dist, $p, 0);
        for my $q (0 .. $Ncells - 1) {
            $dist->[$q] = $c if $local_dist[$q] < 1000000;
        }
        $c++;
    }
    return $c;
} ## end sub mark_connectivities

sub zones_around_place ($brd, $start_p) {
    my @z = (1000000) x 4;
    my $free;
    for my $c (0 .. 3) {
        my $p = $start_p + $Delta_p[$c];
        next if vec($Inner, $p, 8) == 0;
        next if $z[$c] != 1000000;
        next if vec($brd, $p, 8) & OCCUPIED;
        $free //= ($brd&.$OCC_ONLY) =~ tr/\x00\x01\x02\x03/\xFF\x00\x00\x00/r;
        my $cloud = $ZERO_BOARD;
        vec($cloud, $p, 8) = 0xFF;
        $cloud = flood_mask($free, $cloud);

        for my $j (0 .. 3) {
            $z[$j] = $c if vec($cloud, $start_p + $Delta_p[$j], 8);
        }
    }
    return @z;
} ## end sub zones_around_place

sub get_srcs_of_all_targets ($b_in) {
    my @queue;
    my $queue_place = 0;
    my ($brd, $srcs);
    $srcs = $ZERO_BOARD;
    $brd  = $b_in&.$NOT_BOX;
    for my $p (0 .. $Ncells - 1) {
        next if vec($Inner, $p, 8) == 0;
        next if (vec($brd, $p, 8) & TARGET) == 0;
        push @queue, $p;
        vec($srcs, $p, 8) = 1;
    }
    while ($queue_place < @queue) {
        my $p = $queue[$queue_place++];
        for my $delta (@Delta_p) {
            my $bp = $p + $delta;
            next if vec($brd,  $bp,          8) & OCCUPIED;
            next if vec($brd,  $bp + $delta, 8) & OCCUPIED;
            next if vec($srcs, $bp,          8);
            vec($srcs, $bp, 8) = 1;
            push @queue, $bp;
        }
    }
    return $srcs;
} ## end sub get_srcs_of_all_targets

sub expand_group ($brd, $group, $dist) {
    my @current;
    for my $p (0 .. $Ncells - 1) {
        $dist->[$p] = 1000000;
        next unless (vec($group, $p, 8));
        push @current, $p;
        $dist->[$p] = 0;
    }
    while (@current) {
        my @next;
        for my $p (@current) {
            for my $delta (@Delta_p) {
                my $np = $p + $delta;
                next if vec($group, $np, 8);
                next if vec($brd,   $np, 8) & OCCUPIED;
                vec($group, $np, 8) = 1;
                push @next, $np;
                $dist->[$np] = $dist->[$p] + 1;
            }
        }
        @current = @next;
    }
    return $group;
} ## end sub expand_group

sub biconnect_dfs ($brd, $p, $father, $d, $vr, $low, $cr) {
    vec($$vr, $p, 8) = 1;
    $low->[$p] = $d;
    for my $i (0 .. 3) {
        my $np = $p + $Delta_p[$i];
        next if vec($brd, $np, 8) & OCCUPIED;
        next if vec($$vr, $np, 8);
        biconnect_dfs($brd, $np, ($i + 2) & 3, $d + 1, $vr, $low, $cr);
    }
    for my $i (0 .. 3) {
        next if $i == $father;
        my $np = $p + $Delta_p[$i];
        $low->[$p] = $low->[$np] if $low->[$np] < $low->[$p];
        vec($$cr, $np, 8) = 1 if $low->[$np] < $d;
    }
    vec($$cr, $p, 8) = 1 if $low->[$p] < $d;
    return;
} ## end sub biconnect_dfs

sub biconnect_score ($b_in, $report) {
    my ($brd, $visited, $on_cycle);
    $brd      = $b_in;
    $visited  = $ZERO_BOARD;
    $on_cycle = $ZERO_BOARD;
    my @low = (1000000) x $Ncells;
    for my $p (0 .. $Ncells - 1) {
        next if vec($Inner,   $p, 8) == 0;
        next if vec($visited, $p, 8);
        next if vec($brd,     $p, 8) & OCCUPIED;
        biconnect_dfs($brd, $p, -1, 0, \$visited, \@low, \$on_cycle);
    }
    for my $p (0 .. $Ncells - 1) {
        vec($on_cycle, $p, 8) = 1
            if (vec($brd, $p, 8) & TARGET)
            and (vec($brd, $p, 8) & BOX) == 0;
    }
    return $Index_num - $Global_boxes_in_level - unpack('%32C*', $on_cycle);
} ## end sub biconnect_score

sub mark_diags ($brd) {
    my $enclosed;
    my ($diag_right, $diag_left);
    $enclosed   = $ZERO_BOARD;
    $diag_right = $ZERO_BOARD;
    $diag_left  = $ZERO_BOARD;
    for my $i (1 .. $Height - 2) {
        for my $j (1 .. $Width - 2) {
            my $p = $i * $Width + $j;
            next if vec($brd, $p, 8) & OCCUPIED;
            next if vec($brd, $p, 8) & SOKOBAN;
            next if (vec($brd, $p - $Width, 8) & OCCUPIED) == 0;
            next if (vec($brd, $p + $Width, 8) & OCCUPIED) == 0;
            next if (vec($brd, $p + 1,      8) & OCCUPIED) == 0;
            next if (vec($brd, $p - 1,      8) & OCCUPIED) == 0;
            vec($enclosed, $p, 8) = 1;
        }
    }
    for my $i (1 .. $Height - 2) {
        for my $j (1 .. $Width - 2) {
            my $p = $i * $Width + $j;
            next if vec($enclosed, $p, 8) == 0;
            my $diag_start = 0;
            $diag_start = 1 if vec($brd, $p - $Width - 1, 8) & OCCUPIED;
            $diag_start = 1
                if vec($brd, $p - $Width, 8) == WALL and vec($brd, $p - 1, 8) == WALL;
            next if $diag_start == 0;
            my $k = 1;
            $k++ while vec($enclosed, ($i + $k) * $Width + $j + $k, 8);
            my $diag_end = 0;
            my $ep       = ($i + $k) * $Width + $j + $k;
            $diag_end = 1 if vec($brd, $ep, 8) & OCCUPIED;
            $diag_end = 1
                if vec($brd, $ep - $Width, 8) == WALL and vec($brd, $ep - 1, 8) == WALL;
            next if $diag_end == 0;
            vec($diag_right, $p, 8) = $k;
        } ## end for my $j (1 .. $Width ...)
    } ## end for my $i (1 .. $Height...)
    for my $i (1 .. $Height - 2) {
        for my $j (1 .. $Width - 2) {
            my $p = $i * $Width + $j;
            next if vec($enclosed, $p, 8) == 0;
            my $diag_start = 0;
            $diag_start = 1 if vec($brd, $p - $Width + 1, 8) & OCCUPIED;
            $diag_start = 1
                if vec($brd, $p - $Width, 8) == WALL and vec($brd, $p + 1, 8) == WALL;
            next if $diag_start == 0;
            my $k = 1;
            $k++ while vec($enclosed, ($i + $k) * $Width + $j - $k, 8);
            my $diag_end = 0;
            my $ep       = ($i + $k) * $Width + $j - $k;
            $diag_end = 1 if vec($brd, $ep, 8) & OCCUPIED;
            $diag_end = 1
                if vec($brd, $ep - $Width, 8) == WALL and vec($brd, $ep + 1, 8) == WALL;
            next if $diag_end == 0;
            vec($diag_left, $p, 8) = $k;
        } ## end for my $j (1 .. $Width ...)
    } ## end for my $i (1 .. $Height...)
    return ($diag_right, $diag_left);
} ## end sub mark_diags

sub wallify_diag_void ($brd, $p, $k, $diag_right) {
    if ($diag_right) {
        for my $n (0 .. $k - 1) {
            vec($brd, $p + $n * ($Width + 1) - 1, 8) = WALL;
            vec($brd, $p + $n * ($Width + 1) + 1, 8) = WALL;
        }
        vec($brd, $p - $Width - 1, 8) = WALL
            if vec($brd, $p - $Width - 1, 8) & OCCUPIED;
        vec($brd, $p - $Width,            8) = WALL;
        vec($brd, $p + $k * ($Width + 1), 8) = WALL
            if vec($brd, $p + $k * ($Width + 1), 8) & OCCUPIED;
        vec($brd, $p + $k * ($Width + 1) - 1, 8) = WALL;
    }
    else {
        for my $n (0 .. $k - 1) {
            vec($brd, $p + $n * ($Width - 1) - 1, 8) = WALL;
            vec($brd, $p + $n * ($Width - 1) + 1, 8) = WALL;
        }
        vec($brd, $p - $Width + 1, 8) = WALL
            if vec($brd, $p - $Width + 1, 8) & OCCUPIED;
        vec($brd, $p - $Width,            8) = WALL;
        vec($brd, $p + $k * ($Width - 1), 8) = WALL
            if vec($brd, $p + $k * ($Width - 1), 8) & OCCUPIED;
        vec($brd, $p + $k * ($Width - 1) + 1, 8) = WALL;
    }
    return $brd;
} ## end sub wallify_diag_void

sub diag_has_no_targets ($brd, $p, $n, $diag_right) {
    my $step = $Width + ($diag_right ? 1 : -1);
    for my $k (0 .. $n - 1) {
        return 0 if vec($brd, $p + $k * $step, 8) & TARGET;
    }
    return 1;
}

sub diag_deadlock ($brd, $start_p, $n, $delta) {
    my $good = 1;
    my $p;
    $good = 0
        if vec($brd, $start_p - $Width - $delta, 8) == BOX;
    for my $i (0 .. $n) {
        $p = $start_p + $i * ($Width + $delta);
        my $element1 = vec($brd, $p - $Width, 8);
        my $element2 = vec($brd, $p - $delta, 8);
        if ($element1 == BOX or $element2 == BOX or $good == 0) {
            return 1 if $i == $n;
            $good = (vec($brd, $p, 8) & TARGET) ? 1 : 0;
            next;
        }
        last     if $i == $n;
        return 0 if vec($brd, $p, 8) & TARGET;
    }
    return 1 if vec($brd, $p, 8) == BOX;
    return 0;
} ## end sub diag_deadlock

sub is_diag_deadlock ($brd) {
    my ($diag_right, $diag_left);
    ($diag_right, $diag_left) = mark_diags($brd);
    for my $p (0 .. $Ncells - 1) {
        my $n = vec($diag_right, $p, 8);
        if ($n != 0) {
            return 1 if diag_deadlock($brd, $p, $n, 1);
        }
        $n = vec($diag_left, $p, 8);
        next unless ($n != 0);
        return 1 if diag_deadlock($brd, $p, $n, -1);
    }
    return 0;
}

sub reset_helper ($h) {
    $h->{'parking_order_num'}        = 0;
    $h->{'full_parking_order_num'}   = 0;
    $h->{'sol_len'}                  = 0;
    $h->{'perimeter_found'}          = 0;
    $h->{'enable_inefficient_moves'} = 0;
    $h->{'level_solved'}             = 0;
    $h->{'weighted_search'}          = 1;
    $h->{'used_in_plan'}             = '';
    $h->{'imagined_hf_board'}        = '';
    $h->{'wallified'}                = '';
    return;
}

sub init_helper () {
    my $h = {
        'oop'                  => undef,
        'imagine'              => undef,
        'request'              => undef,
        'parking_order'        => [],
        'boxes_were_removed'   => 0,
        'full_parking_order'   => [],
        'scored_distance'      => [],
        'imagined_hf_board'    => '',
        'wallified'            => '',
        'sol_move'             => [],
        'tested_deadlock_room' => 0,
        'k_dist_value'         => 0,
        'alg_type'             => 0,
        'my_core'              => 0,
    };
    reset_helper($h);
    return $h;
} ## end sub init_helper

sub turn_target_holes_into_walls ($brd) {
    for my $p (0 .. $Ncells - 1) {
        vec($brd, $p, 8) = WALL if vec($Target_holes, $p, 8);
    }
    return $brd;
}

sub overlap_score ($brd, $h) {
    my $overlap_board;
    my $score              = 0;
    my $best_overlap_score = -1;
    return 0 if $h->{'boxes_were_removed'};
    return 0 if $h->{'full_parking_order_num'} == 0;
    $overlap_board = $ZERO_BOARD;
    for my $i (0 .. $h->{'full_parking_order_num'} - 1) {
        my $to_p = $Index_to_p[$h->{'full_parking_order'}[$i]{'to'}];
        vec($overlap_board, $to_p, 8) = 1;
        $score++ if vec($brd, $to_p, 8) & BOX;
        if ($h->{'full_parking_order'}[$i]{'from'} >= 0) {
            my $from_p = $Index_to_p[$h->{'full_parking_order'}[$i]{'from'}];
            vec($overlap_board, $from_p, 8) = 0;
            $score-- if vec($brd, $from_p, 8) & BOX;
        }
        $best_overlap_score = $score if $score >= $best_overlap_score;
    }
    return $best_overlap_score;
} ## end sub overlap_score

sub _dz_masks () {
    if ($DZ_len != $Ncells) {
        $NOT_DZ  = chr(0xFF ^ DEADLOCK_ZONE) x $Ncells;
        $DZ_ONLY = chr(DEADLOCK_ZONE) x $Ncells;
        $DZ_len  = $Ncells;
    }
    return;
}

sub work_left_in_deadlock_zone ($brd) {
    for my $p (0 .. $Ncells - 1) {
        my $c = vec($brd, $p, 8);
        next     if ($c & DEADLOCK_ZONE) == 0;
        next     if $c & SOKOBAN;
        return 1 if ($c & BOX)    and ($c & TARGET) == 0;
        return 1 if ($c & TARGET) and ($c & BOX) == 0;
    }
    return 0;
}

sub work_left_outside_deadlock_zone ($brd) {
    for my $p (0 .. $Ncells - 1) {
        next if vec($brd, $p, 8) & DEADLOCK_ZONE;
        if (vec($brd, $p, 8) & BOX) {
            return 1 if (vec($Initial_board, $p, 8) & BOX) == 0;
        }
        next unless (vec($Initial_board, $p, 8) & BOX);
        return 1 if (vec($brd, $p, 8) & BOX) == 0;
    }
    return 0;
}

sub get_sokoban_cloud_as_group ($brd) {
    state $sok_only = '';
    $sok_only = chr(SOKOBAN) x $Ncells if length($sok_only) != $Ncells;
    (my $g = $brd&.$sok_only) =~ tr/\x08/\x01/;
    return $g;
}

sub can_be_pushed_sideways ($brd, $p, $d) {
    $d = ($d + 1) & 3;
    if ((vec($brd, $p + $Delta_p[$d], 8) & OCCUPIED) == 0) {
        if ((vec($brd, $p + 2 * $Delta_p[$d], 8) & OCCUPIED) == 0) {
            return 1 if (vec($brd, $p - $Delta_p[$d], 8) & OCCUPIED) == 0;
        }
    }
    $d = ($d + 2) & 3;
    if ((vec($brd, $p + $Delta_p[$d], 8) & OCCUPIED) == 0) {
        if ((vec($brd, $p + 2 * $Delta_p[$d], 8) & OCCUPIED) == 0) {
            return 1 if (vec($brd, $p - $Delta_p[$d], 8) & OCCUPIED) == 0;
        }
    }
    return 0;
} ## end sub can_be_pushed_sideways

sub update_deadlock_zone_from_group_push_mode ($brd, $group) {
    my $prev_deadlock_zone;
    _dz_masks();
    ($prev_deadlock_zone = $brd&.$DZ_ONLY) =~ tr/\x20/\x01/;
    _dz_masks();
    $brd&.=$NOT_DZ;
    for my $p (0 .. $Ncells - 1) {
        next if vec($Inner, $p, 8) == 0;
        next if vec($group, $p, 8) == 0;
        vec($brd, $p, 8) |= DEADLOCK_ZONE;
        for my $k (0 .. 7) {
            vec($brd, $p + $Delta_p_8[$k], 8) |= DEADLOCK_ZONE
                if vec($brd, $p + $Delta_p_8[$k], 8) != WALL;
        }
        for my $k (0 .. 3) {
            next unless (vec($brd, $p + $Delta_p[$k], 8) & BOX);
            if (vec($brd, $p + 2 * $Delta_p[$k], 8) & BOX) {
                vec($brd, $p + 2 * $Delta_p[$k], 8) |= DEADLOCK_ZONE
                    if can_be_pushed_sideways($brd, $p + 2 * $Delta_p[$k], $k) == 0;
            }
        }
    } ## end for my $p (0 .. $Ncells...)
    for my $p (0 .. $Ncells - 1) {
        vec($brd, $p, 8) &= 0xFF ^ DEADLOCK_ZONE
            if vec($prev_deadlock_zone, $p, 8) == 0;
    }
    return $brd;
} ## end sub update_deadlock_zone_from_group_push_mode

sub add_islands ($brd) {
    my $dz;
    _dz_masks();
    ($dz = $brd&.$DZ_ONLY) =~ tr/\x20/\x01/;
    for my $p (0 .. $Ncells - 1) {
        next if vec($Inner, $p, 8) == 0;
        next if vec($brd,   $p, 8) & OCCUPIED;
        next if vec($dz,    $p, 8);
        next unless grep {vec($dz, $p + $_, 8)} @Delta_p;
        next unless (not grep {(vec($brd, $p + $_, 8) & OCCUPIED) == 0} @Delta_p);
        vec($brd, $p, 8) |= DEADLOCK_ZONE;
        for my $k (0 .. 7) {
            vec($brd, $p + $Delta_p_8[$k], 8) |= DEADLOCK_ZONE
                if vec($brd, $p + $Delta_p_8[$k], 8) & BOX;
        }
    }
    return $brd;
} ## end sub add_islands

sub init_deadlock_zone_from_group ($brd, $group, $pull_mode) {
    if ($pull_mode) {
        _dz_masks();
        $brd&.=$NOT_DZ;
        for my $p (0 .. $Ncells - 1) {
            next if vec($group, $p, 8) == 0;
            vec($brd, $p, 8) |= DEADLOCK_ZONE;
            for my $k (0 .. 7) {
                vec($brd, $p + $Delta_p_8[$k], 8) |= DEADLOCK_ZONE
                    if vec($brd, $p + $Delta_p_8[$k], 8) & BOX;
            }
        }
        $brd = add_islands($brd);
        return $brd;
    }
    for my $p (0 .. $Ncells - 1) {
        vec($brd, $p, 8) |= DEADLOCK_ZONE;
    }
    $brd = update_deadlock_zone_from_group_push_mode($brd, $group);
    return $brd;
} ## end sub init_deadlock_zone_from_group

sub set_deadlock_zone_in_pull_mode ($brd) {
    my $g;
    $g   = get_sokoban_cloud_as_group($brd);
    $brd = init_deadlock_zone_from_group($brd, $g, 1);
    return $brd;
}

sub update_deadlock_zone_push_mode ($brd) {
    my $unreachable;
    $unreachable = $ZERO_BOARD;
    for my $p (0 .. $Ncells - 1) {
        next if vec($brd,   $p, 8) & SOKOBAN;
        next if vec($Inner, $p, 8) == 0;
        next if vec($brd,   $p, 8) & OCCUPIED;
        next if (vec($brd, $p, 8) & DEADLOCK_ZONE) == 0;
        vec($unreachable, $p, 8) = 1;
    }
    $brd = update_deadlock_zone_from_group_push_mode($brd, $unreachable);
    return $brd;
}

sub clear_frozen_boxes_away_from_deadlock_zone ($brd) {
    my $has_frozen = 0;
    for my $p (0 .. $Ncells - 1) {
        next if vec($Inner, $p, 8) == 0;
        $has_frozen = 1
            if vec($brd, $p, 8) == WALL
            and vec($Initial_board, $p, 8) != WALL;
    }
    return $brd if $has_frozen == 0;
    for my $p (0 .. $Ncells - 1) {
        next if vec($Inner, $p, 8) == 0;
        next
            unless (vec($brd, $p, 8) == WALL
                and vec($Initial_board, $p, 8) != WALL
                and ((grep {vec(($brd), $p + $_, 8) & DEADLOCK_ZONE} @Delta_p_8) ? 1 : 0) == 0);
        vec($brd, $p, 8) = vec($Initial_board, $p, 8) & TARGET;
    }
    $brd = expand_sokoban_cloud($brd);
    return $brd;
} ## end sub clear_frozen_boxes_away_from_deadlock_zone

sub clear_boxes_out_of_deadlock_zone ($brd) {
    for my $p (0 .. $Ncells - 1) {
        vec($brd, $p, 8) &= 0xFF ^ BOX
            if (vec($brd, $p, 8) & DEADLOCK_ZONE) == 0;
    }
    $brd = expand_sokoban_cloud($brd);
    return $brd;
}

sub exited_deadlock_zone ($brd) {
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($brd, $p, 8) & SOKOBAN);
        return 1 if (vec($brd, $p, 8) & DEADLOCK_ZONE) == 0;
    }
    return 0;
}

sub update_deadlock_zone ($brd, $pull_mode) {
    if   ($pull_mode) {$brd = set_deadlock_zone_in_pull_mode($brd);}
    else              {$brd = update_deadlock_zone_push_mode($brd);}
    $brd = clear_boxes_out_of_deadlock_zone($brd);
    return $brd;
}

sub size_of_deadlock_zone ($brd) {
    _dz_masks();
    my $t = $brd&.$DZ_ONLY;
    return $t =~ tr/\x00//c;
}

sub wallify_boxes_using_pattern ($brd, $pat_num) {
    for my $p (0 .. $Ncells - 1) {
        vec($brd, $p, 8) = WALL
            if vec($New_envelope_patterns[$pat_num], $p, 8) & BOX;
    }
    return $brd;
}

sub matches_envelope_pattern ($brd, $n) {
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($New_envelope_patterns[$n], $p, 8) & BOX);
        return 0 if (vec($brd, $p, 8) & OCCUPIED) == 0;
    }
    for my $p (0 .. $Ncells - 1) {
        next unless ((vec($New_envelope_patterns[$n], $p, 8) & SOKOBAN) == 0);
        return 0 if vec($brd, $p, 8) & SOKOBAN;
    }
    return 1;
}

sub fix_boxes_using_envelopes ($brd) {
    for my $i (0 .. $#New_envelope_patterns) {
        next if matches_envelope_pattern($brd, $i) == 0;
        $brd = wallify_boxes_using_pattern($brd, $i);
    }
    return $brd;
}

sub turn_2x2_to_walls ($brd) {
    my $changed = 0;
    for my $i (0 .. $Height - 2) {
        for my $j (0 .. $Width - 2) {
            my $sum = 0;
            for my $y (0 .. 1) {
                for my $x (0 .. 1) {
                    $sum++
                        if vec($brd, ($i + $y) * $Width + $j + $x, 8) & OCCUPIED;
                }
            }
            next unless ($sum == 4);
            for my $y (0 .. 1) {
                for my $x (0 .. 1) {
                    my $p = ($i + $y) * $Width + $j + $x;
                    $changed = 1 if vec($brd, $p, 8) & BOX;
                    vec($brd, $p, 8) = WALL;
                }
            }
        } ## end for my $j (0 .. $Width ...)
    } ## end for my $i (0 .. $Height...)
    return ($changed, $brd);
} ## end sub turn_2x2_to_walls

sub close_holes ($brd) {
    for my $i (1 .. $Height - 2) {
        for my $j (1 .. $Width - 2) {
            my $p = $i * $Width + $j;
            if (vec($brd, $p, 8) == SPACE) {
                for my $k (0 .. 3) {
                    next
                        if vec($brd, ($i + $Delta_y[($k + 1) & 3]) * $Width + $j + $Delta_x[($k + 1) & 3], 8) != WALL;
                    next
                        if vec($brd, ($i + $Delta_y[($k + 2) & 3]) * $Width + $j + $Delta_x[($k + 2) & 3], 8) != WALL;
                    next
                        if vec($brd, ($i + $Delta_y[($k + 3) & 3]) * $Width + $j + $Delta_x[($k + 3) & 3], 8) != WALL;
                    vec($brd, $p, 8) = WALL;
                    return (1, $brd);
                }
            }
            next unless (vec($brd, $p, 8) == SOKOBAN);
            for my $k (0 .. 3) {
                next
                    if (vec($brd, ($i + $Delta_y[$k]) * $Width + $j + $Delta_x[$k], 8) & SOKOBAN) == 0;
                next
                    if vec($brd, ($i + $Delta_y[($k + 1) & 3]) * $Width + $j + $Delta_x[($k + 1) & 3], 8) != WALL;
                next
                    if vec($brd, ($i + $Delta_y[($k + 2) & 3]) * $Width + $j + $Delta_x[($k + 2) & 3], 8) != WALL;
                next
                    if vec($brd, ($i + $Delta_y[($k + 3) & 3]) * $Width + $j + $Delta_x[($k + 3) & 3], 8) != WALL;
                vec($brd, $p, 8) = WALL;
                return (1, $brd);
            }
        } ## end for my $j (1 .. $Width ...)
    } ## end for my $i (1 .. $Height...)
    return (0, $brd);
} ## end sub close_holes

sub fix_crystaline ($b_in) {
    my $brd;
    my $fixed_box = 0;
    $brd = $b_in;
    $brd&.=$NOT_SOKOBAN;
    $brd = go_to_final_position_with_given_walls($brd);
    my $removed_box;
    do {
        $removed_box = 0;
        for my $p (0 .. $Ncells - 1) {
            next if vec($brd, $p, 8) != PACKED_BOX;
            for my $k (0 .. 3) {
                next
                    if vec($brd, $p + $Delta_p[$k], 8) & OCCUPIED;
                next
                    if vec($brd, $p + 2 * $Delta_p[$k], 8) & OCCUPIED;
                vec($brd, $p, 8) &= 0xFF ^ BOX;
                $removed_box = 1;
                last;
            }
        }
    } while ($removed_box);
    for my $p (0 .. $Ncells - 1) {
        $fixed_box = 1
            if (vec($brd, $p, 8) & BOX)
            and (vec($b_in, $p, 8) & BOX);
    }
    if ($fixed_box) {
        for my $p (0 .. $Ncells - 1) {
            vec($b_in, $p, 8) = WALL
                if (vec($brd, $p, 8) & BOX)
                and (vec($b_in, $p, 8) & BOX);
        }
    }
    return ($fixed_box, $b_in);
} ## end sub fix_crystaline

sub fix_diagonals ($w) {
    my ($diag_right, $diag_left);
    my $changed = 0;
    ($diag_right, $diag_left) = mark_diags($w);
    for my $p (0 .. $Ncells - 1) {
        if (vec($diag_right, $p, 8)) {
            if (diag_has_no_targets($w, $p, vec($diag_right, $p, 8), 1)) {
                my $backup = $w;
                $w = wallify_diag_void($w, $p, vec($diag_right, $p, 8), 1);
                $changed |= ($w eq $backup ? 0 : 1);
            }
        }
        next unless (vec($diag_left, $p, 8));
        if (diag_has_no_targets($w, $p, vec($diag_left, $p, 8), 0)) {
            my $backup = $w;
            $w = wallify_diag_void($w, $p, vec($diag_left, $p, 8), 0);
            $changed |= ($w eq $backup ? 0 : 1);
        }
    } ## end for my $p (0 .. $Ncells...)
    return ($changed, $w);
} ## end sub fix_diagonals

sub is_box_2x2_frozen_at_index ($b_in, $index) {
    my $p = $Index_to_p[$index];
    Carp::confess('missing box') if (vec($b_in, $p, 8) & BOX) == 0;
    for my $a ($p - $Width - 1, $p - $Width, $p - 1, $p) {
        return 1
            if (vec($b_in, $a, 8) & OCCUPIED)
            and (vec($b_in, $a + 1,          8) & OCCUPIED)
            and (vec($b_in, $a + $Width,     8) & OCCUPIED)
            and (vec($b_in, $a + $Width + 1, 8) & OCCUPIED);
    }
    return 0;
}

sub is_box_2x2_frozen_after_move ($brd, $m) {
    my $from_p = $Index_to_p[$m->{'from'}];
    my $to_p   = $Index_to_p[$m->{'to'}];
    Carp::confess('missing box')
        if (vec($brd, $from_p, 8) & BOX) == 0;
    vec($brd, $from_p, 8) &= 0xFF ^ BOX;
    vec($brd, $to_p, 8) |= BOX;
    my $res = is_box_2x2_frozen_at_index($brd, $m->{'to'});
    vec($brd, $to_p, 8) &= 0xFF ^ BOX;
    vec($brd, $from_p, 8) |= BOX;
    return $res;
}

sub allocate_graph () {
    my $n = $Index_num * 4;
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
    @$active = (0) x $gd->{'vertices_num'};
    for my $i (0 .. $Index_num - 1) {
        my $base_p = $Index_to_p[$i];
        my $p      = $base_p;
        next if vec($brd, $p, 8) & WALL;
        for my $j (0 .. 3) {
            $active->[$i * 4 + $j] = 1
                if (vec($brd, $p + $Delta_p[$j], 8) & WALL) == 0;
        }
    }
    return;
}

sub make_holes_inactive ($brd, $gd) {
    my $active = $gd->{'active'};
    for my $p (0 .. $Ncells - 1) {
        next if vec($Inner, $p, 8) == 0;
        next if vec($brd,   $p, 8) & OCCUPIED;
        my $sum = grep {vec($brd, $p + $_, 8) == WALL} @Delta_p;
        next if $sum != 3;
        for my $i (0 .. 3) {
            my $bp = $p + $Delta_p[$i];
            next if vec($brd,   $bp, 8) == WALL;
            next if vec($Inner, $bp, 8) == 0;
            my $index = $Y_x_to_index_table[$bp] * 4;
            if (vec($brd, $p, 8) & SOKOBAN) {
                if (vec($brd, $bp, 8) & SOKOBAN) {
                    $active->[$index + (($i + 2) & 3)] = 0;
                }
            }
            next unless ((vec($brd, $p, 8) & SOKOBAN) == 0);
            $active->[$index + (($i + 2) & 3)] = 0;
        }
    } ## end for my $p (0 .. $Ncells...)
    return;
} ## end sub make_holes_inactive

sub init_shift ($brd, $gd) {
    my $active = $gd->{'active'};
    my $shift  = $gd->{'shift'};
    @$shift = (0) x ($gd->{'vertices_num'} * 4);
    for my $i (0 .. $Index_num - 1) {
        my $p = $Index_to_p[$i];
        next if vec($brd, $p, 8) & OCCUPIED;
        vec($brd, $p, 8) |= BOX;
        my @zones = zones_around_place($brd, $p);
        vec($brd, $p, 8) &= 0xFF ^ BOX;
        for my $from (0 .. 3) {
            next if $active->[$i * 4 + $from] == 0;
            my $zf = $zones[$from];
            next if $zf == 1000000;
            for my $to (0 .. 3) {
                next if $to == $from;
                next if $active->[$i * 4 + $to] == 0;
                my $zt = $zones[$to];
                next if $zt == 1000000;
                $shift->[($i * 4 + $from) * 4 + $to] = $i * 4 + $to
                    if $zf == $zt;
            }
        }
    } ## end for my $i (0 .. $Index_num...)
    return;
} ## end sub init_shift

sub init_push ($brd, $gd) {
    my $active = $gd->{'active'};
    my $push   = $gd->{'push'};
    for my $i (0 .. $gd->{'vertices_num'} - 1) {
        next if $active->[$i] == 0;
        my $base_p = $Index_to_p[int($i / 4)];
        Carp::confess('something is bad')
            if vec($brd, $base_p, 8) & OCCUPIED;
        my $push_p = $base_p - $Delta_p[$i % 4];
        if (vec($brd, $push_p, 8) & OCCUPIED) {
            $push->[$i] = 0;
        }
        else {
            $push->[$i] = $Y_x_to_index_table[$push_p] * 4 + ($i % 4);
        }
    }
    return;
} ## end sub init_push

sub init_pull ($brd, $gd) {
    my $active = $gd->{'active'};
    my $pull   = $gd->{'pull'};
    for my $i (0 .. $gd->{'vertices_num'} - 1) {
        next if $active->[$i] == 0;
        my $base_p = $Index_to_p[int($i / 4)];
        Carp::confess('something is bad')
            if vec($brd, $base_p, 8) & OCCUPIED;
        $pull->[$i] = 0;
        next if vec($brd, $base_p + $Delta_p[$i % 4] * 2, 8) & OCCUPIED;
        $pull->[$i] = $Y_x_to_index_table[$base_p + $Delta_p[$i % 4]] * 4 + ($i % 4);
    }
    return;
}

sub set_graph_weights_to_infinity ($gd) {
    my $n = $gd->{'vertices_num'};
    @{ $gd->{'weight'} }     = (1000000) x $n;
    @{ $gd->{'src'} }        = (-1) x $n;
    @{ $gd->{'reversible'} } = (0) x $n;
    return;
}

sub build_graph ($brd, $pull_mode, $gd) {
    Carp::confess('boxes in board') if (($brd&.$BOX_ONLY) =~ tr/\x00//c);
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
    for my $i (0 .. $gd->{'vertices_num'} - 1) {
        next unless ($weight->[$i] == 0);
        $src->[$i] = -1;
        push @next, $i;
        $visited[$i] = 1;
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
        } ## end for my $v (@current)
    } ## end while (@next)
    return;
} ## end sub do_graph_iterations

sub get_weight_around_cell ($index, $gd) {
    my $min    = 1000000;
    my $active = $gd->{'active'};
    my $weight = $gd->{'weight'};
    for my $j (0 .. 3) {
        next                              if $active->[$index * 4 + $j] == 0;
        $min = $weight->[$index * 4 + $j] if $weight->[$index * 4 + $j] < $min;
    }
    return $min;
}

sub get_box_moves_from_graph ($start_index, $gd) {
    my @moves;
    my $weight     = $gd->{'weight'};
    my $src        = $gd->{'src'};
    my $reversible = $gd->{'reversible'};
    for my $i (0 .. $Index_num - 1) {
        my $p = $Index_to_p[$i];
        next if vec($gd->{'current_impossible_board'}, $p, 8);
        for my $j (0 .. 3) {
            next if $weight->[$i * 4 + $j] == 1000000;
            next if $weight->[$i * 4 + $j] == 0;
            next if int($src->[$i * 4 + $j] / 4) == $i;
            push @moves,
                {
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
        } ## end for my $j (0 .. 3)
    } ## end for my $i (0 .. $Index_num...)
    return @moves;
} ## end sub get_box_moves_from_graph

sub find_sources_of_a_group ($brd, $group) {
    my $gd = allocate_graph();
    build_graph($brd, 1, $gd);
    for my $g (@$group) {
        clear_weight_around_cell($g, $gd);
    }
    do_graph_iterations(1, $gd);
    my @srcs = grep {get_weight_around_cell($_, $gd) != 1000000 or in_group($_, $group)} 0 .. $Index_num - 1;
    my $res;
    $res = $ZERO_BOARD;
    for my $i (@srcs) {
        my $p = $Index_to_p[$i];
        vec($res, $p, 8) = 1;
    }
    return $res;
} ## end sub find_sources_of_a_group

sub find_targets_of_a_group ($brd, $group) {
    my $gd = allocate_graph();
    build_graph($brd, 0, $gd);
    for my $g (@$group) {
        clear_weight_around_cell($g, $gd);
    }
    do_graph_iterations(0, $gd);
    my @tmp_targets = grep {get_weight_around_cell($_, $gd) != 1000000 or in_group($_, $group)} 0 .. $Index_num - 1;
    my $targets;
    $targets = $ZERO_BOARD;
    for my $i (@tmp_targets) {
        my $p = $Index_to_p[$i];
        vec($targets, $p, 8) = 1;
    }
    return $targets;
} ## end sub find_targets_of_a_group

sub find_targets_of_a_board_input ($brd, $in) {
    my @group;
    for my $p (0 .. $Ncells - 1) {
        next if vec($Inner, $p, 8) == 0;
        push @group, $Y_x_to_index_table[$p] if vec($in, $p, 8);
    }
    return find_targets_of_a_group($brd, \@group);
}

sub find_sources_of_a_board_input ($brd, $in) {
    my @group;
    for my $p (0 .. $Ncells - 1) {
        next unless vec($in, $p, 8);
        my $idx = $Y_x_to_index_table[$p];
        Carp::confess('y_x_to_index') if $idx < 0;
        push @group, $idx;
    }
    return find_sources_of_a_group($brd, \@group);
}

sub find_targets_of_place_without_init_graph ($start_p, $gd) {
    my $weight = $gd->{'weight'};
    my $targets;
    $targets = $ZERO_BOARD;
    set_graph_weights_to_infinity($gd);
    clear_weight_around_cell($Y_x_to_index_table[$start_p], $gd);
    do_graph_iterations(0, $gd);
    for my $i (0 .. $gd->{'vertices_num'} - 1) {
        next unless ($weight->[$i] != 1000000);
        my $p = $Index_to_p[int($i / 4)];
        vec($targets, $p, 8) = 1;
    }
    vec($targets, $start_p, 8) = 1;
    return $targets;
} ## end sub find_targets_of_place_without_init_graph

sub find_distance_from_a_group ($brd, $group, $dist, $pull_mode) {
    my $gd = allocate_graph();
    build_graph($brd, $pull_mode, $gd);
    for my $i (0 .. $Index_num - 1) {
        my $p = $Index_to_p[$i];
        clear_weight_around_cell($i, $gd) if vec($group, $p, 8);
    }
    do_graph_iterations($pull_mode, $gd);
    @$dist = (1000000) x $Ncells;
    for my $i (0 .. $Index_num - 1) {
        my $p = $Index_to_p[$i];
        $dist->[$p] = get_weight_around_cell($i, $gd);
    }
    return;
} ## end sub find_distance_from_a_group

sub update_shift ($brd, $p, $gd) {
    my $shift = $gd->{'shift'};
    my $index = $Y_x_to_index_table[$p] * 4;
    my @has_sokoban =
        map {(vec($brd, $p + $Delta_p[$_], 8) & SOKOBAN) ? 1 : 0} 0 .. 3;
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
    my $d      = 0;
    my (@current, @next);
    @{ $gd->{'shift'} } = (0) x ($gd->{'vertices_num'} * 4);
    set_graph_weights_to_infinity($gd);
    my $box_p = $Index_to_p[$box_index];

    if ((vec($brd, $box_p, 8) & BOX) == 0) {
        Carp::confess('missing box3');
    }
    for my $i (0 .. 3) {
        next unless (vec($brd, $box_p + $Delta_p[$i], 8) & SOKOBAN);
        $weight->[$box_index * 4 + $i] = $d;
        push @current, $box_index * 4 + $i;
    }
    vec($brd, $box_p, 8) &= 0xFF ^ BOX;
    while (@current) {
        $d++;
        @next = ();
        for my $index (@current) {
            my $direction = $index & 3;
            $box_p = $Index_to_p[int($index / 4)];
            my $sok_p = $box_p + $Delta_p[$direction];
            my ($next_box_p, $next_sok_p);
            if ($pull_mode == 0) {
                $next_box_p = $box_p - $Delta_p[$direction];
                $next_sok_p = $sok_p - $Delta_p[$direction];
                next if vec($brd, $next_box_p, 8) & OCCUPIED;
            }
            else {
                $next_box_p = $box_p + $Delta_p[$direction];
                $next_sok_p = $sok_p + $Delta_p[$direction];
                next if vec($brd, $next_sok_p, 8) & OCCUPIED;
            }
            next if vec($gd->{'current_impossible_board'}, $next_box_p, 8);
            my $next_index = $Y_x_to_index_table[$next_box_p] * 4 + $direction;
            next if $weight->[$next_index] != 1000000;
            $weight->[$next_index] = $d;
            $src->[$next_index]    = $index;
            push @next, $next_index;
            my $index_after_push = $next_index;
            $brd&.=$NOT_SOKOBAN;
            vec($brd, $next_box_p, 8) |= BOX;
            vec($brd, $next_sok_p, 8) |= SOKOBAN;
            $brd = expand_sokoban_cloud($brd, $next_sok_p);
            update_shift($brd, $next_box_p, $gd);
            my $next_box_index4 = $Y_x_to_index_table[$next_box_p] * 4;

            for my $j (0 .. 3) {
                next
                    if (vec($brd, $next_box_p + $Delta_p[$j], 8) & SOKOBAN) == 0;
                $next_index = $next_box_index4 + $j;
                next if $weight->[$next_index] != 1000000;
                $weight->[$next_index] = $d;
                $src->[$next_index]    = $index_after_push;
                push @next, $next_index;
            }
            vec($brd, $next_box_p, 8) &= 0xFF ^ BOX;
        } ## end for my $index (@current)
        @current = @next;
    } ## end while (@current)
    return;
} ## end sub mark_box_moves_in_graph

sub find_reversible_moves ($brd, $box_index, $pull_mode, $gd) {
    my (@current, @next, @visited);
    my $src        = $gd->{'src'};
    my $reversible = $gd->{'reversible'};
    @visited = (0) x $gd->{'vertices_num'};
    my $box_p = $Index_to_p[$box_index];
    Carp::confess('missing box4')
        if (vec($brd, $box_p, 8) & BOX) == 0;
    vec($brd, $box_p, 8) &= 0xFF ^ BOX;
    @$reversible = (0) x $gd->{'vertices_num'};

    for my $i (0 .. 3) {
        next if (vec($brd, $box_p + $Delta_p[$i], 8) & SOKOBAN) == 0;
        my $index = $box_index * 4 + $i;
        $reversible->[$index] = 1;
        push @current, $index;
        $visited[$index] = 1;
    }
    while (@current) {
        @next = ();
        for my $index (@current) {
            for my $j (0 .. 3) {
                my $next_index = ($index & ~3) + $j;
                next if $visited[$next_index];
                if (($index ^ $next_index) >> 2) {
                    Carp::confess('bad call');
                }
                next if $gd->{'shift'}[$index * 4 + ($next_index & 3)] != $next_index;
                if ($src->[$next_index] != -1) {
                    push @next, $next_index;
                    $reversible->[$next_index] = 1;
                    $visited[$next_index] = 1;
                }
            }
            $box_p = $Index_to_p[$index >> 2];
            my $direction = $index & 3;
            my $sok_p     = $box_p + $Delta_p[$direction];
            Carp::confess('back problem')
                if vec($brd, $sok_p, 8) & OCCUPIED;
            if ($pull_mode == 0) {
                $sok_p += $Delta_p[$direction];
                $box_p += $Delta_p[$direction];
                next if vec($brd, $sok_p, 8) & OCCUPIED;
            }
            else {
                $box_p -= $Delta_p[$direction];
                next if vec($brd, $box_p, 8) & OCCUPIED;
            }
            my $next_index = $Y_x_to_index_table[$box_p] * 4 + $direction;
            next if vec($gd->{'current_impossible_board'}, $box_p, 8);
            next if $visited[$next_index];
            next unless ($src->[$next_index] != -1);
            push @next, $next_index;
            $reversible->[$next_index] = 1;
            $visited[$next_index] = 1;
        } ## end for my $index (@current)
        @current = @next;
    } ## end while (@current)
    vec($brd, $Index_to_p[$box_index], 8) |= BOX;
    return;
} ## end sub find_reversible_moves

sub rooms_bfs ($brd, $start_p, $color, $seen, $visited) {
    my $bfs_visited;
    $bfs_visited = $ZERO_BOARD;
    @$seen       = (0) x $Rooms_num;
    my @current = ($start_p);
    vec($visited,     $start_p, 8) = 1;
    vec($bfs_visited, $start_p, 8) = 1;
    while (@current) {
        my @next;
        for my $p (@current) {
            for my $j (0 .. 3) {
                my $np         = $p + $Delta_p[$j];
                my $seen_color = $Rooms_board->[$np];
                if ($seen_color != 1000000 and $seen_color != $color) {
                    $seen->[$seen_color] = 1;
                    next;
                }
                next if vec($bfs_visited, $np, 8);
                next if vec($visited,     $np, 8);
                next if vec($brd,         $np, 8) & OCCUPIED;
                vec($bfs_visited, $np, 8) = 1;
                vec($visited,     $np, 8) = 1 if $seen_color == $color;
                push @next, $np;
            }
        } ## end for my $p (@current)
        @current = @next;
    } ## end while (@current)
    return $visited;
} ## end sub rooms_bfs

sub get_current_graph ($brd, $current_graph) {
    my @seen_during_bfs;
    my @color_processed;
    my $visited;
    $visited = $ZERO_BOARD;
    for my $i (0 .. $Rooms_num - 1) {
        for my $j (0 .. $Rooms_num - 1) {
            $current_graph->[$i][$j] = 1;
        }
    }
    for my $i (0 .. $Rooms_num - 1) {
        $current_graph->[$i][$i] = 0;
    }
    for my $i (0 .. $Rooms_num - 1) {
        $color_processed[$i] = 0;
    }
    for my $p (0 .. $Ncells - 1) {
        next if vec($Inner,   $p, 8) == 0;
        next if vec($brd,     $p, 8) & OCCUPIED;
        next if vec($visited, $p, 8);
        my $color = $Rooms_board->[$p];
        next if $color == 1000000;
        $color_processed[$color] = 1;
        $visited = rooms_bfs($brd, $p, $color, \@seen_during_bfs, $visited);
        for my $k (0 .. $Rooms_num - 1) {
            next unless ($seen_during_bfs[$k] == 0);
            $current_graph->[$color][$k] = 0;
            $current_graph->[$k][$color] = 0;
        }
    }
    for my $i (0 .. $Rooms_num - 1) {
        next unless ($color_processed[$i] == 0);
        for my $j (0 .. $Rooms_num - 1) {
            $current_graph->[$i][$j] = 0;
            $current_graph->[$j][$i] = 0;
        }
    }
    return;
} ## end sub get_current_graph

sub score_rooms ($brd) {
    my $sum = 0;
    my @current_graph;
    return 0 if $Rooms_num <= 1;
    get_current_graph($brd, \@current_graph);
    for my $i (0 .. $Rooms_num - 1) {
        for my $j (0 .. $Rooms_num - 1) {
            $sum += $Base_graph[$i][$j] - $current_graph[$i][$j];
        }
    }
    Carp::confess('odd') if $sum % 2;
    return $sum / 2;
}

sub simple_box_can_be_pulled ($brd, $p) {
    for my $i (0 .. 3) {
        next unless ((vec($brd, $p + $Delta_p[$i], 8) & OCCUPIED) == 0);
        return 1
            if (vec($brd, $p + 2 * $Delta_p[$i], 8) & OCCUPIED) == 0;
    }
    return 0;
}

sub pullable_boxes ($brd) {
    my $res = 0;
    for my $p (0 .. $Ncells - 1) {
        $res += simple_box_can_be_pulled($brd, $p)
            if vec($brd, $p, 8) & BOX;
    }
    return $res;
}

sub compute_pull_order ($b_in, $order) {
    my ($brd,     $visited);
    my (@current, @next);
    my $current_num = 0;
    my $next_num;
    my $depth = 0;
    $brd     = $b_in;
    $visited = $ZERO_BOARD;
    @$order  = (-1) x $Ncells;

    for my $p (0 .. $Ncells - 1) {
        next unless (vec($brd, $p, 8) & BOX);
        if (simple_box_can_be_pulled($brd, $p)) {
            vec($visited, $p, 8) = 1;
            $current[$current_num++] = $Y_x_to_index_table[$p];
        }
    }
    while ($current_num) {
        for my $i (0 .. $current_num - 1) {
            my $p = $Index_to_p[$current[$i]];
            $order->[$p] = $depth;
            vec($brd, $p, 8) &= 0xFF ^ BOX;
        }
        $next_num = 0;
        $depth++;
        for my $i (0 .. $current_num - 1) {
            my $p = $Index_to_p[$current[$i]];
            for my $j (0 .. 3) {
                my $box_p = $p + $Delta_p[$j];
                next if (vec($brd, $box_p, 8) & BOX) == 0;
                next if vec($visited, $box_p,            8);
                next if vec($brd,     $p - $Delta_p[$j], 8) & OCCUPIED;
                vec($visited, $box_p, 8) = 1;
                $next[$next_num++] = $Y_x_to_index_table[$box_p];
            }
            for my $j (0 .. 3) {
                next if vec($brd, $p + $Delta_p[$j], 8) & OCCUPIED;
                my $box_p = $p + $Delta_p[$j] * 2;
                next if (vec($brd, $box_p, 8) & BOX) == 0;
                next if vec($visited, $box_p, 8);
                vec($visited, $box_p, 8) = 1;
                $next[$next_num++] = $Y_x_to_index_table[$box_p];
            }
        } ## end for my $i (0 .. $current_num...)
        for my $i (0 .. $next_num - 1) {
            $current[$i] = $next[$i];
        }
        $current_num = $next_num;
    } ## end while ($current_num)
    if ((($brd&.$BOX_ONLY) =~ tr/\x00//c) > 0) {
        return;
    }
    return;
} ## end sub compute_pull_order

sub touched_boxes ($brd) {
    my $sum = 0;
    for my $p (0 .. $Ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;
        my $k;
        for ($k = 0; $k < 4; $k++) {
            last if vec($brd, $p + $Delta_p[$k], 8) & SOKOBAN;
        }
        $sum++ if $k < 4;
    }
    return $sum;
}

sub count_101 ($brd) {
    my $sum = 0;
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($brd, $p, 8) & BOX);
        if ((vec($brd, $p + 1, 8) & OCCUPIED) == 0) {
            $sum++ if vec($brd, $p + 2, 8) & BOX;
        }
        if ((vec($brd, $p + $Width, 8) & OCCUPIED) == 0) {
            $sum++ if vec($brd, $p + 2 * $Width, 8) & BOX;
        }
    }
    return $sum;
}

sub unlikely_pattern ($brd) {
    my $res = 0;
    for my $p (0 .. $Ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;
        my $sum = 0;
        for my $k (0 .. 7) {
            $sum++
                if vec($brd, $p + $Delta_p_8[$k], 8) & OCCUPIED;
        }
        $res++ if $sum >= 6;
    }
    return $res;
}

sub snail_packed ($brd) {
    my @seq;
    for my $i (0 .. $Snail_chain_len - 1) {
        $seq[$i] = 1;
    }
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($Snail_chain, $p, 8));
        if ((vec($brd, $p, 8) & BOX) == 0) {
            $seq[$Snail_dist->[$p]] = 0;
        }
    }
    my $i;
    for ($i = 1; $i < $Snail_chain_len; $i++) {
        return $i if $seq[$i] == 0;
    }
    return $i;
} ## end sub snail_packed

sub fill_snail_scores ($brd, $s, $alg_type) {
    if (vec($brd, $Snail_target_y * $Width + $Snail_target_x, 8) & BOX) {
        $s->{'out_of_plan'} = 1;
    }
    else {
        $s->{'out_of_plan'} = 0;
    }
    $s->{'dist_to_imagined'} = unlikely_pattern($brd) if $alg_type == 0;
    $s->{'biconnect'}        = $Global_boxes_in_level - touched_boxes($brd);
    if ($s->{'out_of_plan'} == 1) {
        $s->{'hotspots'} = count_101($brd) if $alg_type == 0;
    }
    else {
        $s->{'boxes_on_targets'} = snail_packed($brd);
    }
    return;
} ## end sub fill_snail_scores

sub is_better_snail_score ($new_score, $old_score, $pull_mode) {
    return 1 if $new_score->{'out_of_plan'} < $old_score->{'out_of_plan'};
    return 0 if $new_score->{'out_of_plan'} > $old_score->{'out_of_plan'};
    return 1 if $new_score->{'biconnect'} < $old_score->{'biconnect'};
    return 0 if $new_score->{'biconnect'} > $old_score->{'biconnect'};
    return 1
        if $new_score->{'dist_to_imagined'} < $old_score->{'dist_to_imagined'};
    return 0
        if $new_score->{'dist_to_imagined'} > $old_score->{'dist_to_imagined'};
    if ($new_score->{'out_of_plan'} == 0) {
        return 1
            if $new_score->{'boxes_on_targets'} > $old_score->{'boxes_on_targets'};
        return 0
            if $new_score->{'boxes_on_targets'} < $old_score->{'boxes_on_targets'};
    }
    else {
        return 1 if $new_score->{'hotspots'} > $old_score->{'hotspots'};
        return 0 if $new_score->{'hotspots'} < $old_score->{'hotspots'};
    }
    return 1 if $new_score->{'dist_to_targets'} > $old_score->{'dist_to_targets'};
    return 0 if $new_score->{'dist_to_targets'} < $old_score->{'dist_to_targets'};
    return 0;
} ## end sub is_better_snail_score

sub set_snail_parameters ($search_type, $pull_mode, $h) {
    return $search_type if $Snail_level_detected == 0;
    if ($pull_mode == 0) {
        if (   ($search_type == FORWARD_WITH_BASES)
            or ($search_type == HF_SEARCH)
            or ($search_type == GIRL_SEARCH))
        {
            return HF_SEARCH;
        }
        return $search_type;
    }
    if ($search_type == BASE_SEARCH) {
        $h->{'alg_type'}        = 0;
        $h->{'weighted_search'} = 0;
        return SNAIL_SEARCH;
    }
    if ($search_type == MAX_DIST_SEARCH2) {
        $h->{'alg_type'}        = 1;
        $h->{'weighted_search'} = 0;
        return SNAIL_SEARCH;
    }
    if ($search_type == GIRL_SEARCH) {
        $h->{'alg_type'}        = 3;
        $h->{'weighted_search'} = 1;
        return NETLOCK_SEARCH;
    }
    return $search_type;
} ## end sub set_snail_parameters

sub netlock_score ($brd) {
    my $c;
    my $order = [];
    return 0
        if (vec($brd, $Snail_target_y * $Width + $Snail_target_x, 8) & BOX) == 0;
    $c = $brd;
    compute_pull_order($c, $order);
    my $res = $order->[$Snail_target_y * $Width + $Snail_target_x];
    if (vec($brd, $Snail_target_y * $Width + $Snail_target_x, 8) & BOX) {
        return 1000 if $res == -1;
    }
    return $res;
}

sub boxes_on_grid ($brd) {
    my $sum = 0;
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($Netlock_grid, $p, 8));
        $sum++ if vec($brd, $p, 8) & BOX;
    }
    return $sum;
}

sub fill_netlock_scores ($brd, $s, $alg_type) {
    $s->{'connectivity'}     = get_connectivity($brd);
    $s->{'boxes_on_targets'} = netlock_score($brd);
    $s->{'rooms_score'}      = boxes_on_grid($brd);
    if ($s->{'boxes_on_targets'} == 0) {
        $s->{'imagine'} = pullable_boxes($brd);
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
} ## end sub fill_netlock_scores

sub set_netlock_parameters ($search_type, $pull_mode, $h) {
    return $search_type if $Netlock_level_detected == 0;
    if ($pull_mode == 0) {
        if (   ($search_type == FORWARD_WITH_BASES)
            or ($search_type == HF_SEARCH)
            or ($search_type == GIRL_SEARCH))
        {
            return HF_SEARCH;
        }
        return $search_type;
    }
    if ($search_type == BASE_SEARCH) {
        $h->{'alg_type'} = 0;
        return NETLOCK_SEARCH;
    }
    if ($search_type == MAX_DIST_SEARCH2) {
        $h->{'alg_type'} = 1;
        return NETLOCK_SEARCH;
    }
    if ($search_type == GIRL_SEARCH) {
        $h->{'alg_type'} = 2;
        return NETLOCK_SEARCH;
    }
    return $search_type;
} ## end sub set_netlock_parameters

sub is_2x2_deadlock_at_place ($brd, $p) {
    for my $o (0, 1, $Width, $Width + 1) {
        return 0 if (vec($brd, $p + $o, 8) & OCCUPIED) == 0;
    }
    for my $o (0, 1, $Width, $Width + 1) {
        my $c = vec($brd, $p + $o, 8);
        return 1 if ($c & BOX) and ($c & TARGET) == 0;
    }
    return 0;
}

sub mark_deadlock_2x2 ($c) {
    $c&.=$NOT_SOKOBAN;
    my $d;
    $d = $ZERO_BOARD;
    for my $i (0 .. $Height - 2) {
        for my $j (0 .. $Width - 2) {
            my $p = $i * $Width + $j;
            my ($sum, $stuck) = (0, 0);
            for my $y (0 .. 1) {
                for my $x (0 .. 1) {
                    my $val = vec($c, $p + $y * $Width + $x, 8);
                    $sum++   if $val & OCCUPIED;
                    $stuck++ if $val != WALL and ($val & TARGET) == 0;
                }
            }
            if ($sum == 3 and $stuck) {
                for my $y (0 .. 1) {
                    for my $x (0 .. 1) {
                        vec($d, $p + $y * $Width + $x, 8) = 1;
                    }
                }
            }
            if (vec($c, $p, 8) == WALL and vec($c, $p + $Width + 1, 8) == WALL) {
                vec($d, $p + 1,      8) = 1 if vec($c, $p + 1,      8) == 0;
                vec($d, $p + $Width, 8) = 1 if vec($c, $p + $Width, 8) == 0;
            }
            next unless (vec($c, $p + 1, 8) == WALL and vec($c, $p + $Width, 8) == WALL);
            vec($d, $p,              8) = 1 if vec($c, $p, 8) == 0;
            vec($d, $p + $Width + 1, 8) = 1
                if vec($c, $p + $Width + 1, 8) == 0;
        } ## end for my $j (0 .. $Width ...)
    } ## end for my $i (0 .. $Height...)
    return $d;
} ## end sub mark_deadlock_2x2

sub set_current_impossible ($b_in, $box_p, $pull_mode, $search_mode, $possible_board, $gd) {
    my $brd;
    $brd = $b_in;
    my $cib;
    $cib = $ZERO_BOARD;
    for my $i (0 .. $Index_num - 1) {
        my $p = $Index_to_p[$i];
        vec($cib, $p, 8) = 1
            if $Impossible_place[$i];
        vec($cib, $p, 8) = 1 if vec($brd, $p, 8) == WALL;
    }
    if ($pull_mode == 0) {
        vec($brd, $box_p, 8) &= 0xFF ^ BOX;
        my $blocked;
        $blocked = mark_deadlock_2x2($brd);
        for my $p (0 .. $Ncells - 1) {
            next if vec($Inner, $p, 8) == 0;
            vec($cib, $p, 8) = 1 if vec($blocked, $p, 8);
        }
    }
    for my $p (0 .. $Ncells - 1) {
        next if vec($Inner, $p, 8) == 0;
        vec($cib, $p, 8) = 1 if vec($possible_board, $p, 8) == 0;
    }
    $gd->{'current_impossible_board'} = $cib;
    return;
} ## end sub set_current_impossible

sub deadlock_in_direction ($brd, $p, $d) {
    my $dp  = $Delta_p[$d];
    my $dp2 = $Delta_p[($d + 1) & 3];
    my $np  = $p + $dp;
    return 1                     if vec($Inner, $np, 8) == 0;
    return 1                     if $Impossible_place[$Y_x_to_index_table[$np]];
    Carp::confess('missing box') if (vec($brd, $p, 8) & BOX) == 0;
    Carp::confess('no space')    if vec($brd, $np, 8) & OCCUPIED;
    if ((vec($brd, $np, 8) & TARGET) == 0
        and vec($brd, $np + $dp, 8) == WALL)
    {
        return 1 if vec($brd, $np + $dp2, 8) == WALL;
        return 1 if vec($brd, $np - $dp2, 8) == WALL;
    }
    if (vec($brd, $np + $dp, 8) & BOX) {
        my ($wall1, $wall2, $wall3, $wall4) = (0, 0, 0, 0);
        $wall4 = 1 if vec($brd, $np + $dp2,       8) == WALL;
        $wall3 = 1 if vec($brd, $np - $dp2,       8) == WALL;
        $wall2 = 1 if vec($brd, $np + $dp + $dp2, 8) == WALL;
        $wall1 = 1 if vec($brd, $np + $dp - $dp2, 8) == WALL;
        if ($wall1 + $wall4 == 2 or $wall2 + $wall3 == 2) {
            return 1 if (vec($brd, $np,       8) & TARGET) == 0;
            return 1 if (vec($brd, $np + $dp, 8) & TARGET) == 0;
        }
    }
    vec($brd, $p, 8) &= 0xFF ^ BOX;
    vec($brd, $np, 8) |= BOX;
    my $res_0 = is_2x2_deadlock_at_place($brd, $p + $Square_place_p[$d][0]);
    my $res_1 = is_2x2_deadlock_at_place($brd, $p + $Square_place_p[$d][1]);
    vec($brd, $np, 8) &= 0xFF ^ BOX;
    vec($brd, $p, 8) |= BOX;
    return 1 if $res_0 or $res_1;
    return 0;
} ## end sub deadlock_in_direction

sub remove_all_pushable_boxes ($brd) {
    my $changed = 1;
    while ($changed) {
        $changed = 0;
        for my $p (0 .. $Ncells - 1) {
            next if (vec($brd, $p, 8) & BOX) == 0;
            for my $k (0 .. 3) {
                next if vec($brd, $p + $Delta_p[$k], 8) & OCCUPIED;
                next if vec($brd, $p - $Delta_p[$k], 8) & OCCUPIED;
                next if deadlock_in_direction($brd, $p, $k);
                vec($brd, $p, 8) &= 0xFF ^ BOX;
                $changed = 1;
                last;
            }
        }
    }
    return $brd;
} ## end sub remove_all_pushable_boxes

sub turn_immovable_boxes_to_walls ($brd) {
    my $remaining;
    my $changed = 0;
    $remaining = $brd;
    $remaining = remove_all_pushable_boxes($remaining);
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($remaining, $p, 8) & BOX);
        vec($brd, $p, 8) = WALL;
        $changed = 1;
    }
    return ($changed, $brd);
}

sub turn_fixed_boxes_into_walls ($brd) {
    my $w;
    $w = $brd;
    $w = fix_boxes_using_envelopes($w);
    my $changed = 1;
    while ($changed) {
        my $f;
        ($changed, $w) = turn_2x2_to_walls($w);
        ($f,       $w) = close_holes($w);
        $changed |= $f;
        ($f, $w) = turn_immovable_boxes_to_walls($w);
        $changed |= $f;
        ($f, $w) = fix_diagonals($w);
        $changed |= $f;
        ($f, $w) = fix_crystaline($w);
        $changed |= $f;
    }
    return $w;
} ## end sub turn_fixed_boxes_into_walls

sub box_touches_unreachable_square ($brd, $p) {
    for my $i (0 .. 7) {
        my $c = vec($brd, $p + $Delta_p_8[$i], 8);
        next if $c & OCCUPIED;
        next if $c & SOKOBAN;
        return 1;
    }
    return 0;
}

sub box_is_pushable ($brd, $p) {
    if ((vec($brd, $p - $Width, 8) & OCCUPIED) == 0) {
        return 1 if (vec($brd, $p + $Width, 8) & OCCUPIED) == 0;
    }
    if ((vec($brd, $p - 1, 8) & OCCUPIED) == 0) {
        return 1 if (vec($brd, $p + 1, 8) & OCCUPIED) == 0;
    }
    return 0;
}

sub is_freeze_deadlock ($brd, $box_p) {
    Carp::confess('check caller') if (vec($brd, $box_p, 8) & BOX) == 0;
    return 0                      if box_is_pushable($brd, $box_p);
    my $c       = $brd;
    my $changed = 1;
    while ($changed) {
        $changed = 0;
        for my $p (0 .. $Ncells - 1) {
            next unless (vec($c, $p, 8) & BOX);
            if (box_is_pushable($c, $p)) {
                vec($c, $p, 8) &= 0xFF ^ BOX;
                $changed = 1;
            }
        }
    }
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($c, $p, 8) & BOX);
        return 1 if (vec($c, $p, 8) & TARGET) == 0;
    }
    return 0;
} ## end sub is_freeze_deadlock

sub is_3x3_deadlock ($brd, $box_p) {
    return 0 if box_touches_unreachable_square($brd, $box_p) == 0;
    for my $dy (-1 .. 1) {
        for my $dx (-1 .. 1) {
            my $p = $box_p + $dy * $Width + $dx;
            next if vec($Inner, $p, 8) == 0;
            next if vec($brd,   $p, 8) & OCCUPIED;
            next if vec($brd,   $p, 8) & TARGET;
            my $open = 0;
            for my $i (0 .. 3) {
                next unless ((vec($brd, $p + $Delta_p[$i], 8) & OCCUPIED) == 0);
                $open = 1;
                last;
            }
            next if $open;
            my $off_target = 0;
            for my $i (0 .. 3) {
                my $c = vec($brd, $p + $Delta_p[$i], 8);
                next unless (($c & BOX) and ($c & TARGET) == 0);
                $off_target = 1;
                last;
            }
            next unless $off_target;
            if (vec($brd, $p - $Width - 1, 8) & OCCUPIED) {
                return 1 if vec($brd, $p + $Width + 1, 8) & OCCUPIED;
            }
            if (vec($brd, $p - $Width + 1, 8) & OCCUPIED) {
                return 1 if vec($brd, $p + $Width - 1, 8) & OCCUPIED;
            }
            for (my $i = 0; $i < 8; $i += 2) {
                my $val1 = vec($brd, $p + $Delta_p_8[$i], 8);
                next if $val1 != WALL;
                my $val2 = vec($brd, $p + $Delta_p_8[($i + 3) & 7], 8);
                my $val3 = vec($brd, $p + $Delta_p_8[($i + 5) & 7], 8);
                next     if ($val2 & OCCUPIED) == 0;
                next     if ($val3 & OCCUPIED) == 0;
                return 1 if $val2 == WALL or $val3 == WALL;
            }
        } ## end for my $dx (-1 .. 1)
    } ## end for my $dy (-1 .. 1)
    return 0;
} ## end sub is_3x3_deadlock

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
        last if $y + $pt->{'maxcy'} >= $Height;
    X: for my $x ($start_x .. $box_x) {
            last if $x + $mcx >= $Width;
            next
                if (vec($brd, ($y + $shift_y) * $Width + $x + $shift_x, 8) & BOX) == 0;
            my $base = $y * $Width + $x;
            for (my $k = 0; $k < @$fl; $k += 2) {
                next X if vec($brd, $base + $fl->[$k], 8) != $fl->[$k + 1];
            }
            return 1;
        }
    }
    return 0;
} ## end sub check_deadlock_pattern

sub check_all_patterns ($b_in, $box_p, $pull_mode) {
    return -1 if box_touches_unreachable_square($b_in, $box_p) == 0;
    my $box_y = int($box_p / $Width);
    my $box_x = $box_p % $Width;
    return -1 if $pull_mode and (($b_in&.$SOK_ONLY) =~ tr/\x00//c) > 4;
    my $brd;
    _dz_masks();
    $brd = $b_in&.$NOT_DZ;
    if ($pull_mode == 0) {
        for my $i (0 .. $#Patterns) {
            return $i if check_deadlock_pattern($Patterns[$i], $brd, $box_y, $box_x);
        }
    }
    else {
        return -1 if vec($brd, $Initial_sokoban_p, 8) & SOKOBAN;
        for my $i (0 .. $#Pull_patterns) {
            return $i
                if check_deadlock_pattern($Pull_patterns[$i], $brd, $box_y, $box_x);
        }
    }
    return -1;
} ## end sub check_all_patterns

sub is_inefficient_position ($brd, $box_index, $pull_mode, $search_mode, $h) {
    return 0 if $h->{'perimeter_found'};
    return 0 if $h->{'enable_inefficient_moves'};
    return 0 if $search_mode == K_DIST_SEARCH;
    my $box_p = $Index_to_p[$box_index];
    my $p     = $box_p;
    if ($pull_mode == 0) {
        return 0 if vec($h->{'used_in_plan'}, $p, 8);
        return 0
            if $search_mode == HF_SEARCH and vec($h->{'imagined_hf_board'}, $p, 8);
    }
    else {
        return 0
            if $search_mode == REV_SEARCH and vec($h->{'imagined_hf_board'}, $p, 8);
    }
    if ($pull_mode == 0) {
        return 0 if vec($brd, $p, 8) & TARGET;
    }
    else {
        return 0 if vec($Initial_board, $p, 8) & BOX;
    }
    return 1 if $pull_mode == 0 and vec($Forbidden_push_tunnel, $p, 8);
    return 1 if $pull_mode      and vec($Forbidden_pull_tunnel, $p, 8);
    my @val = map {vec($brd, $p + $Delta_p_8[$_], 8)} 0 .. 7;
    if ($pull_mode) {
        for (my $j = 0; $j < 8; $j += 2) {
            next
                unless (($val[$j & 7] & OCCUPIED) == 0
                    and $val[($j + 1) & 7] == WALL
                    and $val[($j + 3) & 7] == WALL
                    and $val[($j + 4) & 7] == WALL);
            return 1 if vec($brd, $p + 2 * $Delta_p_8[$j], 8) == WALL;
        }
        for (my $j = 0; $j < 8; $j += 2) {
            next
                unless (($val[$j & 7] & OCCUPIED) == 0
                    and $val[($j + 4) & 7] == WALL
                    and $val[($j + 5) & 7] == WALL
                    and $val[($j + 7) & 7] == WALL);
            return 1 if vec($brd, $p + 2 * $Delta_p_8[$j], 8) == WALL;
        }
        return 0;
    } ## end if ($pull_mode)
    for (my $j = 0; $j < 8; $j += 2) {
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
        if (    $val[($j + 3) & 7] == WALL
            and $val[($j + 5) & 7] == WALL
            and $val[($j + 2) & 7] & BOX
            and ($val[($j + 6) & 7] & SOKOBAN) == 0)
        {
            return 1;
        }
        next
            unless ($val[($j + 3) & 7] == WALL
                and $val[($j + 5) & 7] == WALL
                and $val[($j + 6) & 7] & BOX
                and ($val[($j + 2) & 7] & SOKOBAN) == 0);
        return 1;
    } ## end for (my $j = 0; $j < 8;...)
    return 0;
} ## end sub is_inefficient_position

sub set_blok ($src) {
    undef %Blok_sets;
    my $own = Storable::dclone($src);
    for my $bx (keys %$own) {
        my $row = $own->{$bx};
        for my $t (keys %$row) {
            for my $p (@{ $row->{$t} }) {
                Carp::confess('array blok pattern -- the Parser writes bit vectors')
                    if ref $p;
            }
            $Blok_sets{$bx}{$t} = $row->{$t};
        }
    }
    return scalar keys %Blok_sets;
}

sub _blok_boxvec ($brd) {
    my $vb = '';
    for my $p (0 .. $Ncells - 1) {
        vec($vb, $p, 1) = 1 if vec($brd, $p, 8) & BOX;
    }
    return $vb;
}

sub blok_forbids ($m) {
    my $t    = $Index_to_p[$m->{'to'}];
    my $prev = $t + $Delta_p[$m->{'sokoban_position'}];
    my $sets = $Blok_sets{$prev} && $Blok_sets{$prev}{$t} or return 0;
    my $vb   = $Blok_boxes;
    vec($vb, $Index_to_p[$m->{'from'}], 1) = 0;
    vec($vb, $t, 1) = 1;
    for my $pv (@$sets) {
        return 1 if ($vb&.$pv) eq $pv;
    }
    return 0;
}

sub get_distance_from_targets ($brd, $dist) {
    my ($target_area, $board_without_boxes);
    $target_area         = $ZERO_BOARD;
    $board_without_boxes = $brd&.$NOT_BOX;
    for my $p (0 .. $Ncells - 1) {
        vec($target_area, $p, 8) = 1 if vec($brd, $p, 8) & TARGET;
    }
    find_distance_from_a_group($board_without_boxes, $target_area, $dist, 1);
    return;
}

sub get_direction_from_pusher_dest ($pusher_p, $dest_p) {
    for my $i (0 .. 3) {
        return ($i, $pusher_p + $Delta_p[$i])
            if $pusher_p + $Delta_p[$i] * 2 == $dest_p;
    }
    Carp::confess('no direction');
}

sub get_corral_boxes ($orig_b, $cd) {
    my $corral_boxes;
    $corral_boxes = $orig_b&.$NOT_BOX;
    $corral_boxes&.=$NOT_SOKOBAN;
    for my $p (0 .. $Ncells - 1) {
        next if vec($cd->{'corral'}, $p, 8) == 0;
        vec($corral_boxes, $p, 8) |= SOKOBAN;
        for my $k (0 .. 7) {
            vec($corral_boxes, $p + $Delta_p_8[$k], 8) |= BOX
                if vec($orig_b, $p + $Delta_p_8[$k], 8) & BOX;
        }
    }
    return $corral_boxes;
}

sub is_possible_push_into_corral ($brd, $pp, $dp, $cd) {
    return 0 if vec($brd,            $pp, 8) == WALL;
    return 0 if vec($brd,            $dp, 8) & OCCUPIED;
    return 0 if vec($cd->{'corral'}, $pp, 8);
    return 0 if vec($cd->{'corral'}, $dp, 8) == 0;
    my ($direction, $box_p) = get_direction_from_pusher_dest($pp, $dp);
    return 0 if deadlock_in_direction($brd, $box_p, $direction);
    return 1;
}

sub is_possible_push_aside_corral ($brd, $pp, $dp, $cd) {
    return 0 if vec($brd,            $pp, 8) & OCCUPIED;
    return 0 if vec($brd,            $dp, 8) & OCCUPIED;
    return 0 if vec($cd->{'corral'}, $pp, 8);
    return 0 if vec($cd->{'corral'}, $dp, 8);
    my ($direction, $box_p) = get_direction_from_pusher_dest($pp, $dp);
    return 0 if deadlock_in_direction($brd, $box_p, $direction);
    return 1;
}

sub is_corral_active ($b_in, $cd) {
    my $corral_boxes;
    $corral_boxes = get_corral_boxes($b_in, $cd);
    for my $p (0 .. $Ncells - 1) {
        if (vec($cd->{'corral'}, $p, 8)) {
            Carp::confess('debug corral')
                if vec($corral_boxes, $p, 8) == TARGET;
            return 1 if vec($corral_boxes, $p, 8) == (TARGET | SOKOBAN);
        }
        return 1 if vec($corral_boxes, $p, 8) == BOX;
    }
    return 0;
}

sub set_corral_options ($b_in, $cd) {
    my $corral_boxes;
    $corral_boxes = get_corral_boxes($b_in, $cd);
    my $corral_options;
    $corral_options = $b_in&.$NOT_BOX;
    for my $p (0 .. $Ncells - 1) {
        next if (vec($corral_boxes, $p, 8) & BOX) == 0;
        for my $k (0 .. 3) {
            my $pusher_p = $p + $Delta_p[$k];
            next unless (is_possible_push_into_corral($corral_boxes, $pusher_p, $p - $Delta_p[$k], $cd));
            vec($corral_options, $p, 8) |= BOX
                if vec($b_in, $pusher_p, 8) & SOKOBAN;
        }
    }
    return $corral_options;
} ## end sub set_corral_options

sub get_corral_candidates ($brd, $cd) {
    my @corral_d;
    $cd->{'corral_comps_num'}    = mark_connectivities($brd, \@corral_d);
    $cd->{'corral_d'}            = \@corral_d;
    $cd->{'corral_sokoban_comp'} = $corral_d[get_sokoban_position($brd)];
    $cd->{'corral_candidates'}   = [(0) x $cd->{'corral_comps_num'}];
    for my $p (0 .. $Ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;
        for my $k (0 .. 3) {
            next unless ($corral_d[$p + $Delta_p[$k]] == $cd->{'corral_sokoban_comp'});
            my $other = $corral_d[$p - $Delta_p[$k]];
            $cd->{'corral_candidates'}[$other] = 1
                if $other != 1000000
                and $other != $cd->{'corral_sokoban_comp'};
        }
    }
    return;
} ## end sub get_corral_candidates

sub init_corral_with_comp ($comp1, $comp2, $b_in, $cd) {
    $cd->{'corral'}                        = $ZERO_BOARD;
    $cd->{'corral_component_used'}         = [(0) x $cd->{'corral_comps_num'}];
    $cd->{'corral_component_used'}[$comp1] = 1;
    $cd->{'corral_component_used'}[$comp2] = 1;
    for my $p (0 .. $Ncells - 1) {
        next unless ($cd->{'corral_d'}[$p] == $comp1 or $cd->{'corral_d'}[$p] == $comp2);
        vec($cd->{'corral'}, $p, 8) = 1;
    }
    return is_corral_active($b_in, $cd);
}

sub update_corral_with_comp ($comp1, $cd) {
    $cd->{'corral_component_used'}[$comp1] = 1;
    for my $p (0 .. $Ncells - 1) {
        vec($cd->{'corral'}, $p, 8) = 1 if $cd->{'corral_d'}[$p] == $comp1;
    }
    return;
}

sub box_touches_corral_and_non_corral ($brd, $p, $corral) {
    my ($touches_corral, $touches_non_corral) = (0, 0);
    for my $i (0 .. 3) {
        my $np = $p + $Delta_p[$i];
        $touches_corral = 1 if vec($corral, $np, 8);
        next unless ((vec($brd, $np, 8) & OCCUPIED) == 0);
        $touches_non_corral = 1 if vec($corral, $np, 8) == 0;
    }
    return $touches_corral & $touches_non_corral;
}

sub should_add_component_to_corral ($corral_boxes, $cd) {
    for my $p (0 .. $Ncells - 1) {
        next if (vec($corral_boxes, $p, 8) & BOX) == 0;
        next
            if box_touches_corral_and_non_corral($corral_boxes, $p, $cd->{'corral'}) == 0;
        for my $k (0 .. 3) {
            my $pusher_p        = $p + $Delta_p[$k];
            my $dest_p          = $p - $Delta_p[$k];
            my $can_push_inside = is_possible_push_into_corral($corral_boxes, $pusher_p, $dest_p, $cd);
            $can_push_inside = 0
                if vec($corral_boxes, $pusher_p, 8) & OCCUPIED;
            my $can_push_aside = is_possible_push_aside_corral($corral_boxes, $pusher_p, $dest_p, $cd);
            next if $can_push_inside == 0 and $can_push_aside == 0;
            if ($can_push_inside) {
                my $d = $cd->{'corral_d'}[$pusher_p];
                if ($d != 1000000) {
                    return (1, $d)
                        if $d != $cd->{'corral_sokoban_comp'}
                        and $cd->{'corral_component_used'}[$d] == 0;
                }
            }
            next unless ($can_push_aside);
            my $d = $cd->{'corral_d'}[$dest_p];
            Carp::confess('this is strange') if $d == 1000000;
            return (1, $d)
                if $d != $cd->{'corral_sokoban_comp'}
                and $cd->{'corral_component_used'}[$d] == 0;
        } ## end for my $k (0 .. 3)
    } ## end for my $p (0 .. $Ncells...)
    return (0, undef);
} ## end sub should_add_component_to_corral

sub can_push_box_out_of_corral ($brd, $corral) {
    for my $p (0 .. $Ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;
        next if vec($Inner, $p, 8) == 0;
        for my $k (0 .. 3) {
            my $pusher_p = $p + $Delta_p[$k];
            my $dest_p   = $p - $Delta_p[$k];
            next if vec($brd, $pusher_p, 8) & OCCUPIED;
            next if vec($brd, $dest_p,   8) & OCCUPIED;
            next if deadlock_in_direction($brd, $p, ($k + 2) & 3);
            next unless (vec($corral, $pusher_p, 8) == 0);
            if (vec($corral, $dest_p, 8) == 0) {
                return 1;
            }
        }
    } ## end for my $p (0 .. $Ncells...)
    return 0;
} ## end sub can_push_box_out_of_corral

sub check_pi_corral ($corral_boxes, $b_in, $cd) {
    for my $p (0 .. $Ncells - 1) {
        next if (vec($corral_boxes, $p, 8) & BOX) == 0;
        for my $k (0 .. 3) {
            my $pusher_p = $p + $Delta_p[$k];
            my $dest_p   = $p - $Delta_p[$k];
            next
                if is_possible_push_into_corral($corral_boxes, $pusher_p, $dest_p, $cd) == 0;
            next if vec($corral_boxes, $pusher_p, 8) & OCCUPIED;
            Carp::confess('not right1')
                if vec($cd->{'corral'}, $dest_p, 8) == 0;
            Carp::confess('not right2')
                if vec($cd->{'corral'}, $pusher_p, 8) == 1;
            return 0 if (vec($b_in, $pusher_p, 8) & SOKOBAN) == 0;
        }
    } ## end for my $p (0 .. $Ncells...)
    return 1;
} ## end sub check_pi_corral

sub expand_corral ($b_in, $cd) {
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
} ## end sub expand_corral

sub init_touches_two_comps ($brd, $cd) {
    my @touches;
    my $ncomp = $cd->{'corral_comps_num'};
    for my $i (0 .. $ncomp - 1) {
        for my $j (0 .. $ncomp - 1) {
            $touches[$i][$j] = 0;
        }
    }
    for my $p (0 .. $Ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;
        for my $k (0 .. 3) {
            for my $l (0 .. 3) {
                my $d1 = $cd->{'corral_d'}[$p + $Delta_p[$k]];
                my $d2 = $cd->{'corral_d'}[$p + $Delta_p[$l]];
                $touches[$d1][$d2] = 1
                    if $d1 != 1000000 and $d2 != 1000000;
            }
        }
    }
    return \@touches;
} ## end sub init_touches_two_comps

sub detect_corral ($brd) {
    my $cd = {
        'corral'                => '',
        'corral_d'              => [],
        'corral_component_used' => [],
        'corral_sokoban_comp'   => -1,
        'corral_comps_num'      =>  0,
        'corral_candidates'     => [],
    };
    get_corral_candidates($brd, $cd);
    for my $i (0 .. $cd->{'corral_comps_num'} - 1) {
        next if $cd->{'corral_candidates'}[$i] == 0;
        next if init_corral_with_comp($i, $i, $brd, $cd) == 0;
        next unless (expand_corral($brd, $cd) == 1);
        return (1, set_corral_options($brd, $cd));
    }
    my $touches_two_comps = init_touches_two_comps($brd, $cd);
    for my $i (0 .. $cd->{'corral_comps_num'} - 1) {
        next if $i == $cd->{'corral_sokoban_comp'};
        for my $j ($i + 1 .. $cd->{'corral_comps_num'} - 1) {
            next if $j == $cd->{'corral_sokoban_comp'};
            if ($cd->{'corral_candidates'}[$j] == 0) {
                next if $cd->{'corral_candidates'}[$i] == 0;
            }
            next if $touches_two_comps->[$i][$j] == 0;
            next if init_corral_with_comp($i, $j, $brd, $cd) == 0;
            next unless (expand_corral($brd, $cd) == 1);
            return (1, set_corral_options($brd, $cd));
        }
    }
    return (0, undef);
} ## end sub detect_corral

sub find_hotspots ($brd) {
    my ($h, $hotspot_weights);
    $h               = $ZERO_BOARD;
    $hotspot_weights = $ZERO_BOARD;
    my @boxes_indices = (grep {vec($brd, $Index_to_p[$_], 8) & BOX} 0 .. $Index_num - 1);
    for my $i (0 .. $#boxes_indices) {
        my $bp = $Index_to_p[$boxes_indices[$i]];
        for my $j (0 .. $#boxes_indices) {
            next if $j == $i;
            next unless (vec($Blocks_place, $boxes_indices[$j] * $Index_num + $boxes_indices[$i], 32));
            vec($h, $bp, 8) = 1;
            vec($hotspot_weights, $bp, 8)++;
        }
    }
    return ($h, $hotspot_weights);
} ## end sub find_hotspots

sub hotspots_score ($brd) {
    my ($h, $weights);
    ($h, $weights) = find_hotspots($brd);
    return unpack('%32C*', $h);
}

sub compute_match_distance ($brd, $base_score, $moves, $scores) {
    my $ctx;
    my (@mat, @newrow);
    my @boxes_indices = (grep {vec($brd, $Index_to_p[$_], 8) & BOX} 0 .. $Index_num - 1);
    my $boxes_num     = scalar @boxes_indices;
    my $targets_num   = scalar @Target_indices;
    Carp::confess('box num mismatch1') if $boxes_num != $targets_num;
    for my $i (0 .. $boxes_num - 1) {
        for my $j (0 .. $targets_num - 1) {
            $mat[$i][$j] = vec($Distance_from_to, $boxes_indices[$i] * $Index_num + $Target_indices[$j], 32);
        }
    }
    $ctx = Games::Sokoban::Solver::Munkres::context(\@mat);
    $base_score->{'dist_to_targets'} = $ctx->{'weight'};
    for my $t (0 .. $#$moves) {
        my $from = $moves->[$t]{'from'};
        my $to   = $moves->[$t]{'to'};
        $scores->[$t] //= {};
        if ($from == $to) {
            $scores->[$t]{'dist_to_targets'} = $base_score->{'dist_to_targets'};
            next;
        }
        my $row = $boxes_num;
        for my $i (0 .. $boxes_num - 1) {
            next unless ($boxes_indices[$i] == $from);
            $row = $i;
            last;
        }
        Carp::confess('internal error') if $row == $boxes_num;
        for my $j (0 .. $targets_num - 1) {
            $newrow[$j] = vec($Distance_from_to, $to * $Index_num + $Target_indices[$j], 32);
        }
        $scores->[$t]{'dist_to_targets'} =
            Games::Sokoban::Solver::Munkres::with_row($ctx, $row, \@newrow);
    } ## end for my $t (0 .. $#$moves)
    return;
} ## end sub compute_match_distance

sub compute_base_distance ($brd, $base_score, $moves, $scores) {
    my $ctx;
    my (@mat, @newrow);
    my @boxes_indices = (grep {vec($brd, $Index_to_p[$_], 8) & BOX} 0 .. $Index_num - 1);
    my $boxes_num     = scalar @boxes_indices;
    my $bases_num     = scalar @Base_indices;
    Carp::confess('box num mismatch3') if $boxes_num != $bases_num;
    for my $i (0 .. $boxes_num - 1) {
        for my $j (0 .. $bases_num - 1) {
            $mat[$i][$j] = vec($Distance_from_to, $Base_indices[$j] * $Index_num + $boxes_indices[$i], 32);
        }
    }
    $ctx = Games::Sokoban::Solver::Munkres::context(\@mat);
    $base_score->{'dist_to_targets'} = $ctx->{'weight'};
    for my $t (0 .. $#$moves) {
        my $from = $moves->[$t]{'from'};
        my $to   = $moves->[$t]{'to'};
        $scores->[$t] //= {};
        if ($from == $to) {
            $scores->[$t]{'dist_to_targets'} = $base_score->{'dist_to_targets'};
            next;
        }
        my $row = $boxes_num;
        for my $i (0 .. $boxes_num - 1) {
            next unless ($boxes_indices[$i] == $from);
            $row = $i;
            last;
        }
        Carp::confess('internal error') if $row == $boxes_num;
        for my $j (0 .. $bases_num - 1) {
            $newrow[$j] = vec($Distance_from_to, $Base_indices[$j] * $Index_num + $to, 32);
        }
        $scores->[$t]{'dist_to_targets'} =
            Games::Sokoban::Solver::Munkres::with_row($ctx, $row, \@newrow);
    } ## end for my $t (0 .. $#$moves)
    return;
} ## end sub compute_base_distance

sub compute_rev_distance ($brd, $base_score, $moves, $scores, $base_board, $from_to_mat) {
    my $ctx;
    my (@mat, @newrow);
    my @boxes_indices = (grep {vec($brd,        $Index_to_p[$_], 8) & BOX} 0 .. $Index_num - 1);
    my @bases_indices = (grep {vec($base_board, $Index_to_p[$_], 8) & BOX} 0 .. $Index_num - 1);
    my $boxes_num     = scalar @boxes_indices;
    my $bases_num     = scalar @bases_indices;
    Carp::confess('box num mismatch4') if $boxes_num != $bases_num;
    for my $i (0 .. $boxes_num - 1) {
        for my $j (0 .. $bases_num - 1) {
            $mat[$i][$j] =
                vec($from_to_mat, $bases_indices[$j] * $Index_num + $boxes_indices[$i], 32);
        }
    }
    $ctx = Games::Sokoban::Solver::Munkres::context(\@mat);
    $base_score->{'dist_to_imagined'} = $ctx->{'weight'};
    for my $t (0 .. $#$moves) {
        my $from = $moves->[$t]{'from'};
        my $to   = $moves->[$t]{'to'};
        $scores->[$t] //= {};
        if ($from == $to) {
            $scores->[$t]{'dist_to_imagined'} = $base_score->{'dist_to_imagined'};
            next;
        }
        my $row = $boxes_num;
        for my $i (0 .. $boxes_num - 1) {
            next unless ($boxes_indices[$i] == $from);
            $row = $i;
            last;
        }
        Carp::confess('internal error') if $row == $boxes_num;
        for my $j (0 .. $bases_num - 1) {
            $newrow[$j] =
                vec($from_to_mat, $bases_indices[$j] * $Index_num + $to, 32);
        }
        $scores->[$t]{'dist_to_imagined'} =
            Games::Sokoban::Solver::Munkres::with_row($ctx, $row, \@newrow);
    } ## end for my $t (0 .. $#$moves)
    return;
} ## end sub compute_rev_distance

sub get_parked_boxes ($step, $h) {
    my $parked;
    my $init_num      = 0;
    my $parking_order = $h->{'parking_order'};
    $parked = $ZERO_BOARD;
    for my $i (0 .. $h->{'parking_order_num'} - 1) {
        $init_num++ if $parking_order->[$i]{'from'} == -2;
    }
    if ($step < $init_num) {
        $step = $init_num;
    }
    for my $i (0 .. $step - 1) {
        next unless ($parking_order->[$i]{'until'} == -1 or $parking_order->[$i]{'until'} >= $step);
        vec($parked, $Index_to_p[$parking_order->[$i]{'to'}], 8) = 1;
    }
    return $parked;
} ## end sub get_parked_boxes

sub get_oop_zone_for_step ($step, $h) {
    my ($parked_boxes, $next_targets, $brd, $sources, $oop);
    my $parking_order = $h->{'parking_order'};
    $parked_boxes = $ZERO_BOARD;
    for my $i (0 .. $step) {
        next unless ($parking_order->[$i]{'until'} == -1);
        vec($parked_boxes, $Index_to_p[$parking_order->[$i]{'to'}], 8) = 1;
    }
    $next_targets = $ZERO_BOARD;
    for my $i ($step + 1 .. $h->{'parking_order_num'} - 1) {
        vec($next_targets, $Index_to_p[$parking_order->[$i]{'to'}], 8) = 1;
    }
    $brd = $Initial_board&.$NOT_BOX;
    for my $p (0 .. $Ncells - 1) {
        vec($brd, $p, 8) = WALL if vec($parked_boxes, $p, 8);
    }
    $sources = find_sources_of_a_board_input($brd, $next_targets);
    $oop     = $ZERO_BOARD;
    for my $p (0 .. $Ncells - 1) {
        next if vec($Inner, $p, 8) == 0;
        next if vec($brd,   $p, 8) == WALL;
        next if $Impossible_place[$Y_x_to_index_table[$p]] == 1;
        next if vec($sources, $p, 8);
        vec($oop, $p, 8) = 1;
    }
    return $oop;
} ## end sub get_oop_zone_for_step

sub set_oop_zones_range ($val, $from, $to, $h) {
    Carp::confess('missing oop') unless defined $h->{'oop'};
    my $oop_zone_for_step = $h->{'oop'}{'oop_zone_for_step'} //= [];
    for my $i ($from .. $to - 1) {
        $oop_zone_for_step->[$i] = $val;
    }
    return;
}

sub get_oop_distance_for_step ($step, $h) {
    my ($parked, $empty_board);
    Carp::confess('missing oop1') unless defined $h->{'oop'};
    my $oop_zone_for_step = $h->{'oop'}{'oop_zone_for_step'};
    $parked      = get_parked_boxes($step, $h);
    $empty_board = $Initial_board&.$NOT_BOX;
    for my $p (0 .. $Ncells - 1) {
        vec($empty_board, $p, 8) = WALL if vec($parked, $p, 8);
    }
    my $oop_dist = [];
    find_distance_from_a_group($empty_board, $oop_zone_for_step->[$step], $oop_dist, 0);
    return $oop_dist;
}

sub prepare_oop_zones ($h) {
    Carp::confess('missing oop2') unless defined $h->{'oop'};
    my $oop_zone_for_step          = $h->{'oop'}{'oop_zone_for_step'} //= [];
    my $oop_zone_distance_for_step = $h->{'oop'}{'oop_zone_distance_for_step'} //=
        [];
    for my $i (0 .. $h->{'parking_order_num'} - 2) {
        $oop_zone_for_step->[$i] = get_oop_zone_for_step($i, $h);
    }
    my $current_board;
    $current_board = $ZERO_BOARD;
    my $last_modified = 0;
    for my $i (0 .. $h->{'parking_order_num'} - 2) {
        next if ($oop_zone_for_step->[$i] eq $current_board ? 1 : 0);
        $current_board = $oop_zone_for_step->[$i];
        set_oop_zones_range($current_board, $last_modified, $i + 1, $h);
        $last_modified = $i;
    }
    for my $i (0 .. $h->{'parking_order_num'} - 2) {
        $oop_zone_distance_for_step->[$i] = get_oop_distance_for_step($i, $h);
    }
    return;
} ## end sub prepare_oop_zones

sub count_boxes_in_oop_zone ($brd, $oop) {
    my $sum = 0;
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($oop, $p, 8));
        $sum++ if vec($brd, $p, 8) & BOX;
    }
    return $sum;
}

sub get_out_of_plan_score ($brd, $parked_num, $h) {
    Carp::confess('missing oop3') unless defined $h->{'oop'};
    my $oop_zone_for_step = $h->{'oop'}{'oop_zone_for_step'};
    my $res               = count_boxes_in_oop_zone($brd, $oop_zone_for_step->[$parked_num]);
    return $res;
}

sub new_oop_advisor ($brd, $base_score, $moves_num, $moves, $scores, $pull_mode, $h) {
    my $best_move = -1;
    my $min_from  = 1000000;
    my $max_to    = -1;
    my $step      = $base_score->{'packed_boxes'};
    Carp::confess('missing oop') unless defined $h->{'oop'};
    my $oop_zone_distance_for_step = $h->{'oop'}{'oop_zone_distance_for_step'};
    return -1 if $base_score->{'out_of_plan'} == 0;
    my $min_connect = $base_score->{'connectivity'};
    my $min_rooms   = $base_score->{'rooms_score'};

    for my $i (0 .. $moves_num - 1) {
        next if $scores->[$i]{'connectivity'} > $min_connect;
        next if $scores->[$i]{'rooms_score'} > $min_rooms;
        next if $scores->[$i]{'out_of_plan'} > $base_score->{'out_of_plan'};
        next if $scores->[$i]{'packed_boxes'} < $base_score->{'packed_boxes'};
        my $from = $moves->[$i]{'from'};
        my $to   = $moves->[$i]{'to'};
        next if vec($Distance_from_to, $to * $Index_num + $from, 32) == 1000000;
        my $from_dist = $oop_zone_distance_for_step->[$step][$Index_to_p[$from]];
        my $to_dist   = $oop_zone_distance_for_step->[$step][$Index_to_p[$to]];
        next if $from_dist == 1000000;
        next if $to_dist == 1000000;
        next if $to_dist <= $from_dist;
        next if $from_dist > $min_from;

        if ($from_dist < $min_from) {
            $min_from  = $from_dist;
            $max_to    = $to_dist;
            $best_move = $i;
        }
        next unless ($from_dist == $min_from);
        if ($to_dist > $max_to) {
            $max_to    = $to_dist;
            $best_move = $i;
        }
    } ## end for my $i (0 .. $moves_num...)
    return $best_move;
} ## end sub new_oop_advisor

sub box_can_be_moved ($brd, $index, $pull_mode) {
    my $p = $Index_to_p[$index];
    if ($pull_mode == 0) {
        for my $i (0 .. 3) {
            next if vec($brd, $p + $Delta_p[$i], 8) & OCCUPIED;
            next if (vec($brd, $p - $Delta_p[$i], 8) & SOKOBAN) == 0;
            next if deadlock_in_direction($brd, $p, $i);
            return 1;
        }
        return 0;
    }
    for my $i (0 .. 3) {
        next if (vec($brd, $p + $Delta_p[$i], 8) & SOKOBAN) == 0;
        next if vec($brd, $p + 2 * $Delta_p[$i], 8) & OCCUPIED;
        return 1;
    }
    return 0;
} ## end sub box_can_be_moved

sub find_box_moves ($brd, $index, $pull_mode, $search_mode, $possible_board, $gd) {
    Carp::confess("box can't be moved")
        if box_can_be_moved($brd, $index, $pull_mode) == 0;
    my $p = $Index_to_p[$index];
    set_current_impossible($brd, $p, $pull_mode, $search_mode, $possible_board, $gd);
    mark_box_moves_in_graph($brd, $index, $pull_mode, $gd);
    find_reversible_moves($brd, $index, $pull_mode, $gd)
        if $search_mode == NORMAL or $search_mode == WOBBLERS_SEARCH;
    my @moves = get_box_moves_from_graph($index, $gd);
    $_->{'pull'} = $pull_mode for @moves;
    return @moves;
}

sub move_pack ($m) {
    return $m->{'from'} | $m->{'to'} << 12 | $m->{'sokoban_position'} << 24
        | ($m->{'kill'} ? 1 << 26 : 0) | ($m->{'base'} ? 1 << 27 : 0) | ($m->{'pull'} ? 1 << 28 : 0)
        | ($m->{'attr'}{'reversible'} ? 1 << 29 : 0) | ($m->{'attr'}{'weight'} + 1) << 30;
}

sub move_unpack ($v) {
    return {
        'from'             => $v & 0xFFF,
        'to'               => $v >> 12 & 0xFFF,
        'sokoban_position' => $v >> 24 & 3,
        'kill'             => $v >> 26 & 1,
        'base'             => $v >> 27 & 1,
        'pull'             => $v >> 28 & 1,
        'attr'             => {'weight' => ($v >> 30 & 3) - 1, 'advisor' => 0, 'reversible' => $v >> 29 & 1},
    };
}

sub apply_move ($brd, $m, $search_type) {
    Carp::confess('search type not initialized') if $search_type == -1;
    if ($m->{'kill'}) {
        my $p2 = $Index_to_p[$m->{'from'}];
        vec($brd, $p2, 8) &= 0xFF ^ BOX;
        $brd = expand_sokoban_cloud($brd);
        $brd = update_deadlock_zone($brd, $m->{'pull'})
            if $search_type == DEADLOCK_SEARCH;
        return $brd;
    }
    $brd&.=$NOT_SOKOBAN;
    my $p = $Index_to_p[$m->{'from'}];
    Carp::confess('missing box2') if (vec($brd, $p, 8) & BOX) == 0;
    vec($brd, $p, 8) &= 0xFF ^ BOX;
    $p = $Index_to_p[$m->{'to'}];
    Carp::confess('occupied place') if vec($brd, $p, 8) & OCCUPIED;
    vec($brd, $p, 8) |= BOX;

    if ($m->{'base'} == 1) {
        vec($brd, $p, 8) &= 0xFF ^ BOX;
        Carp::confess('no base in apply') if (vec($brd, $p, 8) & BASE) == 0;
        vec($brd, $p, 8) &= 0xFF ^ BASE;
    }
    my $sok_p = $p + $Delta_p[$m->{'sokoban_position'}];
    vec($brd, $sok_p, 8) |= SOKOBAN;
    $brd = expand_sokoban_cloud($brd, $sok_p);
    $brd = update_deadlock_zone($brd, $m->{'pull'}) if $search_type == DEADLOCK_SEARCH;
    return $brd;
} ## end sub apply_move

sub is_pull_mpdb_deadlock ($brd) {
    for my $pair (@Pull_mpdb_list) {
        my $p = $Index_to_p[$pair->[0]];
        next if (vec($brd, $p, 8) & BOX) == 0;
        $p = $Index_to_p[$pair->[1]];
        next if (vec($brd, $p, 8) & BOX) == 0;
        return 1;
    }
    return 0;
}

sub is_mpdb_deadlock ($brd, $pull_mode) {
    return is_pull_mpdb_deadlock($brd) if $pull_mode;
    for my $pair (@Mpdb_list) {
        my $p = $Index_to_p[$pair->[0]];
        next if (vec($brd, $p, 8) & BOX) == 0;
        $p = $Index_to_p[$pair->[1]];
        next if (vec($brd, $p, 8) & BOX) == 0;
        return 1;
    }
    return 0;
}

sub init_scored_distance ($brd, $pull_mode, $h) {
    if ($pull_mode == 0) {
        get_distance_from_targets($brd, $h->{'scored_distance'});
        return;
    }
    @{ $h->{'scored_distance'} } = (0) x $Ncells;
    for my $from (0 .. $Index_num - 1) {
        my $from_p = $Index_to_p[$from];
        for my $to (0 .. $Index_num - 1) {
            my $to_p = $Index_to_p[$to];
            next unless (vec($brd, $to_p, 8) & TARGET);
            $h->{'scored_distance'}[$from_p] += vec($Distance_from_to, $from * $Index_num + $to, 32)
                if vec($Distance_from_to, $from * $Index_num + $to, 32) != 1000000;
        }
    }
    return;
} ## end sub init_scored_distance

sub get_scored_distance ($brd, $h) {
    my $sum = 0;
    for my $p (0 .. $Ncells - 1) {
        $sum += $h->{'scored_distance'}[$p] if vec($brd, $p, 8) & BOX;
    }
    return $sum;
}

sub simple_pull_box_eliminator ($brd) {
    my $changed = 0;
    for my $p (0 .. $Ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;
        for my $k (0 .. 3) {
            my $sp = $p + $Delta_p[$k];
            next if (vec($brd, $sp, 8) & SOKOBAN) == 0;
            my $tp = $p + 2 * $Delta_p[$k];
            next if vec($brd, $tp, 8) & OCCUPIED;
            vec($brd, $p, 8) &= 0xFF ^ BOX;
            vec($brd, $p, 8) |= SOKOBAN;
            $changed = 1;
            last;
        }
    }
    return ($changed, $brd);
} ## end sub simple_pull_box_eliminator

sub back_eliminate_loop ($brd) {
    my $res;
    do {
        ($res, $brd) = simple_pull_box_eliminator($brd);
        $brd = expand_sokoban_cloud($brd) if $res;
    } while ($res);
    return $brd;
}

sub eliminate_from_zone ($base, $final_pos, $zones, $z) {
    my $e = $final_pos;
    $e = put_sokoban_in_zone($e, $zones, $z);
    $e = back_eliminate_loop($e);
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($e, $p, 8) & BOX);
        return 0 if (vec($base, $p, 8) & BOX) == 0;
    }
    return 1;
}

sub try_pulling_all_zones ($b_in) {
    my ($brd, $final);
    my @zones;
    $brd   = turn_fixed_boxes_into_walls($b_in);
    $final = $brd&.$NOT_BOX;
    $final = turn_targets_into_packed($final);
    my $zones_num = mark_connectivities($final, \@zones);
    for my $i (0 .. $zones_num - 1) {
        return 1 if eliminate_from_zone($brd, $final, \@zones, $i) == 1;
    }
    return 0;
}

sub free_pull_deadlock ($b_in) {
    my $brd = $b_in;
    $brd = back_eliminate_loop($brd);
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($brd, $p, 8) & BOX);
        return 1 if (vec($Initial_board, $p, 8) & BOX) == 0;
    }
    return 0;
}

sub can_played_reversed ($brd, $m, $pull_mode, $search_mode) {
    return 1                  if $search_mode != BASE_SEARCH;
    Carp::confess('bad call') if $pull_mode == 0;
    return 1                  if $search_mode == GIRL_SEARCH;
    my $c = $brd;
    $c = apply_move($c, $m, NORMAL);
    return 1 if board_is_solved($c, 1);
    my $p = $Index_to_p[$m->{'to'}];
    if (get_connectivity($c) > 1) {
        my ($w, $corral_options);
        $c&.=$NOT_BASE;
        $w = turn_fixed_boxes_into_walls($c);
        (my $has_c, $corral_options) = detect_corral($w);
        if ($has_c) {
            return 0 if $m->{'base'};
            return 0 if (vec($corral_options, $p, 8) & BOX) == 0;
        }
    }
    return 1;
} ## end sub can_played_reversed

sub check_matching_deadlock ($b_in, $pull_mode, $search_mode) {
    my (@box_places, @target_places);
    my @cost;
    my $sol = {};
    return 0 if $search_mode == DRAGONFLY;
    my $has_bases = 0;
    for my $p (0 .. $Ncells - 1) {
        $has_bases = 1 if vec($b_in, $p, 8) & BASE;
    }
    my $brd;
    if ($pull_mode == 0) {
        $brd = turn_fixed_boxes_into_walls($b_in);
        for my $i (0 .. $Index_num - 1) {
            my $p2 = $Index_to_p[$i];
            my $c  = vec($brd, $p2, 8);
            push @box_places,    $i if $c & BOX;
            push @target_places, $i if $c & TARGET;
        }
    }
    else {
        for my $i (0 .. $Index_num - 1) {
            my $p = $Index_to_p[$i];
            if ($has_bases == 0) {
                push @box_places, $i if vec($Initial_board, $p, 8) & BOX;
            }
            else {
                push @box_places, $i if vec($b_in, $p, 8) & BASE;
            }
            push @target_places, $i if vec($b_in, $p, 8) & BOX;
        }
    }
    my $box_num    = scalar @box_places;
    my $target_num = scalar @target_places;
    if ($pull_mode == 0) {
        return 1 if $box_num != $target_num;
    }
    for my $i (0 .. $box_num - 1) {
        for my $j (0 .. $box_num - 1) {
            $cost[$i][$j] = 1;
        }
    }
    if ($pull_mode == 0) {
        my $gd = allocate_graph();
        my $empty;
        $empty = $brd&.$NOT_BOX;
        build_graph($empty, 0, $gd);
        make_holes_inactive($brd, $gd);
        for my $i (0 .. $box_num - 1) {
            my $p2 = $Index_to_p[$box_places[$i]];
            my $targets;
            $targets = find_targets_of_place_without_init_graph($p2, $gd);
            for my $j (0 .. $target_num - 1) {
                $p2 = $Index_to_p[$target_places[$j]];
                $cost[$i][$j] = 0 if vec($targets, $p2, 8);
            }
        }
    } ## end if ($pull_mode == 0)
    else {
        for my $i (0 .. $box_num - 1) {
            for my $j (0 .. $target_num - 1) {
                $cost[$i][$j] = 0
                    if vec($Distance_from_to, $box_places[$i] * $Index_num + $target_places[$j], 32) < 1000000;
            }
        }
    }
    my $weight = Games::Sokoban::Solver::Munkres::assign(\@cost);
    if ($pull_mode == 0) {
        return 0 if $weight == 0;
    }
    else {
        return 0 if $weight == $box_num - $target_num;
    }
    return 1;
} ## end sub check_matching_deadlock

sub verify_simple_base_matching ($brd, $board_with_bases) {
    my (@box_places, @bases_places);
    for my $i (0 .. $Index_num - 1) {
        my $p = $Index_to_p[$i];
        push @bases_places, $i if vec($board_with_bases, $p, 8) & BASE;
        push @box_places,   $i if vec($brd,              $p, 8) & BOX;
    }
    if (@bases_places != @box_places) {
        Carp::confess('Num box mismatch');
    }
    for my $base_index (@bases_places) {
        my $found = 0;
        for my $box_index (@box_places) {
            next unless (vec($Distance_from_to, $base_index * $Index_num + $box_index, 32) != 1000000);
            $found = 1;
            last;
        }
        return 0 unless $found;
    }
    return 1;
} ## end sub verify_simple_base_matching

sub discard_advisors_in_base_search ($moves, $l) {
    return if $l->{'pack'} == -1;
    if ($moves->[$l->{'pack'}]{'base'}) {
        $l->{'connectivity'} = -1;
        $l->{'rooms'}        = -1;
        $l->{'hotspots'}     = -1;
        $l->{'opener'}       = -1;
        $l->{'out_of_plan'}  = -1;
        $l->{'explorer'}     = -1;
        $l->{'imagine'}      = -1;
    }
    return;
}

sub is_an_advisor ($adv, $son) {
    for my $v (unpack 'l8', $adv) {
        return 1 if $v == $son;
    }
    return 0;
}

sub score_pack ($s) {
    return pack 'd13', @{$s}{ @{ +SCORE_KEYS } };
}

sub score_hash ($t, $place) {
    my %s;
    @s{ @{ +SCORE_KEYS } } = unpack 'd13', $t->{'node_score'}[$place];
    return \%s;
}

sub score_field ($t, $place, $i) {
    return unpack 'd', substr($t->{'node_score'}[$place], 8 * $i, 8);
}

sub score_set ($t, $place, $i, $v) {
    substr($t->{'node_score'}[$place], 8 * $i, 8) = pack 'd', $v;
    return;
}

sub get_hash_without_bases ($t, $e, $son) {
    my $brd;
    return 0xFFFFFFFF
        if score_field($t, $e->{'node'}, SC_BOXES_IN_LEVEL) != $Global_boxes_in_level;
    if ($son == -1) {
        $brd = $e->{'b'};
        $brd&.=$NOT_BASE;
        return get_board_hash($brd);
    }
    my $mhi   = $e->{'move_hash_place'} + $son;
    my $place = $t->{'mh_node'}[$mhi];
    return 0xFFFFFFFF
        if score_field($t, $place, SC_BOXES_IN_LEVEL) != $Global_boxes_in_level;
    $brd = $e->{'b'};
    $brd = apply_move($brd, move_unpack($t->{'mh_move'}[$mhi]), NORMAL);
    $brd&.=$NOT_BASE;
    return get_board_hash($brd);
} ## end sub get_hash_without_bases

sub update_perimeter ($hash, $depth, $pull_mode, $alg) {
    my $v = $Perimeter{$hash};
    if (($v & 255) == DRAGONFLY) {
        $Perimeter{$hash} = $depth << 16 | ($v & 0xFFFF) if $pull_mode and $depth < $v >> 16;
        return;
    }
    if ((($v >> 8) & 255) == $pull_mode) {
        $Perimeter{$hash} = $depth << 16 | $pull_mode << 8 | ($alg & 255) if $depth < $v >> 16;
        return;
    }
    return if (($v >> 8) & 255) == 1;
    $Perimeter{$hash} = $depth << 16 | $pull_mode << 8 | ($alg & 255);
    return;
} ## end sub update_perimeter

sub perimeter_is_full () {
    my $limit = 1 << ($Log_perimeter_size - 1);
    return 0 if $Total_perimeter_entries < $limit;
    return 1;
}

sub insert_node_into_perimeter ($t, $e, $with_sons) {
    my $perimeter_entries = 0;
    return 0 if perimeter_is_full();
    my $hash =
        $t->{'search_mode'} == BASE_SEARCH
        ? get_hash_without_bases($t, $e, -1)
        : $t->{'node_hash'}[$e->{'node'}];
    my $tag = $t->{'pull_mode'} << 8 | ($t->{'search_mode'} & 255);
    if (not exists $Perimeter{$hash}) {
        $Perimeter{$hash} = $e->{'depth'} << 16 | $tag;
        $perimeter_entries++;
        $Total_perimeter_entries++;
    }
    else {
        update_perimeter($hash, $e->{'depth'}, $t->{'pull_mode'}, $t->{'search_mode'});
        $perimeter_entries++;
    }
    return $perimeter_entries if $with_sons == 0;
    my $mh_node = $t->{'mh_node'};
    my $mp      = $e->{'move_hash_place'};
    for my $j (0 .. $e->{'moves_num'} - 1) {
        $hash =
            $t->{'search_mode'} == BASE_SEARCH
            ? get_hash_without_bases($t, $e, $j)
            : $t->{'node_hash'}[ $mh_node->[$mp + $j] ];
        if (not exists $Perimeter{$hash}) {
            $Perimeter{$hash} = ($e->{'depth'} + 1) << 16 | $tag;
            $perimeter_entries++;
            $Total_perimeter_entries++;
        }
        else {
            update_perimeter($hash, $e->{'depth'} + 1, $t->{'pull_mode'}, $t->{'search_mode'});
            $perimeter_entries++;
        }
    } ## end for my $j (0 .. $e->{'moves_num'...})
    return $perimeter_entries;
} ## end sub insert_node_into_perimeter

sub is_in_perimeter ($hash, $depth_ref, $side) {
    my $v = $Perimeter{$hash};
    if (defined $v and (($v >> 8) & 255) == $side) {
        $$depth_ref = $v >> 16;
        return 1;
    }
    return 0;
}

sub dragonfly_mark_visited_hashes ($hashes, $n, $visited) {
    for my $i (0 .. $n - 1) {
        my $v = $Perimeter{ $hashes->[$i] };
        if (defined $v and ($v & 255) == DRAGONFLY) {
            $visited->[$i] = 1;
            next;
        }
        if (defined $v and (($v >> 8) & 255) == 0) {
            $visited->[$i] = -2000 + ($v >> 16);
            next;
        }
        $visited->[$i] = 0;
    }
    return;
} ## end sub dragonfly_mark_visited_hashes

sub dragonfly_update_perimeter ($hashes, $visited, $n, $depth) {
    my $tag = 1 << 8 | DRAGONFLY;
    for my $i (0 .. $n - 1) {
        next if $visited->[$i] == 1;
        my $v = $Perimeter{ $hashes->[$i] };
        if (defined $v and (($v >> 8) & 255) == 1) {
            $Perimeter{ $hashes->[$i] } = ($depth < $v >> 16 ? $depth : $v >> 16) << 16 | $tag;
            next;
        }
        $Perimeter{ $hashes->[$i] } = $depth << 16 | $tag;
        $Total_perimeter_entries++;
    }
    return;
}

sub position_is_solved ($p) {
    my $brd = $p->{'board'};
    if ($p->{'search_mode'} == DEADLOCK_SEARCH and $p->{'pull_mode'} == 0) {
        return work_left_in_deadlock_zone($brd) ^ 1;
    }
    return 0 if $p->{'search_mode'} == DEADLOCK_SEARCH and $p->{'pull_mode'};
    return board_is_solved($brd, $p->{'pull_mode'});
}

sub mark_deadlocks ($positions, $pos_num) {
    my $changed;
    do {
        $changed = 0;
        for my $i (0 .. $pos_num - 1) {
            my $pi = $positions->[$i];
            next if $pi->{'position_deadlocked'};
            for my $j (0 .. $pi->{'moves_num'} - 1) {
                my $t = $pi->{'place_in_positions'}[$j];
                next unless (defined $t and $pi->{'move_deadlocked'}[$j] == 0 and $t->{'position_deadlocked'});
                $pi->{'move_deadlocked'}[$j] = 1;
                $changed = 1;
            }
            my $all = 1;
            for my $j (0 .. $pi->{'moves_num'} - 1) {
                next unless ($pi->{'move_deadlocked'}[$j] == 0);
                $all = 0;
                last;
            }
            next unless ($all);
            if (position_is_solved($pi) == 0) {
                $pi->{'position_deadlocked'} = 1;
                $changed = 1;
            }
        } ## end for my $i (0 .. $pos_num...)
    } while ($changed == 1);
    return;
} ## end sub mark_deadlocks

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
        if (substr($brd, 0, ($Height * $Width)) eq substr($next->{'board'}, 0, ($Height * $Width)) ? 1 : 0) == 0;
    return;
}

sub set_place_in_positions ($p, $positions, $pos_num) {
    my %pos_by_hash;
    for my $i (0 .. $pos_num - 1) {
        $pos_by_hash{ $positions->[$i]{'position_hash'} } = $positions->[$i];
    }
    for my $j (0 .. $p->{'moves_num'} - 1) {
        my $t = $pos_by_hash{ $p->{'hashes'}[$j] };
        $p->{'place_in_positions'}[$j] = $t;
        next unless defined $t;
        assert_board_after_move($p, $j, $t);
        $p->{'move_deadlocked'}[$j] = 1 if $t->{'position_deadlocked'};
    }
    return;
}

sub allocate_position_structures ($p) {
    $p->{'moves'}              = [];
    $p->{'hashes'}             = [];
    $p->{'scores'}             = [];
    $p->{'place_in_positions'} = [];
    $p->{'move_deadlocked'}    = [];
    return;
}

sub set_hash_indicators ($p) {
    $p->{'hash_indicators'} = [(0) x 64];
    for my $i (0 .. $p->{'moves_num'} - 1) {
        my $upper = ($p->{'hashes'}[$i] >> 52) & 0xFFF;
        $p->{'hash_indicators'}[$upper >> 6] |= 1 << ($upper & 0x3F);
    }
    return;
}

sub direct_other_sons_to_position ($pos, $positions, $pos_num) {
    my $hash  = $pos->{'position_hash'};
    my $upper = ($hash >> 52) & 0xFFF;
    my $lower = $upper & 0x3F;
    $upper >>= 6;
    for my $i (0 .. $pos_num - 1) {
        my $p = $positions->[$i];
        next unless ($p->{'hash_indicators'}[$upper] >> $lower) & 1;
        for my $j (0 .. $p->{'moves_num'} - 1) {
            next if $p->{'hashes'}[$j] != $hash;
            next if defined $p->{'place_in_positions'}[$j];
            $p->{'place_in_positions'}[$j] = $pos;
            assert_board_after_move($p, $j, $pos);
        }
    }
    return;
} ## end sub direct_other_sons_to_position

sub all_sons_are_deadlocked ($p) {
    for my $i (0 .. $p->{'moves_num'} - 1) {
        next if $p->{'move_deadlocked'}[$i];
        my $q = $p->{'place_in_positions'}[$i];
        return 0 unless defined $q;
        Carp::confess('move_deadlocked error') if $q->{'position_deadlocked'};
        return 0                               if $q->{'position_deadlocked'} == 0;
    }
    return 1;
}

sub set_leaf_as_deadlock ($positions, $pos_num, $pos, $son) {
    my $node_changed = 0;
    my $hash         = $positions->[$pos]{'hashes'}[$son];
    my $upper        = ($hash >> 52) & 0xFFF;
    my $lower        = $upper & 0x3F;
    $upper >>= 6;
    for my $i (0 .. $pos_num - 1) {
        my $pi = $positions->[$i];
        next if $pi->{'position_deadlocked'};
        next unless ($pi->{'hash_indicators'}[$upper] >> $lower) & 1;
        my $n = $pi->{'moves_num'};
        for my $j (0 .. $n - 1) {
            next if $pi->{'hashes'}[$j] != $hash;
            $pi->{'move_deadlocked'}[$j] = 1;
            if ($i != $pos) {
                Carp::confess('leaf should not be expanded')
                    if defined $pi->{'place_in_positions'}[$j];
            }
            my $all = 1;
            for my $k (0 .. $n - 1) {
                next unless ($pi->{'move_deadlocked'}[$k] == 0);
                $all = 0;
                last;
            }
            $node_changed = 1 if $all;
        } ## end for my $j (0 .. $n - 1)
    } ## end for my $i (0 .. $pos_num...)
    mark_deadlocks($positions, $pos_num) if $node_changed;
    return;
} ## end sub set_leaf_as_deadlock

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

sub init_queue ($q, $t) {
    $q->{'elements'}  = [];
    $q->{'heap_size'} = 0;
    $q->{'t'}         = $t;
    return;
}

sub find_sol_move ($b_in, $start_sok_index, $start_box_index, $end_sok_index, $end_box_index) {
    my (@current, @next, @src);
    my $space_size = $Index_num * $Index_num;
    my $brd        = $b_in;
    my $box_p      = $Index_to_p[$start_box_index];
    Carp::confess('missing box1')
        if (vec($brd, $box_p, 8) & BOX) == 0;
    vec($brd, $box_p, 8) &= 0xFF ^ BOX;
    @src = (-1) x $space_size;
    my $target_index = $start_sok_index * $Index_num + $start_box_index;
    $current[0] = $end_sok_index * $Index_num + $end_box_index;
    $src[$current[0]] = $current[0];

    while (@current) {
        @next = ();
        for my $current_index (@current) {
            my $sok_index = int($current_index / $Index_num);
            my $box_index = $current_index % $Index_num;
            my $sok_p     = $Index_to_p[$sok_index];
            my $bp        = $Index_to_p[$box_index];
            for my $j (0 .. 3) {
                my $next_sok_p = $sok_p + $Delta_p[$j];
                next if $next_sok_p == $bp;
                next if vec($brd, $next_sok_p, 8) & OCCUPIED;
                my $next_index = $Y_x_to_index_table[$next_sok_p] * $Index_num + $box_index;
                next if $src[$next_index] != -1;
                $src[$next_index] = $current_index;
                push @next, $next_index;
            }
            for my $j (0 .. 3) {
                next if $bp + $Delta_p[$j] != $sok_p;
                my $next_sok_p = $sok_p + $Delta_p[$j];
                next if vec($brd, $next_sok_p, 8) & OCCUPIED;
                my $next_index = $Y_x_to_index_table[$next_sok_p] * $Index_num + $sok_index;
                next if $src[$next_index] != -1;
                $src[$next_index] = $current_index;
                push @next, $next_index;
            }
        } ## end for my $current_index (...)
        @current = @next;
        last if $src[$target_index] != -1;
    } ## end while (@current)
    my $current_index = $target_index;
    Carp::confess('could not find path') if $src[$current_index] == -1;
    my $next_index = $src[$current_index];
    my $moves      = '';
    while ($next_index != $current_index) {
        my $diff = $Index_to_p[int($next_index / $Index_num)] - $Index_to_p[int($current_index / $Index_num)];
        my $m =
              $diff == $Width  ? 'd'
            : $diff == -$Width ? 'u'
            : $diff == 1       ? 'r'
            : $diff == -1      ? 'l'
            :                    Carp::confess('move error');
        $m = uc $m if $current_index % $Index_num != $next_index % $Index_num;
        $moves .= $m;
        $current_index = $next_index;
        $next_index    = $src[$current_index];
    }
    return $moves;
} ## end sub find_sol_move

sub find_in_k_dist_hash ($hash) {
    for my $i (0 .. $K_dist_hash_num - 1) {
        return $i if $K_dist_hash[$i]{'hash'} == $hash;
    }
    return -1;
}

sub insert_to_k_dist_hash ($hash, $w, $forced, $adj_4, $adj_9) {
    my $n = $K_dist_hash_num;
    return if $n >= MAX_K_DIST_HASH_SIZE;
    $K_dist_hash[$n] = {
        'hash'   => $hash,
        'b'      => $w,
        'forced' => $forced,
        'adj_4'  => $adj_4,
        'adj_9'  => $adj_9,
    };
    $K_dist_hash_num++;
    return;
}

sub sokoban_touches_a_filled_hole ($brd) {
    my $p = get_sokoban_position($brd);
    for my $i (0 .. 3) {
        my $q = $p + $Delta_p[$i];
        next unless (vec($brd, $q, 8) == WALL);
        return 1 if vec($Initial_board, $q, 8) != WALL;
    }
    return 0;
}

sub has_pull_continuation ($brd, $search_mode) {
    my $all_boxes_solved = all_boxes_in_place($brd, 1);
    if (vec($brd, $Initial_sokoban_p, 8) & SOKOBAN) {
        return 1 if $all_boxes_solved;
    }
    if ($search_mode == K_DIST_SEARCH) {
        return 1 if (($brd&.$SOK_ONLY) =~ tr/\x00//c) > 1;
        return 1
            if sokoban_touches_a_filled_hole($brd);
        return 0;
    }
    for my $p (0 .. $Ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;
        for my $k (0 .. 3) {
            my $sp = $p + $Delta_p[$k];
            next     if (vec($brd, $sp,                8) & SOKOBAN) == 0;
            return 1 if (vec($brd, $sp + $Delta_p[$k], 8) & OCCUPIED) == 0;
        }
    }
    return 0;
} ## end sub has_pull_continuation

sub check_deadlock_in_moves ($b_in, $moves, $pull_mode, $search_mode, $h) {
    my @valid;
    my $brd = $b_in;
    $search_mode = NORMAL if $search_mode == DEADLOCK_SEARCH;
    $brd&.=$NOT_BASE if $pull_mode;
    my @elim = (0) x $Index_num;
    if ($pull_mode and $search_mode == BASE_SEARCH) {
        for my $p (0 .. $Ncells - 1) {
            $elim[$Y_x_to_index_table[$p]] = 1 if vec($b_in, $p, 8) & BASE;
        }
    }
    for my $i (0 .. $#$moves) {
        $valid[$i] = 1;
        if ($moves->[$i]{'kill'} == 1) {
            next;
        }
        my $dest   = $moves->[$i]{'to'};
        my $dest_p = $Index_to_p[$dest];
        next if $pull_mode and $elim[$dest];
        if ($Impossible_place[$dest]) {
            $valid[$i] = 0;
            next;
        }
        my $blok_first =
               $BLOK_REPLACES
            && $Blok_usable
            && $pull_mode == 0
            && $search_mode != DEADLOCK_SEARCH
            && $search_mode != BASE_SEARCH;
        if ($blok_first
            and blok_forbids($moves->[$i]))
        {
            $valid[$i] = 0;
            next;
        }
        my $c = $brd;
        $c = apply_move($c, $moves->[$i], $search_mode);
        if (!$blok_first and is_mpdb_deadlock($c, $pull_mode)) {
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
                Carp::confess('should not be here');
            }
            my $res = check_all_patterns($c, $dest_p, 1);
            if ($res != -1) {
                $valid[$i] = 0;
                next;
            }
            if ($search_mode == BASE_SEARCH) {
                if (verify_simple_base_matching($c, $b_in) == 0) {
                    $valid[$i] = 0;
                    next;
                }
            }
            next;
        } ## end if ($pull_mode)
        next if $blok_first;
        if (is_freeze_deadlock($c, $dest_p)) {
            $valid[$i] = 0;
            next;
        }
        if (is_3x3_deadlock($c, $dest_p)) {
            $valid[$i] = 0;
            next;
        }
        my $res = check_all_patterns($c, $dest_p, 0);
        next unless ($res != -1);
        $valid[$i] = 0;
        next;
    } ## end for my $i (0 .. $#$moves)
    return @valid;
} ## end sub check_deadlock_in_moves

sub remove_deadlocked_moves ($brd, $moves, $pull_mode, $search_mode, $h) {
    my @valid = check_deadlock_in_moves($brd, $moves, $pull_mode, $search_mode, $h);
    return map {$moves->[$_]} grep {$valid[$_]} 0 .. $#$moves;
}

sub count_adjacent_boxes ($brd) {
    my $adj_4 = $ZERO_BOARD;
    my $adj_9 = $ZERO_BOARD;
    for my $p (0 .. $Ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;
        vec($adj_4, $p, 8)++;
        vec($adj_9, $p, 8)++;
        for my $k (0 .. 7) {
            my $q = $p + $Delta_p_8[$k];
            vec($adj_9, $q, 8)++;
            vec($adj_4, $q, 8)++ if ($k & 1) == 0;
        }
    }
    return ($adj_4, $adj_9);
} ## end sub count_adjacent_boxes

sub check_for_k_dist_moves ($brd, $moves, $h) {
    for my $i (0 .. $#$moves) {
        my $from = $moves->[$i]{'from'};
        my $to   = $moves->[$i]{'to'};
        next unless (vec($Bfs_distance_from_to, $to * $Index_num + $from, 32) >= $h->{'k_dist_value'});
        my $c;
        $c = $brd;
        $c = apply_move($c, $moves->[$i], NORMAL);
        my $p = $Index_to_p[$from];
        if (vec($c, $p, 8) & SOKOBAN) {
            my $kill = { %{ $moves->[$i] } };
            $kill->{'kill'} = 1;
            return ($kill);
        }
    }
    return @$moves;
} ## end sub check_for_k_dist_moves

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
            next unless ($p->{'scores'}[$j]{'connectivity'} < $best_connectivity);
            $best_pos          = $i;
            $$son_ref          = $j;
            $best_connectivity = $p->{'scores'}[$j]{'connectivity'};
        } ## end for my $j (0 .. $p->{'moves_num'...})
    } ## end for my $i (0 .. $pos_num...)
    return $best_pos;
} ## end sub get_move_with_most_packing

sub has_a_move_with_all_boxes_packed ($p) {
    my $brd             = $p->{'board'};
    my $boxes_in_search = (($brd&.$BOX_ONLY) =~ tr/\x00//c);
    for my $i (0 .. $p->{'moves_num'} - 1) {
        return 1 if $p->{'scores'}[$i]{'boxes_on_targets'} == $boxes_in_search;
    }
    return 0;
}

sub reduce_moves_in_rooms_deadlock_search ($moves, $h) {
    for my $i (0 .. $#$moves) {
        my $p = $Index_to_p[$moves->[$i]{'to'}];
        next if $Rooms_board->[$p] == 1000000;
        next unless ($Rooms_board->[$p] != $h->{'tested_deadlock_room'});
        my $m = { %{ $moves->[$i] } };
        $m->{'kill'} = 1;
        return ($m);
    }
    return @$moves;
}

sub boxes_in_room ($brd, $r) {
    my $sum = 0;
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($Room_with_corridors[$r], $p, 8));
        $sum++ if vec($brd, $p, 8) & BOX;
    }
    return $sum;
}

sub is_better_rooms_deadlock_score ($new_score, $old_score) {
    return 1 if $new_score->{'boxes_in_level'} < $old_score->{'boxes_in_level'};
    return 0 if $new_score->{'boxes_in_level'} > $old_score->{'boxes_in_level'};
    return 1 if $new_score->{'connectivity'} < $old_score->{'connectivity'};
    return 0 if $new_score->{'connectivity'} > $old_score->{'connectivity'};
    return 1 if $new_score->{'boxes_on_targets'} > $old_score->{'boxes_on_targets'};
    return 0 if $new_score->{'boxes_on_targets'} < $old_score->{'boxes_on_targets'};
    return 0;
}

sub get_best_rooms_deadlock_move ($positions, $pos_num, $son_ref) {
    my $best_pos = -1;
    my $best_score;
    for my $i (0 .. $pos_num - 1) {
        my $p = $positions->[$i];
        next if $p->{'position_deadlocked'};
        for my $j (0 .. $p->{'moves_num'} - 1) {
            next if $p->{'move_deadlocked'}[$j];
            next if defined $p->{'place_in_positions'}[$j];
            next unless ($best_pos == -1 or is_better_rooms_deadlock_score($p->{'scores'}[$j], $best_score));
            $best_pos   = $i;
            $$son_ref   = $j;
            $best_score = { %{ $p->{'scores'}[$j] } };
        }
    }
    return $best_pos;
} ## end sub get_best_rooms_deadlock_move

sub keep_boxes_in_room ($brd, $r) {
    for my $p (0 .. $Ncells - 1) {
        vec($brd, $p, 8) &= 0xFF ^ BOX
            if vec($Room_with_corridors[$r], $p, 8) == 0;
    }
    $brd = expand_sokoban_cloud($brd);
    return $brd;
}

sub init_tree ($t) {
    $t->{'node_of_hash'}    = {};
    $t->{'node_expansion'}  = [];
    $t->{'node_hash'}       = [];
    $t->{'node_score'}      = [];
    $t->{'node_deadlocked'} = [];
    $t->{'nodes_num'}       = 0;
    $t->{'expansions'}      = [];
    $t->{'expansions_num'}  = 0;
    $t->{'mh_move'}         = [];
    $t->{'mh_node'}         = [];
    $t->{'mh_deadlocked'}   = [];
    $t->{'move_hashes_num'} = 0;
    $t->{'queues'}          = [];
    $t->{'labels_num'}      = 0;
    $t->{'pull_mode'}       = -1;
    $t->{'search_mode'}     = -1;
    return;
} ## end sub init_tree

sub reset_tree ($t) {
    %{ $t->{'node_of_hash'} } = ();
    @{ $t->{$_} } = ()
        for 'node_expansion', 'node_hash', 'node_score', 'node_deadlocked', 'expansions', 'mh_move', 'mh_node', 'mh_deadlocked';
    $t->{'nodes_num'}       = 0;
    $t->{'expansions_num'}  = 0;
    $t->{'move_hashes_num'} = 0;
    for my $i (0 .. $t->{'labels_num'} - 1) {
        $t->{'queues'}[$i]->{'elements'}  = [];
        $t->{'queues'}[$i]->{'heap_size'} = 0;
    }
    $t->{'labels_num'} = 0;
    return;
}

sub add_entry_to_hash_array ($t, $hash, $node_place) {
    my $map = $t->{'node_of_hash'};
    Carp::confess('already in array') if exists $map->{$hash};
    $map->{$hash} = $node_place;
    return;
}

sub get_score_of_node ($t, $place, $s) {
    @{$s}{ @{ +SCORE_KEYS } } = unpack 'd13', $t->{'node_score'}[$place];
    return;
}

sub update_subtree_size ($t, $e) {
    return unless defined $e;
    return if $t->{'node_deadlocked'}[$e->{'node'}];
    $e->{'subtree_size'}++;
    update_subtree_size($t, $e->{'father'});
    return;
}

sub add_node_to_tree ($t, $hash, $s) {
    my $place = ($t->{'node_of_hash'}{$hash} // -1);
    Carp::confess('adding exisitng hash') if $place != -1;
    $place                          = $t->{'nodes_num'};
    $t->{'node_expansion'}[$place]  = -1;
    $t->{'node_hash'}[$place]       = $hash;
    $t->{'node_score'}[$place]      = score_pack($s);
    $t->{'node_deadlocked'}[$place] = 0;
    $t->{'nodes_num'}++;
    add_entry_to_hash_array($t, $hash, $place);
    return;
}

sub node_is_solved ($t, $e) {
    my $brd = $e->{'b'};
    return 0 if $e->{'depth'} == 0;
    return board_is_solved($brd, $t->{'pull_mode'});
}

sub set_deadlock_status ($t, $e) {
    my $node_dead = $t->{'node_deadlocked'};
    my $node      = $e->{'node'};
    return if $node_dead->[$node];
    $node_dead->[$node] = 0;
    return if node_is_solved($t, $e);
    my $mh_node = $t->{'mh_node'};
    my $mh_dead = $t->{'mh_deadlocked'};
    my $mp      = $e->{'move_hash_place'};

    for my $i (0 .. $e->{'moves_num'} - 1) {
        next if $mh_dead->[$mp + $i];
        my $place = $mh_node->[$mp + $i];
        $mh_dead->[$mp + $i] = 1      if $node_dead->[$place];
    }
    for my $i (0 .. $e->{'moves_num'} - 1) {
        return if $mh_dead->[$mp + $i] == 0;
    }
    $node_dead->[$node] = 1;
    set_deadlock_status($t, $e->{'father'}) if defined $e->{'father'};
    return;
} ## end sub set_deadlock_status

sub set_leaf_direction ($t, $e) {
    my $mh_node = $t->{'mh_node'};
    my $mp      = $e->{'move_hash_place'};
    $e->{'leaf_direction'} = -1;
    return if $t->{'node_deadlocked'}[$e->{'node'}];
    for my $i (0 .. $e->{'moves_num'} - 1) {
        my $place = $mh_node->[$mp + $i];
        next                          if $t->{'node_deadlocked'}[$place];
        next unless ($t->{'node_expansion'}[$place] == -1);
        $e->{'leaf_direction'} = $i;
        return;
    }
    return;
} ## end sub set_leaf_direction

sub block_existing_sons_tree ($t, $e, $nodes_before_expansion) {
    my $mh_node = $t->{'mh_node'};
    my $mh_dead = $t->{'mh_deadlocked'};
    my $mp      = $e->{'move_hash_place'};
    for my $i (0 .. $e->{'moves_num'} - 1) {
        my $place = $mh_node->[$mp + $i];
        $mh_dead->[$mp + $i] = 1      if $place < $nodes_before_expansion;
    }
    set_deadlock_status($t, $e);
    return;
}

sub set_weight_to_node_moves ($t, $e, $h) {
    my $mh_move = $t->{'mh_move'};
    my $mp      = $e->{'move_hash_place'};
    for my $i (0 .. $e->{'moves_num'} - 1) {
        my $w = is_an_advisor($e->{'advisors'}, $i) == 1 ? 0 : 1;
        $mh_move->[$mp + $i] = $mh_move->[$mp + $i] & ~MOVE_WEIGHT | ($w + 1) << 30;
    }
    if ($h->{'weighted_search'} == 0) {
        for my $i (0 .. $e->{'moves_num'} - 1) {
            $mh_move->[$mp + $i] = $mh_move->[$mp + $i] & ~MOVE_WEIGHT | 1 << 30;
        }
    }
    $mh_move->[$mp] = $mh_move->[$mp] & ~MOVE_WEIGHT | 1 << 30 if $e->{'moves_num'} >= 1 and $e->{'moves_num'} <= 2;
    if ($h->{'perimeter_found'}) {
        for my $i (0 .. $e->{'moves_num'} - 1) {
            $mh_move->[$mp + $i] = $mh_move->[$mp + $i] & ~MOVE_WEIGHT | 2 << 30;
        }
    }
    return;
} ## end sub set_weight_to_node_moves

sub best_move_is_available ($t, $e) {
    my $mh_dead = $t->{'mh_deadlocked'};
    my $mp      = $e->{'move_hash_place'};
    my $son     = $e->{'best_move'};
    return 0 if $son == -1;
    return 0 if $mh_dead->[$mp + $son];
    my $place = $t->{'mh_node'}[$mp + $son];
    if ($t->{'node_deadlocked'}[$place]) {
        $mh_dead->[$mp + $son] = 1;
        return 0;
    }
    return 0 if $t->{'node_expansion'}[$place] != -1;
    return 1;
} ## end sub best_move_is_available

sub set_node_as_deadlocked ($t, $pos, $son) {
    my $e     = $t->{'expansions'}[$pos];
    my $mp    = $e->{'move_hash_place'};
    my $place = $t->{'mh_node'}[$mp + $son];
    Carp::confess('node is already deadlocked')
        if $t->{'node_deadlocked'}[$place];
    $t->{'node_deadlocked'}[$place] = 1;
    $t->{'mh_deadlocked'}[$mp + $son] = 1;
    set_deadlock_status($t, $e);
    return;
}

sub get_move_to_node ($t, $e) {
    Carp::confess('no father') unless defined $e->{'father'};
    my $f       = $e->{'father'};
    my $mh_node = $t->{'mh_node'};
    my $mp      = $f->{'move_hash_place'};
    for my $i (0 .. $f->{'moves_num'} - 1) {
        return move_unpack($t->{'mh_move'}[$mp + $i]) if $mh_node->[$mp + $i] == $e->{'node'};
    }
    Carp::confess('missing move');
}

sub store_solution_in_helper ($t, $e, $h) {
    my @solution_path;
    my $n = $e->{'depth'} + 1;
    while (defined $e) {
        $solution_path[$e->{'depth'}] = $e;
        $e = $e->{'father'};
    }
    Carp::confess('does not start at root')
        if $solution_path[0] != $t->{'expansions'}[0];
    for my $i (1 .. $n - 1) {
        $h->{'sol_move'}[$i - 1] =
            get_move_to_node($t, $solution_path[$i]);
    }
    $h->{'sol_len'} = $n - 1;
    return;
} ## end sub store_solution_in_helper

sub set_subtree_as_deadlocked ($t, $e) {
    my $mh_node   = $t->{'mh_node'};
    my $mh_dead   = $t->{'mh_deadlocked'};
    my $node_exp  = $t->{'node_expansion'};
    my $node_dead = $t->{'node_deadlocked'};
    my $mp        = $e->{'move_hash_place'};
    my $node      = $e->{'node'};
    return if $node_dead->[$node];
    $node_dead->[$node] = 1;

    for my $i (0 .. $e->{'moves_num'} - 1) {
        $mh_dead->[$mp + $i] = 1;
        my $place = $mh_node->[$mp + $i];
        if ($node_exp->[$place] == -1) {
            $node_dead->[$place] = 1;
        }
        else {
            set_subtree_as_deadlocked($t, $t->{'expansions'}[$node_exp->[$place]]);
        }
    }
    $node_dead->[$node] = 0;
    set_deadlock_status($t, $e);
    Carp::confess('dl bug') if $node_dead->[$node] == 0;
    return;
} ## end sub set_subtree_as_deadlocked

sub reduce_moves_in_wobblers_search ($moves) {
    for my $i (0 .. $#$moves) {
        my $kill = 0;
        $kill = 1 if $moves->[$i]{'attr'}{'reversible'};
        my $from = $moves->[$i]{'from'};
        my $to   = $moves->[$i]{'to'};
        if (abs($Index_to_y[$from] - $Index_to_y[$to]) >= 2) {
            $kill = 1 if abs($Index_to_x[$from] - $Index_to_x[$to]) >= 2;
        }
        next unless ($kill);
        my $m = { %{ $moves->[$i] } };
        $m->{'kill'} = 1;
        return ($m);
    }
    return @$moves;
} ## end sub reduce_moves_in_wobblers_search

sub box_can_be_pulled ($brd, $p) {
    for my $i (0 .. 3) {
        next unless (vec($brd, $p + $Delta_p[$i], 8) & SOKOBAN);
        return 1 if vec($brd, $p + 2 * $Delta_p[$i], 8) & SOKOBAN;
    }
    return 0;
}

sub remove_boxes_with_no_player_access ($brd, $pull_mode, $with_diag) {
    for my $p (0 .. $Ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;
        my ($touched, $untouched) = (0, 0);
        for my $k (0 .. 7) {
            next if $with_diag == 0 and $k & 1;
            my $val = vec($brd, $p + $Delta_p_8[$k], 8);
            $touched++ if $val & SOKOBAN;
            next unless (($val & OCCUPIED) == 0);
            $untouched++ if ($val & SOKOBAN) == 0;
        }
        if ($touched == 0) {
            vec($brd, $p, 8) &= 0xFF ^ BOX;
            next;
        }
        next unless ($untouched);
        vec($brd, $p, 8) &= 0xFF ^ BOX if box_can_be_pulled($brd, $p);
    } ## end for my $p (0 .. $Ncells...)
    $brd = expand_sokoban_cloud($brd);
    return $brd;
} ## end sub remove_boxes_with_no_player_access

sub push_is_reversible ($b_in, $p, $d) {
    return 0 if (vec($b_in, $p - $Delta_p[$d], 8) & SOKOBAN) == 0;
    return 0 if vec($b_in, $p + $Delta_p[$d],     8) & OCCUPIED;
    return 0 if vec($b_in, $p + 2 * $Delta_p[$d], 8) & OCCUPIED;
    my $brd = $b_in;
    vec($brd, $p, 8) &= 0xFF ^ BOX;
    vec($brd, $p + $Delta_p[$d], 8) |= BOX;
    $brd&.=$NOT_SOKOBAN;
    vec($brd, $p, 8) |= SOKOBAN;
    $brd = expand_sokoban_cloud($brd, $p);
    return 1 if vec($brd, $p + 2 * $Delta_p[$d], 8) & SOKOBAN;
    return 0;
}

sub pull_is_reversible ($b_in, $p, $d) {
    return 0 if (vec($b_in, $p + $Delta_p[$d], 8) & SOKOBAN) == 0;
    return 0 if vec($b_in, $p - $Delta_p[$d],     8) & OCCUPIED;
    return 0 if vec($b_in, $p + 2 * $Delta_p[$d], 8) & OCCUPIED;
    my $brd = $b_in;
    vec($brd, $p, 8) &= 0xFF ^ BOX;
    vec($brd, $p + $Delta_p[$d], 8) |= BOX;
    $brd&.=$NOT_SOKOBAN;
    my $sok_p = $p + 2 * $Delta_p[$d];
    vec($brd, $sok_p, 8) |= SOKOBAN;
    $brd = expand_sokoban_cloud($brd, $sok_p);
    return 1 if vec($brd, $p, 8) & SOKOBAN;
    return 0;
}

sub remove_wobblers ($brd, $pull_mode) {
    my $changed = 1;
    while ($changed) {
        $changed = 0;
        for my $p (0 .. $Ncells - 1) {
            next if (vec($brd, $p, 8) & BOX) == 0;
            for my $k (0 .. 3) {
                if ($pull_mode == 0) {
                    next if push_is_reversible($brd, $p, $k) == 0;
                }
                else {
                    next if pull_is_reversible($brd, $p, $k) == 0;
                }
                vec($brd, $p, 8) &= 0xFF ^ BOX;
                vec($brd, $p, 8) |= SOKOBAN;
                $changed = 1;
                last;
            }
        } ## end for my $p (0 .. $Ncells...)
        $brd = expand_sokoban_cloud($brd) if $changed;
    } ## end while ($changed)
    return $brd;
} ## end sub remove_wobblers

sub is_better_wobblers_score ($new_score, $old_score) {
    return 1 if $new_score->{'boxes_in_level'} < $old_score->{'boxes_in_level'};
    return 0 if $new_score->{'boxes_in_level'} > $old_score->{'boxes_in_level'};
    return 1 if $new_score->{'connectivity'} < $old_score->{'connectivity'};
    return 0 if $new_score->{'connectivity'} > $old_score->{'connectivity'};
    return 1 if $new_score->{'boxes_on_targets'} > $old_score->{'boxes_on_targets'};
    return 0 if $new_score->{'boxes_on_targets'} < $old_score->{'boxes_on_targets'};
    return 0;
}

sub get_best_wobblers_move ($positions, $pos_num, $son_ref) {
    my $best_pos = -1;
    my $best_score;
    for my $i (0 .. $pos_num - 1) {
        my $p = $positions->[$i];
        next if $p->{'position_deadlocked'};
        for my $j (0 .. $p->{'moves_num'} - 1) {
            next if $p->{'move_deadlocked'}[$j];
            next if defined $p->{'place_in_positions'}[$j];
            next unless ($best_pos == -1 or is_better_wobblers_score($p->{'scores'}[$j], $best_score));
            $best_pos   = $i;
            $$son_ref   = $j;
            $best_score = { %{ $p->{'scores'}[$j] } };
        }
    }
    return $best_pos;
} ## end sub get_best_wobblers_move

sub mark_hv_indices ($brd, $moves) {
    my (@h_indices, @v_indices, @con_ok, @indices);
    for my $i (0 .. $#$moves) {
        $con_ok[$i] = 0;
        my $c = $brd;
        $c = apply_move($c, $moves->[$i], NORMAL);
        my $from_p = $Index_to_p[$moves->[$i]{'from'}];
        $con_ok[$i] = 1 if vec($c, $from_p, 8) & SOKOBAN;
    }
    for my $i (0 .. $Index_num - 1) {
        $h_indices[$i] = $v_indices[$i] = 0;
    }
    for my $i (0 .. $#$moves) {
        next if $con_ok[$i] == 0;
        my $from = $moves->[$i]{'from'};
        my $to   = $moves->[$i]{'to'};
        $v_indices[$from] = 1 if $Index_to_y[$to] != $Index_to_y[$from];
        $h_indices[$from] = 1 if $Index_to_x[$to] != $Index_to_x[$from];
    }
    for my $i (0 .. $Index_num - 1) {
        $indices[$i] = $v_indices[$i] & $h_indices[$i];
    }
    return @indices;
} ## end sub mark_hv_indices

sub reduce_moves_in_xy_search ($brd, $moves) {
    my @hv_indices = mark_hv_indices($brd, $moves);
    for my $i (0 .. $#$moves) {
        next unless ($hv_indices[$moves->[$i]{'from'}]);
        my $kill = { %{ $moves->[$i] } };
        $kill->{'kill'} = 1;
        return ($kill);
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
            next unless ($best_pos == -1 or is_better_xy_score($p->{'scores'}[$j], $best_score));
            $best_pos   = $i;
            $$son_ref   = $j;
            $best_score = { %{ $p->{'scores'}[$j] } };
        }
    }
    return $best_pos;
} ## end sub get_best_xy_move

sub set_leaf_direction_in_tree ($t) {
    my $changed = 1;
    for my $i (0 .. $t->{'expansions_num'} - 1) {
        $t->{'expansions'}[$i]{'leaf_direction'} = -1;
    }
    while ($changed) {
        $changed = 0;
        for my $i (reverse 0 .. $t->{'expansions_num'} - 1) {
            my $e = $t->{'expansions'}[$i];
            next if $e->{'leaf_direction'} != -1;
            next if $t->{'node_deadlocked'}[$e->{'node'}];
            my $mh_node = $t->{'mh_node'};
            my $mh_dead = $t->{'mh_deadlocked'};
            my $mp      = $e->{'move_hash_place'};
            for my $j (0 .. $e->{'moves_num'} - 1) {
                next if $mh_dead->[$mp + $j];
                my $place = $mh_node->[$mp + $j];
                if ($t->{'node_deadlocked'}[$place]) {
                    $mh_dead->[$mp + $j] = 1;
                    next;
                }
                my $exp = $t->{'node_expansion'}[$place];
                if ($exp == -1) {
                    $e->{'leaf_direction'} = $j;
                    $changed = 1;
                    last;
                }
                my $e2 = $t->{'expansions'}[$exp];
                next unless ($e2->{'leaf_direction'} != -1);
                $e->{'leaf_direction'} = $j;
                $changed = 1;
                last;
            } ## end for my $j (0 .. $e->{'moves_num'...})
        } ## end for my $i (reverse 0 .....)
    } ## end while ($changed)
    for my $i (0 .. $t->{'expansions_num'} - 1) {
        my $e = $t->{'expansions'}[$i];
        next if $t->{'node_deadlocked'}[$e->{'node'}];
        next if $e->{'leaf_direction'} != -1;
        $t->{'node_deadlocked'}[$e->{'node'}] = 1;
    }
    return;
} ## end sub set_leaf_direction_in_tree

sub check_cycle_deadlock ($t, $e, $h) {
    my $depth = 0;
    my $base  = $e;
    return if $t->{'search_mode'} == BASE_SEARCH;
    while ($e->{'leaf_direction'} != -1) {
        last if $t->{'node_deadlocked'}[$e->{'node'}];
        my $place = $t->{'mh_node'}[$e->{'move_hash_place'} + $e->{'leaf_direction'}];
        last if $t->{'node_deadlocked'}[$place];
        my $exp = $t->{'node_expansion'}[$place];
        return if $exp == -1;
        $e = $t->{'expansions'}[$exp];
        $depth++;
        Carp::confess('cycle cycle') if $depth > 100000;
    }
    set_leaf_direction_in_tree($t);
    if ($t->{'node_deadlocked'}[$base->{'node'}]) {
    }
    return;
} ## end sub check_cycle_deadlock

sub go_to_root_greedy_tree ($t) {
    my $min_subtree_size = 1000000;
    my $best_tree        = -1;
    my $expansions       = $t->{'expansions'};
    for my $i (0 .. $t->{'expansions_num'} - 1) {
        next if $t->{'node_deadlocked'}[$expansions->[$i]{'node'}];
        last if $expansions->[$i]{'depth'} > 0;
        next unless (($best_tree == -1) or ($expansions->[$i]{'subtree_size'} < $min_subtree_size));
        $min_subtree_size = $expansions->[$i]{'subtree_size'};
        $best_tree        = $i;
    }
    return undef if $best_tree == -1;
    return $expansions->[$best_tree];
}

sub choose_cyclic_son_tree ($t, $e) {
    my $mh_dead = $t->{'mh_deadlocked'};
    my $mp      = $e->{'move_hash_place'};
    Carp::confess('choosing son for deadlocked position')
        if $t->{'node_deadlocked'}[$e->{'node'}];
    my $son = $e->{'next_son_to_check'};
    while ($mh_dead->[$mp + $son]) {
        $son = ($son + 1) % $e->{'moves_num'};
        Carp::confess('returned to first') if $son == $e->{'next_son_to_check'};
    }
    $e->{'next_son_to_check'} = ($son + 1) % $e->{'moves_num'};
    return $son;
}

sub recompute_values_tree ($t, $e, $h) {
    my $mh_node = $t->{'mh_node'};
    my $mh_dead = $t->{'mh_deadlocked'};
    my $mp      = $e->{'move_hash_place'};
    my $s       = {};
    Carp::confess('recomputing for deadlock') if $t->{'node_deadlocked'}[$e->{'node'}];
    score_set($t, $e->{'node'}, SC_VALUE, -1000000);
    for my $i (0 .. $e->{'moves_num'} - 1) {
        next if $mh_dead->[$mp + $i];
        get_score_of_node($t, $mh_node->[$mp + $i], $s);
        next unless ($s->{'value'} > score_field($t, $e->{'node'}, SC_VALUE));
        score_set($t, $e->{'node'}, SC_VALUE, $s->{'value'});
    }
    if (score_field($t, $e->{'node'}, SC_VALUE) == -1000000) {
        Carp::confess('score problem');
    }
    return;
} ## end sub recompute_values_tree

sub choose_best_value_son_tree ($t, $e, $h) {
    my $best_value = -1000000;
    my $best_son   = -1;
    my $mh_node    = $t->{'mh_node'};
    my $mh_dead    = $t->{'mh_deadlocked'};
    my $mp         = $e->{'move_hash_place'};
    my $s          = {};
    Carp::confess('choosing son for deadlocked') if $t->{'node_deadlocked'}[$e->{'node'}];
    for my $i (0 .. $e->{'moves_num'} - 1) {
        next if $mh_dead->[$mp + $i];
        get_score_of_node($t, $mh_node->[$mp + $i], $s);
        my $value = $s->{'value'};
        next unless (($best_son == -1) or ($value > $best_value));
        $best_value = $value;
        $best_son   = $i;
    }
    if ($best_son == -1) {
        Carp::confess('no best son');
    }
    return $best_son;
} ## end sub choose_best_value_son_tree

sub pick_son_Epsilon_greedy_tree ($t, $e, $h) {
    my $son;
    Carp::confess('epsilon deadlocked') if $t->{'node_deadlocked'}[$e->{'node'}];
    if (($e->{'subtree_size'} % $Inv_epsilon) == 0) {
        $son = choose_cyclic_son_tree($t, $e);
        return $son;
    }
    $son = choose_best_value_son_tree($t, $e, $h);
    return $son;
}

sub choose_pos_son_to_expand_Epsilon_greedy_tree ($t, $pos, $son, $h) {
    my $exp;
    $$pos = -1;
    my $e = go_to_root_greedy_tree($t);
    return unless defined $e;
    Carp::confess('root is deadlocked') if $t->{'node_deadlocked'}[$e->{'node'}];
    while (1) {
        set_deadlock_status($t, $e);
        if ($t->{'node_deadlocked'}[$e->{'node'}]) {
            $e = go_to_root_greedy_tree($t);
            return unless defined $e;
            last if $exp == -1;
            next;
        }
        recompute_values_tree($t, $e, $h);
        $$son = pick_son_Epsilon_greedy_tree($t, $e, $h);
        my $place = $t->{'mh_node'}[$e->{'move_hash_place'} + $$son];
        $exp = $t->{'node_expansion'}[$place];
        if ($exp != -1) {
            my $next = $t->{'expansions'}[$exp];
            $e = $next;
        }
        last if $exp == -1;
    } ## end while (1)
    $$pos = $e->{'index'};
    return;
} ## end sub choose_pos_son_to_expand_Epsilon_greedy_tree

sub back_propagate_values_tree ($t, $e) {
    my $max_value = -1000000;
    my $has_son   = 0;
    return unless defined $e;
    return if $t->{'node_deadlocked'}[$e->{'node'}];
    my $mh_node = $t->{'mh_node'};
    my $mh_dead = $t->{'mh_deadlocked'};
    my $mp      = $e->{'move_hash_place'};
    for my $i (0 .. $e->{'moves_num'} - 1) {
        next if $mh_dead->[$mp + $i];
        my $node_place = $mh_node->[$mp + $i];
        my $value = score_field($t, $node_place, SC_VALUE);
        $max_value = $value if $value > $max_value;
        $has_son   = 1;
    }
    if ($has_son == 0) {
        Carp::confess('no sons?') if node_is_solved($t, $e) == 0;
        $max_value = score_field($t, $e->{'node'}, SC_VALUE);
    }
    score_set($t, $e->{'node'}, SC_VALUE, $max_value);
    Carp::confess('max val') if $max_value == -1000000;
    back_propagate_values_tree($t, $e->{'father'});
    return;
} ## end sub back_propagate_values_tree

sub boxes_in_different_rooms ($index1, $index2) {
    my $index1_has_room = 0;
    my $index2_has_room = 0;
    return 1 if vec($Bfs_distance_from_to, $index1 * $Index_num + $index2, 32) >= BIG_DISTANCE;
    my $box1_p = $Index_to_p[$index1];
    my $box2_p = $Index_to_p[$index2];
    my $r1     = $Rooms_board->[$box1_p];
    my $r2     = $Rooms_board->[$box2_p];
    if ($r1 != 1000000 and $r2 != 1000000) {
        return 1 if $r1 != $r2;
    }
    if ($r1 != $r2) {
        if ($r1 != 1000000) {
            return 0 if vec($Room_with_corridors[$r1], $box2_p, 8);
        }
        if ($r2 != 1000000) {
            return 0 if vec($Room_with_corridors[$r2], $box1_p, 8);
        }
        return 1
            if $Index_to_y[$index1] != $Index_to_y[$index2]
            and $Index_to_x[$index1] != $Index_to_x[$index2];
    }
    return 0;
} ## end sub boxes_in_different_rooms

sub get_kill_zone ($bases) {
    my @bases_list;
    for my $p (0 .. $Ncells - 1) {
        push @bases_list, $Y_x_to_index_table[$p]
            if vec($bases, $p, 8);
    }
    my $kill_zone = $ZERO_BOARD;
    for my $i (0 .. $Index_num - 1) {
        my $j;
        for ($j = 0; $j < @bases_list; $j++) {
            last if vec($Bfs_distance_from_to, $i * $Index_num + $bases_list[$j], 32) < BIG_DISTANCE;
        }
        next unless ($j == @bases_list);
        vec($kill_zone, $Index_to_p[$i], 8) = 1;
        last;
    }
    return $kill_zone;
} ## end sub get_kill_zone

sub get_bases_as_board ($brd) {
    my $bases = $ZERO_BOARD;
    for my $p (0 .. $Ncells - 1) {
        vec($bases, $p, 8) = 1 if vec($brd, $p, 8) & BASE;
    }
    return $bases;
}

sub compute_possible_from_bases ($brd) {
    my ($bases, $board_without_boxes);
    $board_without_boxes = $Initial_board&.$NOT_BOX;
    $bases               = get_bases_as_board($brd);
    return find_targets_of_a_board_input($board_without_boxes, $bases);
}

sub get_possible_places ($brd, $pull_mode, $search_mode) {
    my $possible = $Inner;
    if ($pull_mode == 0) {
        $possible = get_srcs_of_all_targets($brd);
        return $possible;
    }
    if ($search_mode == BASE_SEARCH) {
        $possible = compute_possible_from_bases($brd);
    }
    return $possible;
}

sub test_base_matching ($brd, $from, $to) {
    my $c;
    my $from_p = $Index_to_p[$from];
    my $to_p   = $Index_to_p[$to];
    Carp::confess('no box')              if (vec($brd, $from_p, 8) & BOX) == 0;
    Carp::confess('no base in matching') if (vec($brd, $to_p,   8) & BASE) == 0;
    $c = $brd;
    vec($c, $from_p, 8) &= 0xFF ^ BOX;
    vec($c, $to_p,   8) &= 0xFF ^ BASE;
    my $res = check_matching_deadlock($c, 1, BASE_SEARCH);
    return 0 if $res == 1;
    return 1;
}

sub unreachable_area_contains_elim ($brd, $elim) {
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($elim, $p, 8));
        return 1 if (vec($brd, $p, 8) & SOKOBAN) == 0;
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
    for my $p (0 .. $Ncells - 1) {
        $bases[$bases_num++] = $Y_x_to_index_table[$p]
            if vec($brd, $p, 8) & BASE;
    }
    for my $i (0 .. $bases_num - 1) {
        for my $j (0 .. $bases_num - 1) {
            $mat[$i][$j] = 0;
        }
    }
    my $gd = allocate_graph();
    build_graph($brd, 0, $gd);
    for my $i (0 .. $bases_num - 1) {
        my $p2 = $Index_to_p[$bases[$i]];
        $targets = find_targets_of_place_without_init_graph($p2, $gd);
        Carp::confess('no self')
            if vec($targets, $Index_to_p[$bases[$i]], 8) == 0;
        for my $j (0 .. $bases_num - 1) {
            $mat[$i][$j] = 1 if vec($targets, $Index_to_p[$bases[$j]], 8);
        }
    }
    for my $i (0 .. $bases_num - 1) {
        Carp::confess('bad diag') if $mat[$i][$i] != 1;
    }
    for my $i (0 .. $bases_num - 1) {
        $scc[$i] = -1;
    }
    my $current_scc = 0;
    for my $i (0 .. $bases_num - 1) {
        next if $scc[$i] != -1;
        $scc[$i] = $current_scc;
        for my $j ($i .. $bases_num - 1) {
            $scc[$j] = $current_scc if $mat[$i][$j] & $mat[$j][$i];
        }
        $current_scc++;
    }
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
            next unless ($scc[$j] == $scc[$i]);
            vec($scc_out, $Index_to_p[$bases[$j]], 8) = 1;
        }
    }
    return $scc_out;
} ## end sub compute_bases_scc

sub mark_sink_squares_moves ($brd, $moves) {
    my $has_base_move = 0;
    my @tmp;
    my $elim;
    my @move_tested;
    my $moves_num = scalar @$moves;
    $elim = compute_bases_scc($brd);
    return @$moves if unreachable_area_contains_elim($brd, $elim);
    for my $i (0 .. $moves_num - 1) {
        $move_tested[$i] = 0;
    }
    for my $i (0 .. $moves_num - 1) {
        $move_tested[$i] = 1;
        next if vec($elim, $Index_to_p[$moves->[$i]{'to'}], 8) == 0;
        next
            if boxes_in_different_rooms($moves->[$i]{'from'}, $moves->[$i]{'to'}) == 0;
        next
            if test_base_matching($brd, $moves->[$i]{'from'}, $moves->[$i]{'to'}) == 0;
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
    my @box_was_pulled = (0) x $Index_num;
    for my $i (0 .. $moves_num - 1) {
        if ($move_tested[$i]) {
            next if $moves->[$i]{'base'} == 0;
        }
        if ($moves->[$i]{'base'} == 1) {
            push @tmp, $moves->[$i];
            $box_was_pulled[$moves->[$i]{'from'}] = 1;
            next;
        }
        next if $box_was_pulled[$moves->[$i]{'from'}];
        next if vec($elim, $Index_to_p[$moves->[$i]{'to'}], 8) == 0;
        next
            if boxes_in_different_rooms($moves->[$i]{'from'}, $moves->[$i]{'to'}) == 0;
        next
            if test_base_matching($brd, $moves->[$i]{'from'}, $moves->[$i]{'to'}) == 0;
        $moves->[$i]{'base'} = 1;
        push @tmp, $moves->[$i];
        $box_was_pulled[$moves->[$i]{'from'}] = 1;
    } ## end for my $i (0 .. $moves_num...)
    return @tmp;
} ## end sub mark_sink_squares_moves

sub is_better_pull_candidate ($old_opt, $new_opt) {
    return 0 if $new_opt->{'target_hole'} > $old_opt->{'target_hole'};
    return 1 if $new_opt->{'target_hole'} < $old_opt->{'target_hole'};
    return 1 if $new_opt->{'kill_zone'} > $old_opt->{'kill_zone'};
    return 0 if $new_opt->{'kill_zone'} < $old_opt->{'kill_zone'};
    return 1 if $new_opt->{'connectivity'} < $old_opt->{'connectivity'};
    return 0 if $new_opt->{'connectivity'} > $old_opt->{'connectivity'};
    return 1 if $new_opt->{'rooms_score'} < $old_opt->{'rooms_score'};
    return 0 if $new_opt->{'rooms_score'} > $old_opt->{'rooms_score'};
    return 1 if $new_opt->{'pull_len'} > $old_opt->{'pull_len'};
    return 0 if $new_opt->{'pull_len'} < $old_opt->{'pull_len'};
    return 0;
}

sub pick_pull_advisor_normal ($b_in, $base_score, $moves_num, $moves, $scores, $search_mode) {
    my $brd;
    my $best_move = -1;
    my ($kill_zone, $scc, $w, $targets);
    my ($best_pull, $current_pull);
    $brd = $b_in;
    if ($search_mode == BASE_SEARCH) {
        $scc       = compute_bases_scc($brd);
        $kill_zone = get_kill_zone($scc);
        $w         = $brd;
        $w         = turn_boxes_into_walls($w);
        $targets   = find_targets_of_a_board_input($w, $scc);
        $kill_zone&.=$targets;
    }
    else {
        $kill_zone = $ZERO_BOARD;
    }
    $best_pull = {
        'target_hole'  =>  2,
        'kill_zone'    => -1,
        'connectivity' =>  0,
        'rooms_score'  =>  0,
        'pull_len'     =>  0,
    };
    for my $i (0 .. $moves_num - 1) {
        next if $scores->[$i]{'connectivity'} > $base_score->{'connectivity'};
        next if $scores->[$i]{'rooms_score'} > $base_score->{'rooms_score'};
        next
            if $scores->[$i]{'dist_to_targets'} <= $base_score->{'dist_to_targets'};
        my $from_p = $Index_to_p[$moves->[$i]{'from'}];
        my $to_p   = $Index_to_p[$moves->[$i]{'to'}];
        next if (vec($brd, $from_p, 8) & TARGET) == 0;
        $current_pull = {
            'kill_zone'    => vec($kill_zone, $to_p, 8),
            'connectivity' => $scores->[$i]{'connectivity'},
            'rooms_score'  => $scores->[$i]{'rooms_score'},
            'pull_len'     => vec($Distance_from_to, $moves->[$i]{'to'} * $Index_num + $moves->[$i]{'from'}, 32),
            'target_hole'  => vec($Target_holes,     $from_p,                                                8),
        };
        next unless (is_better_pull_candidate($best_pull, $current_pull));
        $best_move = $i;
        $best_pull = $current_pull;
    } ## end for my $i (0 .. $moves_num...)
    return $best_move;
} ## end sub pick_pull_advisor_normal

sub is_better_base_prioirity ($new_bp, $old_bp) {
    return 1 if $new_bp->{'hole'} < $old_bp->{'hole'};
    return 0 if $new_bp->{'hole'} > $old_bp->{'hole'};
    return 1 if $new_bp->{'connectivity'} < $old_bp->{'connectivity'};
    return 0 if $new_bp->{'connectivity'} > $old_bp->{'connectivity'};
    return 1 if $new_bp->{'dist'} > $old_bp->{'dist'};
    return 0 if $new_bp->{'dist'} < $old_bp->{'dist'};
    return 0;
}

sub connectivity_after_move ($b_in, $m) {
    my $brd;
    $brd = $b_in;
    my $p = $Index_to_p[$m->{'from'}];
    vec($brd, $p, 8) &= 0xFF ^ BOX;
    $p = $Index_to_p[$m->{'to'}];
    vec($brd, $p, 8) |= BOX;
    return get_connectivity($brd);
}

sub find_best_base_pull ($b_in, $base_score, $moves_num, $moves) {
    my $best_move = -1;
    my ($best_pull, $current_pull);
    my $brd;
    $current_pull = { 'hole' => 2 };
    $brd          = $b_in;
    for my $i (0 .. $moves_num - 1) {
        next if $moves->[$i]{'base'} == 0;
        my $p = $Index_to_p[$moves->[$i]{'from'}];
        return $i if vec($brd, $p, 8) == BOX;
    }
    $best_move = -1;
    for my $i (0 .. $moves_num - 1) {
        next if $moves->[$i]{'base'} == 0;
        my $p = $Index_to_p[$moves->[$i]{'from'}];
        $current_pull = {
            'hole'         => vec($Target_holes, $p, 8),
            'connectivity' => connectivity_after_move($brd, $moves->[$i]),
        };
        $p = $Index_to_p[$moves->[$i]{'to'}];
        $current_pull->{'dist'} =
            vec($Bfs_distance_from_to, $moves->[$i]{'to'} * $Index_num + $moves->[$i]{'from'}, 32);
        next unless ($best_move == -1 or is_better_base_prioirity($current_pull, $best_pull));
        $best_move = $i;
        $best_pull = $current_pull;
    }
    Carp::confess("base bug\n") if $best_move == -1;
    return $best_move;
} ## end sub find_best_base_pull

sub packing_search_advisor ($brd, $base_score, $moves_num, $moves, $scores, $search_mode) {
    my $has_elim = 0;
    for my $i (0 .. $moves_num - 1) {
        $has_elim |= $moves->[$i]{'base'};
    }
    if ($has_elim == 0) {
        return pick_pull_advisor_normal($brd, $base_score, $moves_num, $moves, $scores, $search_mode);
    }
    return find_best_base_pull($brd, $base_score, $moves_num, $moves);
}

sub can_be_accessed_from_some_direction ($brd, $p) {
    for my $i (0 .. 3) {
        next if vec($brd, $p + $Delta_p[$i],     8) == WALL;
        next if vec($brd, $p + $Delta_p[$i] * 2, 8) & OCCUPIED;
        return 1;
    }
    return 0;
}

sub hf_hotspots ($brd, $pull_mode, $h) {
    my $sum = 0;
    if ($pull_mode) {
        for my $p (0 .. $Ncells - 1) {
            next unless (vec($brd, $p, 8) & BOX);
            $sum++
                if can_be_accessed_from_some_direction($brd, $p) == 0;
        }
        return $sum;
    }
    my $img = $h->{'imagined_hf_board'};
    for my $p (0 .. $Ncells - 1) {
        if ((vec($brd, $p, 8) & BOX) and ((vec($img, $p, 8) & BOX) == 0)) {
            for my $k (0 .. 3) {
                next unless (vec($brd, $p + $Delta_p[$k], 8) & OCCUPIED);
                $sum++;
                last;
            }
        }
        next unless ((vec($img, $p, 8) & BOX) and ((vec($brd, $p, 8) & BOX) == 0));
        $sum++ if can_be_accessed_from_some_direction($brd, $p) == 0;
    }
    return $sum;
} ## end sub hf_hotspots

sub is_better_hf_score ($new_score, $old_score, $pull_mode) {
    if ($pull_mode == 0) {
        return 1
            if ($new_score->{'dist_to_imagined'} < 1000000)
            and ($old_score->{'dist_to_imagined'} >= 1000000);
        return 0
            if ($new_score->{'dist_to_imagined'} >= 1000000)
            and ($old_score->{'dist_to_imagined'} < 1000000);
        return 1 if $new_score->{'connectivity'} < $old_score->{'connectivity'};
        return 0 if $new_score->{'connectivity'} > $old_score->{'connectivity'};
        return 1 if $new_score->{'imagine'} > $old_score->{'imagine'};
        return 0 if $new_score->{'imagine'} < $old_score->{'imagine'};
        return 1 if $new_score->{'hotspots'} < $old_score->{'hotspots'};
        return 0 if $new_score->{'hotspots'} > $old_score->{'hotspots'};
        return 1
            if $new_score->{'dist_to_imagined'} < $old_score->{'dist_to_imagined'};
        return 0
            if $new_score->{'dist_to_imagined'} > $old_score->{'dist_to_imagined'};
        return 0;
    } ## end if ($pull_mode == 0)
    return 1 if $new_score->{'connectivity'} < $old_score->{'connectivity'};
    return 0 if $new_score->{'connectivity'} > $old_score->{'connectivity'};
    return 1 if $new_score->{'rooms_score'} < $old_score->{'rooms_score'};
    return 0 if $new_score->{'rooms_score'} > $old_score->{'rooms_score'};
    if (($new_score->{'connectivity'} == 1) and ($old_score->{'connectivity'} == 1)) {
        return 1 if $new_score->{'hotspots'} < $old_score->{'hotspots'};
        return 0 if $new_score->{'hotspots'} > $old_score->{'hotspots'};
        return 1 if $new_score->{'biconnect'} < $old_score->{'biconnect'};
        return 0 if $new_score->{'biconnect'} > $old_score->{'biconnect'};
    }
    return 1 if $new_score->{'dist_to_targets'} > $old_score->{'dist_to_targets'};
    return 0 if $new_score->{'dist_to_targets'} < $old_score->{'dist_to_targets'};
    return 0;
} ## end sub is_better_hf_score

sub is_better_rev_score ($new_score, $old_score, $pull_mode) {
    if ($pull_mode) {
        return 1
            if ($new_score->{'dist_to_imagined'} < 1000000)
            and ($old_score->{'dist_to_imagined'} >= 1000000);
        return 0
            if ($new_score->{'dist_to_imagined'} >= 1000000)
            and ($old_score->{'dist_to_imagined'} < 1000000);
        return 1 if $new_score->{'connectivity'} < $old_score->{'connectivity'};
        return 0 if $new_score->{'connectivity'} > $old_score->{'connectivity'};
        if ($new_score->{'connectivity'} > 1) {
            return 1
                if $new_score->{'dist_to_targets'} > $old_score->{'dist_to_targets'};
            return 0
                if $new_score->{'dist_to_targets'} < $old_score->{'dist_to_targets'};
        }
        return 1
            if $new_score->{'boxes_on_targets'} > $old_score->{'boxes_on_targets'};
        return 0
            if $new_score->{'boxes_on_targets'} < $old_score->{'boxes_on_targets'};
        return 1
            if $new_score->{'dist_to_imagined'} < $old_score->{'dist_to_imagined'};
        return 0
            if $new_score->{'dist_to_imagined'} > $old_score->{'dist_to_imagined'};
        return 0;
    } ## end if ($pull_mode)
    return 1 if $new_score->{'connectivity'} < $old_score->{'connectivity'};
    return 0 if $new_score->{'connectivity'} > $old_score->{'connectivity'};
    return 1 if $new_score->{'rooms_score'} < $old_score->{'rooms_score'};
    return 0 if $new_score->{'rooms_score'} > $old_score->{'rooms_score'};
    return 1 if $new_score->{'hotspots'} < $old_score->{'hotspots'};
    return 0 if $new_score->{'hotspots'} > $old_score->{'hotspots'};
    return 1 if $new_score->{'dist_to_targets'} > $old_score->{'dist_to_targets'};
    return 0 if $new_score->{'dist_to_targets'} < $old_score->{'dist_to_targets'};
    return 0;
} ## end sub is_better_rev_score

sub setup_rev_board ($e, $h) {
    my $w;
    $h->{'imagined_hf_board'} = $e->{'b'};
    $w                        = $h->{'imagined_hf_board'};
    $w                        = turn_fixed_boxes_into_walls($h->{'imagined_hf_board'});
    $h->{'wallified'}         = $ZERO_BOARD;
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($w, $p, 8) == WALL);
        vec($h->{'wallified'}, $p, 8) = 1 if vec($Inner, $p, 8);
    }
    return;
}

sub set_rev_distance ($t, $e, $h, $moves, $scores) {
    my $mh_move = $t->{'mh_move'};
    my $mh_node = $t->{'mh_node'};
    my $mp      = $e->{'move_hash_place'};
    for my $i (0 .. $e->{'moves_num'} - 1) {
        $moves->[$i]  = move_unpack($mh_move->[$mp + $i]);
        $scores->[$i] = {};
        get_score_of_node($t, $mh_node->[$mp + $i], $scores->[$i]);
    }
    my $brd = $e->{'b'};
    my $base = score_hash($t, $e->{'node'});
    compute_rev_distance($brd, $base, $moves, $scores, $h->{'imagined_hf_board'}, $Distance_from_to);
    $t->{'node_score'}[$e->{'node'}] = score_pack($base);
    for my $i (0 .. $e->{'moves_num'} - 1) {
        my $place = $mh_node->[$mp + $i];
        score_set($t, $place, SC_DIST_TO_IMAGINED, $scores->[$i]{'dist_to_imagined'});
    }
    return;
} ## end sub set_rev_distance

sub can_be_pushed_to_direction ($brd, $p, $d) {
    return 0 if vec($brd, $p + $Delta_p[$d],           8) & OCCUPIED;
    return 0 if vec($brd, $p + $Delta_p[($d + 2) & 3], 8) & OCCUPIED;
    return 0 if deadlock_in_direction($brd, $p, $d);
    return 1;
}

sub get_rev_hotspots ($brd) {
    my $hs = $ZERO_BOARD;
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($brd, $p, 8) & BOX);
        next if vec($brd, $p, 8) & TARGET;
        my $k;
        for ($k = 0; $k < 4; $k++) {
            last if can_be_pushed_to_direction($brd, $p, $k);
        }
        vec($hs, $p, 8) = 1 if $k == 4;
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
    $b2 = $Initial_board&.$NOT_BOX;
    $hs = expand_group($b2, $hs, $dist);
    for my $p (0 .. $Ncells - 1) {
        $sum += $dist->[$p]
            if vec($brd, $p, 8) & BOX;
    }
    return $sum;
} ## end sub rev_hotspots_distance

sub rev_hotspots ($brd) {
    my $hs;
    $hs = get_rev_hotspots($brd);
    return unpack('%32C*', $hs);
}

sub compare_to_imagined_hf ($brd, $h) {
    my $sum = 0;
    my $img = $h->{'imagined_hf_board'};
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($brd, $p, 8) & BOX);
        $sum++ if vec($img, $p, 8) & BOX;
    }
    return $sum;
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

sub get_distance_in_hf_search ($brd, $s, $h) {
    my ($untouched, $tmp);
    my $dist = [];
    my $sum  = 0;
    return get_scored_distance($brd, $h);
    $untouched = get_untouched_areas($brd);
    $tmp       = $Initial_board&.$NOT_BOX;
    $untouched = expand_group($tmp, $untouched, $dist);
    for my $p (0 .. $Ncells - 1) {
        $sum += $dist->[$p]
            if vec($brd, $p, 8) & BOX;
    }
    return $sum;
}

sub fill_hf_scores ($brd, $s, $pull_mode, $search_mode, $h) {
    $s->{'boxes_on_targets'} = 0;
    $s->{'hotspots'}         = hf_hotspots($brd, $pull_mode, $h);
    if ($pull_mode == 0) {
        $s->{'imagine'} = compare_to_imagined_hf($brd, $h);
        return;
    }
    if (($search_mode == BICON_SEARCH) or ($search_mode == MAX_DIST_SEARCH)) {
        $s->{'biconnect'} = biconnect_score($brd, 0);
    }
    $s->{'rooms_score'}     = score_rooms($brd);
    $s->{'dist_to_targets'} = get_distance_in_hf_search($brd, $s, $h);
    return;
}

sub set_max_dist_data_in_node ($t, $e, $h) {
    my (@moves, @scores);
    return if $t->{'pull_mode'} == 0;
    my $mh_move = $t->{'mh_move'};
    my $mh_node = $t->{'mh_node'};
    my $mp      = $e->{'move_hash_place'};
    for my $i (0 .. $e->{'moves_num'} - 1) {
        $moves[$i]  = move_unpack($mh_move->[$mp + $i]);
        $scores[$i] = {};
        get_score_of_node($t, $mh_node->[$mp + $i], $scores[$i]);
    }
    my $brd  = $e->{'b'};
    my $base = score_hash($t, $e->{'node'});
    compute_match_distance($brd, $base, \@moves, \@scores);
    $t->{'node_score'}[$e->{'node'}] = score_pack($base);
    for my $i (0 .. $e->{'moves_num'} - 1) {
        my $place = $mh_node->[$mp + $i];
        score_set($t, $place, SC_DIST_TO_TARGETS, $scores[$i]{'dist_to_targets'});
    }
    return;
} ## end sub set_max_dist_data_in_node

sub set_naive_data_in_node ($t, $e, $h) {
    my (@moves, @scores);
    my $mh_move = $t->{'mh_move'};
    my $mh_node = $t->{'mh_node'};
    my $mp      = $e->{'move_hash_place'};
    for my $i (0 .. $e->{'moves_num'} - 1) {
        $moves[$i]  = move_unpack($mh_move->[$mp + $i]);
        $scores[$i] = {};
        get_score_of_node($t, $mh_node->[$mp + $i], $scores[$i]);
    }
    my $brd = $e->{'b'};
    my $base = score_hash($t, $e->{'node'});
    if ($t->{'pull_mode'}) {
        compute_base_distance($brd, $base, \@moves, \@scores);
    }
    else {
        compute_match_distance($brd, $base, \@moves, \@scores);
    }
    $t->{'node_score'}[$e->{'node'}] = score_pack($base);
    for my $i (0 .. $e->{'moves_num'} - 1) {
        my $place = $mh_node->[$mp + $i];
        score_set($t, $place, SC_DIST_TO_TARGETS, $scores[$i]{'dist_to_targets'});
    }
    return;
} ## end sub set_naive_data_in_node

sub verify_parking_order ($h) {
    my $parking_order     = $h->{'parking_order'};
    my $parking_order_num = $h->{'parking_order_num'};
    for my $i (0 .. $parking_order_num - 1) {
        if (   $parking_order->[$i]{'to'} >= $Index_num
            or $parking_order->[$i]{'to'} < 0)
        {
            Carp::confess("parking order $i (to) out of range");
        }
        next unless ($parking_order->[$i]{'from'} >= $Index_num);
        Carp::confess("parking order $i (from) out of range");
    }
    return;
}

sub move_mandatory_boxes_to_beginning ($p, $n) {
    my @tmp;
    for my $i (0 .. $n - 1) {
        push @tmp, $p->[$i]
            if $p->[$i]{'from'} == -2 and $p->[$i]{'until'} == -1;
    }
    for my $i (0 .. $n - 1) {
        push @tmp, $p->[$i]
            if $p->[$i]{'from'} != -2
            or $p->[$i]{'until'} != -1;
    }
    for my $i (0 .. $n - 1) {
        $p->[$i] = $tmp[$i];
    }
    return;
} ## end sub move_mandatory_boxes_to_beginning

sub recompute_until ($h) {
    my $parking_order = $h->{'parking_order'};
    my $n             = $h->{'parking_order_num'};
    for my $i (0 .. $n - 1) {
        $parking_order->[$i]{'until'} = -1;
    }
    for my $i (0 .. $n - 1) {
        for my $j ($i + 1 .. $n - 1) {
            next unless ($parking_order->[$j]{'from'} == $parking_order->[$i]{'to'});
            $parking_order->[$i]{'until'} = $j;
            last;
        }
    }
    return;
} ## end sub recompute_until

sub fix_consecutive_pushes ($h) {
    my $fixed         = 0;
    my $parking_order = $h->{'parking_order'};
    my $i             = 0;
    while ($i < $h->{'parking_order_num'} - 1) {
        if ($parking_order->[$i]{'from'} == -2) {
            $i++;
            next;
        }
        if ($parking_order->[$i]{'to'} == $parking_order->[$i]{'from'}) {
            for my $j ($i .. $h->{'parking_order_num'} - 2) {
                $parking_order->[$j] = $parking_order->[$j + 1];
            }
            $h->{'parking_order_num'}--;
            $i     = 0;
            $fixed = 1;
        }
        if ($parking_order->[$i]{'to'} == $parking_order->[$i + 1]{'from'}) {
            $parking_order->[$i]{'to'} = $parking_order->[$i + 1]{'to'};
            for my $j ($i + 1 .. $h->{'parking_order_num'} - 2) {
                $parking_order->[$j] = $parking_order->[$j + 1];
            }
            $h->{'parking_order_num'}--;
            $i     = 0;
            $fixed = 1;
        }
        $i++;
    } ## end while ($i < $h->{'parking_order_num'...})
    recompute_until($h);
    return $fixed;
} ## end sub fix_consecutive_pushes

sub get_parking_plan ($t, $e, $h) {
    my $n             = 0;
    my $parking_order = $h->{'parking_order'};
    my $brd           = $e->{'b'};
    for my $p (reverse 0 .. $Ncells - 1) {
        next unless (vec($brd, $p, 8) & BOX);
        $parking_order->[$n] = {
            'from'  => -2,
            'to'    => $Y_x_to_index_table[$p],
            'until' => -1,
        };
        $n++;
    }
    while (defined $e->{'father'}) {
        my $m = get_move_to_node($t, $e);
        my ($from, $to);
        if ($m->{'base'} == 0) {
            $from = $m->{'from'};
            $to   = $m->{'to'};
        }
        else {
            $from = $m->{'from'};
            $to   = -1;
        }
        $e = $e->{'father'};
        next if $from == $to;
        $parking_order->[$n] = {
            'from'  => $to,
            'to'    => $from,
            'until' => -1,
        };
        $n++;
    } ## end while (defined $e->{'father'...})
    $h->{'parking_order_num'} = $n;
    recompute_until($h);
    fix_consecutive_pushes($h);
    move_mandatory_boxes_to_beginning($parking_order, $h->{'parking_order_num'});
    return;
} ## end sub get_parking_plan

sub keep_only_perm ($h) {
    my $n = 0;
    my @tmp;
    my $parking_order = $h->{'parking_order'};
    for my $i (0 .. $h->{'parking_order_num'} - 1) {
        next unless ($parking_order->[$i]{'until'} == -1);
        $tmp[$n] = $parking_order->[$i];
        $tmp[$n]{'from'} = -1 if $tmp[$n]{'from'} != -2;
        $n++;
    }
    for my $i (0 .. $n - 1) {
        $parking_order->[$i] = $tmp[$i];
    }
    $h->{'parking_order_num'} = $n;
    return;
} ## end sub keep_only_perm

sub mandatory_inits_missing ($has_box, $init_num, $h) {
    my $parking_order = $h->{'parking_order'};
    for my $i (0 .. $init_num - 1) {
        next unless ($parking_order->[$i]{'until'} == -1);
        return 1 if $has_box->[$i] == 0;
    }
    return 0;
}

sub get_number_of_mandatory_inits ($has_box, $init_num, $h) {
    my $n             = 0;
    my $parking_order = $h->{'parking_order'};
    for my $i (0 .. $init_num - 1) {
        next unless ($parking_order->[$i]{'until'} == -1);
        $n++ if $has_box->[$i];
    }
    return $n;
}

sub get_boxes_in_place ($brd, $has_box, $h) {
    my $parking_order = $h->{'parking_order'};
    for my $i (0 .. $h->{'parking_order_num'} - 1) {
        $has_box->[$i] =
            (vec($brd, $Index_to_p[$parking_order->[$i]{'to'}], 8) & BOX ? 1 : 0);
    }
    return;
}

sub score_parked_boxes ($brd, $h) {
    my @has_box;
    my $init_num      = 0;
    my $good_init     = 0;
    my $parking_order = $h->{'parking_order'};
    get_boxes_in_place($brd, \@has_box, $h);
    for my $i (0 .. $h->{'parking_order_num'} - 1) {
        $init_num++ if $parking_order->[$i]{'from'} == -2;
    }
    if (mandatory_inits_missing(\@has_box, $init_num, $h)) {
        return get_number_of_mandatory_inits(\@has_box, $init_num, $h);
    }
    my $packed = $h->{'parking_order_num'};
    for my $i (reverse $init_num .. $h->{'parking_order_num'} - 1) {
        next if $has_box[$i];
        if ($parking_order->[$i]{'until'} == -1) {
            $packed = $i;
        }
        else {
            $packed = $i if $parking_order->[$i]{'until'} >= $packed;
        }
    }
    for my $i (0 .. $init_num - 1) {
        $good_init++
            if $has_box[$i]
            or $parking_order->[$i]{'until'} < $packed;
    }
    $packed -= ($init_num - $good_init);
    return $packed;
} ## end sub score_parked_boxes

sub all_fixed_initials_on_place ($brd, $h) {
    my @has_box;
    my $parking_order = $h->{'parking_order'};
    get_boxes_in_place($brd, \@has_box, $h);
    for my $i (0 .. $h->{'parking_order_num'} - 1) {
        next unless ($parking_order->[$i]{'from'} == -2);
        if ($parking_order->[$i]{'until'} == -1) {
            return 0 if $has_box[$i] == 0;
        }
    }
    return 1;
}

sub next_parking_place ($brd, $h) {
    my @has_box;
    my $init_num      = 0;
    my $parking_order = $h->{'parking_order'};
    return -1 if all_fixed_initials_on_place($brd, $h) == 0;
    get_boxes_in_place($brd, \@has_box, $h);
    while ( $init_num < $h->{'parking_order_num'}
        and $parking_order->[$init_num]{'from'} == -2)
    {
        $init_num++;
    }
    my $packed = $h->{'parking_order_num'};
    for my $i (reverse $init_num .. $h->{'parking_order_num'} - 1) {
        next if $has_box[$i];
        if ($parking_order->[$i]{'until'} == -1) {
            $packed = $i;
        }
        else {
            $packed = $i if $parking_order->[$i]{'until'} >= $packed;
        }
    }
    return -1 if $packed == $h->{'parking_order_num'};
    return $parking_order->[$packed]{'to'};
} ## end sub next_parking_place

sub is_in_stuck_patterns ($brd, $pull_mode) {
    return 0 if @Stuck_patterns == 0;
    my @indices = (map {(vec($brd, $Index_to_p[$_], 8) & BOX) ? 1 : 0} 0 .. $Index_num - 1);
    for my $sp (@Stuck_patterns) {
        next if $sp->{'pull'} != $pull_mode;
        my $all = 1;
        for my $j (0 .. $sp->{'boxes_num'} - 1) {
            next unless ($indices[$sp->{'boxes'}[$j]] == 0);
            $all = 0;
            last;
        }
        next unless ($all);
        return 1 if vec($sp->{'b'}, get_sokoban_position($brd), 8) & SOKOBAN;
    }
    return 0;
} ## end sub is_in_stuck_patterns

sub add_stuck_pattern ($brd, $pull_mode) {
    if (is_in_stuck_patterns($brd, $pull_mode) == 0) {
        my $n = (($brd&.$BOX_ONLY) =~ tr/\x00//c);
        Carp::confess('pattern too big') if $n > MAX_STUCK_PATTERN_SIZE;
        Carp::confess('empty pattern')   if $n == 0;
        push @Stuck_patterns,
            {
                'b'         => $brd,
                'boxes'     => [(grep {vec($brd, $Index_to_p[$_], 8) & BOX} 0 .. $Index_num - 1)],
                'boxes_num' => $n,
                'pull'      => $pull_mode,
            };
    }
    return;
} ## end sub add_stuck_pattern

sub recheck_tree_with_patterns ($t) {
    for my $i (0 .. $t->{'expansions_num'} - 1) {
        my $e = $t->{'expansions'}[$i];
        next if $t->{'node_deadlocked'}[$e->{'node'}];
        my $brd = $e->{'b'};
        next unless (is_in_stuck_patterns($brd, $t->{'pull_mode'}));
        set_subtree_as_deadlocked($t, $e);
    }
    return;
}

sub check_for_deadlock_zone_moves ($brd, $moves) {
    for my $i (0 .. $#$moves) {
        my $p = $Index_to_p[$moves->[$i]{'to'}];
        next if vec($brd, $p, 8) & DEADLOCK_ZONE;
        my $kill = { %{ $moves->[$i] } };
        $kill->{'kill'} = 1;
        return ($kill);
    }
    return @$moves;
}

sub detect_kill_moves ($b_in, $brd, $moves, $pull_mode, $search_mode, $h) {
    my @m = @$moves;
    @m = check_for_deadlock_zone_moves($b_in, \@m)
        if $search_mode == DEADLOCK_SEARCH;
    @m = check_for_k_dist_moves($brd, \@m, $h)
        if $search_mode == K_DIST_SEARCH;
    @m = reduce_moves_in_wobblers_search(\@m)
        if $search_mode == WOBBLERS_SEARCH;
    @m = reduce_moves_in_rooms_deadlock_search(\@m, $h)
        if $search_mode == ROOMS_DEADLOCK_SEARCH;
    @m = reduce_moves_in_xy_search($brd, \@m)
        if $search_mode == XY_SEARCH;
    return @m;
}

sub find_possible_moves ($b_input, $pull_mode, $has_corral_ref, $search_mode, $h) {
    my @moves;
    my ($brd, $c, $corral_options, $possible_board);
    my $use_corral = 1;
    my $gd         = allocate_graph();
    $$has_corral_ref = 0;
    if ($pull_mode == 0) {
        _dz_masks();
        $c          = $b_input&.$NOT_DZ;
        $brd        = turn_fixed_boxes_into_walls($c);
        $Blok_boxes = _blok_boxvec($c) if $BLOK_REPLACES and $Blok_usable;
    }
    else {
        _dz_masks();
        $brd = $b_input&.$NOT_DZ;
    }
    $possible_board = get_possible_places($brd, $pull_mode, $search_mode);
    $use_corral     = 0 if $search_mode == DEADLOCK_SEARCH;
    $use_corral     = 0 if $search_mode == ROOMS_DEADLOCK_SEARCH;
    $use_corral     = 0 if $search_mode == MINI_SEARCH;
    $use_corral     = 0 if $search_mode == XY_SEARCH;
    $use_corral     = 0 if $search_mode == K_DIST_SEARCH;
    if ($search_mode == IGNORE_CORRAL) {
        $use_corral  = 0;
        $search_mode = NORMAL;
    }
    $use_corral = 0 if $h->{'perimeter_found'};
    $use_corral = 0 if $h->{'enable_inefficient_moves'};
    if ($use_corral and $pull_mode == 0) {
        ($$has_corral_ref, $corral_options) = detect_corral($brd);
    }
    for my $i (0 .. $Index_num - 1) {
        my $p = $Index_to_p[$i];
        if ($$has_corral_ref) {
            next if (vec($corral_options, $p, 8) & BOX) == 0;
        }
        if ($search_mode == REV_SEARCH and $pull_mode and $h->{'perimeter_found'} == 0) {
            next if vec($h->{'wallified'}, $p, 8);
        }
        next if (vec($brd, $p, 8) & BOX) == 0;
        next if box_can_be_moved($brd, $i, $pull_mode) == 0;
        my @box_moves = find_box_moves($brd, $i, $pull_mode, $search_mode, $possible_board, $gd);
        @box_moves = remove_deadlocked_moves($brd, \@box_moves, $pull_mode, $search_mode, $h);
        @box_moves = detect_kill_moves($b_input, $brd, \@box_moves, $pull_mode, $search_mode, $h);
        if (@box_moves == 1 and $box_moves[0]{'kill'}) {
            @moves = ($box_moves[0]);
            last;
        }
        push @moves, @box_moves;
    } ## end for my $i (0 .. $Index_num...)
    if ($search_mode == BASE_SEARCH) {
        @moves = mark_sink_squares_moves($brd, \@moves);
    }
    return @moves;
} ## end sub find_possible_moves

sub has_pull_moves ($brd) {
    my $h = init_helper();
    my ($corral, @moves);
    @moves = find_possible_moves($brd, 1, \$corral, NORMAL, $h);
    return @moves > 0 ? 1 : 0;
}

sub clear_xy_boxes ($brd, $pull_mode) {
    my $h = init_helper();
    while (1) {
        my $corral = 0;
        my @moves  = find_possible_moves($brd, $pull_mode, \$corral, XY_SEARCH, $h);
        if (@moves > 0 and $moves[0]{'kill'}) {
            my $p = $Index_to_p[$moves[0]{'from'}];
            vec($brd, $p, 8) &= 0xFF ^ BOX;
            $brd = expand_sokoban_cloud($brd);
        }
        else {
            return $brd;
        }
    }
    return $brd;
} ## end sub clear_xy_boxes

sub board_contains_more_deadlocks ($new_board, $old_board) {
    for my $p (0 .. $Ncells - 1) {
        next unless (vec($new_board, $p, 8) & DEADLOCK_ZONE);
        return 1 if (vec($old_board, $p, 8) & DEADLOCK_ZONE) == 0;
    }
    return 0;
}

sub insert_positions_to_deadlock_cache ($positions, $pos_num, $result) {
    for my $i (0 .. $pos_num - 1) {
        next unless ($positions->[$i]{'position_deadlocked'} or $result == IS_DEADLOCK);
        insert_to_deadlock_cache($positions->[$i]{'position_hash'}, IS_DEADLOCK, $positions->[$i]{'pull_mode'}, DEADLOCK_SEARCH);
    }
    if ($result == NOT_DEADLOCK) {
        my $p = $positions->[$pos_num - 1];
        do {
            insert_to_deadlock_cache($p->{'position_hash'}, NOT_DEADLOCK, $p->{'pull_mode'}, DEADLOCK_SEARCH);
            $p = $p->{'father'};
        } while (defined $p);
    }
    return;
}

sub get_components_around_place ($p, $d) {
    my @list;
    for my $k (0 .. 3) {
        my $q = $p + $Delta_p[$k];
        next if $d->[$q] == 1000000;
        push @list, $d->[$q];
    }
    return @list;
}

sub keep_two_components ($brd, $d, $comp1, $comp2, $pull_mode) {
    my $group;
    $group = $ZERO_BOARD;
    for my $p (0 .. $Ncells - 1) {
        vec($group, $p, 8) = 1
            if $d->[$p] == $comp1
            or $d->[$p] == $comp2;
    }
    $brd = init_deadlock_zone_from_group($brd, $group, $pull_mode);
    return $brd;
}

sub is_better_deadlock_score ($new_score, $old_score) {
    return 1 if $new_score->{'connectivity'} < $old_score->{'connectivity'};
    return 0 if $new_score->{'connectivity'} > $old_score->{'connectivity'};
    return 1 if $new_score->{'boxes_in_level'} < $old_score->{'boxes_in_level'};
    return 0 if $new_score->{'boxes_in_level'} > $old_score->{'boxes_in_level'};
    return 1 if $new_score->{'hotspots'} < $old_score->{'hotspots'};
    return 0 if $new_score->{'hotspots'} > $old_score->{'hotspots'};
    return 0;
}

sub choose_deadlock_son ($deadlock_positions, $deadlock_pos_num, $son_ref) {
    my $res = -1;
    my $best_score;
    for my $i (0 .. $deadlock_pos_num - 1) {
        my $pi = $deadlock_positions->[$i];
        next if $pi->{'position_deadlocked'};
        for my $j (0 .. $pi->{'moves_num'} - 1) {
            next if $pi->{'move_deadlocked'}[$j];
            next if defined $pi->{'place_in_positions'}[$j];
            next unless ($res == -1 or is_better_deadlock_score($pi->{'scores'}[$j], $best_score));
            $res        = $i;
            $$son_ref   = $j;
            $best_score = { %{ $pi->{'scores'}[$j] } };
        }
    }
    return $res;
} ## end sub choose_deadlock_son

sub son_can_break_free ($p, $pull_mode) {
    my ($brd, $c);
    $brd = $p->{'board'};
    if ($pull_mode == 0) {
        return 1 if work_left_in_deadlock_zone($brd) == 0;
    }
    for my $i (0 .. $p->{'moves_num'} - 1) {
        next     if $p->{'move_deadlocked'}[$i];
        return 1 if $p->{'scores'}[$i]{'hotspots'} == 0;
        return 1 if $p->{'scores'}[$i]{'connectivity'} == 1;
        return 1
            if (($Cache{ join '/', $p->{'hashes'}[$i], $pull_mode, DEADLOCK_SEARCH } // $CACHE_MISS)->[0]) == NOT_DEADLOCK;
        next unless ($pull_mode);
        $c = $brd;
        $c = apply_move($c, $p->{'moves'}[$i], DEADLOCK_SEARCH);
        return 1 if board_contains_more_deadlocks($c, $brd);
        return 1 if exited_deadlock_zone($c);
    }
    return 0;
} ## end sub son_can_break_free

sub mark_deadlocked_sons_using_cache ($deadlock_positions, $deadlock_pos_num) {
    my $node = $deadlock_pos_num - 1;
    my $p    = $deadlock_positions->[$node];
    for my $i (0 .. $p->{'moves_num'} - 1) {
        next
            unless ((($Cache{ join '/', $p->{'hashes'}[$i], $p->{'pull_mode'}, DEADLOCK_SEARCH } // $CACHE_MISS)->[0]) ==
                IS_DEADLOCK);
        set_leaf_as_deadlock($deadlock_positions, $deadlock_pos_num, $node, $i)
            unless defined $p->{'place_in_positions'}[$i];
    }
    return;
}

sub should_reevaluate ($queries_num) {
    return 0 if $queries_num < (MAX_DEADLOCK_SEARCH * 2);
    return 0 if $queries_num & ($queries_num - 1);
    return 1;
}

sub get_girl_distance ($brd) {
    my $sum = 0;
    for my $p (0 .. $Ncells - 1) {
        $sum += $Girl_distance->[$p] if vec($brd, $p, 8) & BOX;
    }
    return $sum;
}

sub prepare_vector_of_basic_features ($s, $pull_mode, $features) {
    my $n            = 0;
    my $packed       = $s->{'packed_boxes'};
    my $tgt          = $s->{'boxes_on_targets'};
    my $connectivity = $s->{'connectivity'};
    my $dist         = $s->{'dist_to_targets'};
    my $overlap      = $s->{'overlap'};
    if ($pull_mode == 0) {
        $features->[$n++] = $packed * $Inv_n_boxes;
        $features->[$n++] = $tgt * $Inv_n_boxes;
        $features->[$n++] = $connectivity * $Inv_n_boxes;
        $features->[$n++] = $dist * $Dist_normalizer;
        $features->[$n++] = $overlap * $Inv_n_boxes;
        $features->[$n++] = $Gamma_table[$Global_boxes_in_level - $tgt];
        $features->[$n++] = $Gamma_table[$Global_boxes_in_level];
        $features->[$n++] = 1;
        return $n;
    }
    $features->[$n++] = $tgt * $Inv_n_boxes;
    $features->[$n++] = $connectivity * $Inv_n_boxes;
    $features->[$n++] = $dist * $Dist_normalizer;
    $features->[$n++] = $Gamma_table[$tgt];
    $features->[$n++] = $Gamma_table[$Global_boxes_in_level];
    $features->[$n++] = 1;
    return $n;
} ## end sub prepare_vector_of_basic_features

sub score_to_value ($s, $pull_mode) {
    my @features;
    my $sum = 0;
    my $n   = prepare_vector_of_basic_features($s, $pull_mode, \@features);
    if ($pull_mode) {
        for my $i (0 .. $n - 1) {
            $sum += $features[$i] * $Pull_weights[$i];
        }
    }
    else {
        for my $i (0 .. $n - 1) {
            $sum += $features[$i] * $Push_weights[$i];
        }
    }
    return $sum;
} ## end sub score_to_value

sub is_better_score ($new_score, $old_score, $pull_mode, $search_mode) {
    if (   $search_mode == HF_SEARCH
        or $search_mode == BICON_SEARCH
        or $search_mode == MAX_DIST_SEARCH
        or $search_mode == MAX_DIST_SEARCH2)
    {
        return is_better_hf_score($new_score, $old_score, $pull_mode);
    }
    return is_better_snail_score($new_score, $old_score, $pull_mode)
        if $search_mode == SNAIL_SEARCH;
    if ($search_mode == NETLOCK_SEARCH) {
        return 1 if $new_score->{'connectivity'} < $old_score->{'connectivity'};
        return 0 if $new_score->{'connectivity'} > $old_score->{'connectivity'};
        return 1 if $new_score->{'boxes_on_targets'} < $old_score->{'boxes_on_targets'};
        return 0 if $new_score->{'boxes_on_targets'} > $old_score->{'boxes_on_targets'};
        return 1 if $new_score->{'rooms_score'} > $old_score->{'rooms_score'};
        return 0 if $new_score->{'rooms_score'} < $old_score->{'rooms_score'};
        return 1 if $new_score->{'imagine'} > $old_score->{'imagine'};
        return 0 if $new_score->{'imagine'} < $old_score->{'imagine'};
        return 0;
    }
    if ($search_mode == NAIVE_SEARCH) {
        my $new_val = $new_score->{'dist_to_targets'};
        my $old_val = $old_score->{'dist_to_targets'};
        return 1 if $new_val < $old_val;
        return 0 if $new_val > $old_val;
        return 1 if $new_score->{'packed_boxes'} > $old_score->{'packed_boxes'};
        return 0 if $new_score->{'packed_boxes'} < $old_score->{'packed_boxes'};
        return 0;
    }
    return is_better_rev_score($new_score, $old_score, $pull_mode)
        if $search_mode == REV_SEARCH;
    if ($search_mode == K_DIST_SEARCH) {
        return 1 if $new_score->{'boxes_in_level'} < $old_score->{'boxes_in_level'};
        return 0 if $new_score->{'boxes_in_level'} > $old_score->{'boxes_in_level'};
        return 1 if $new_score->{'connectivity'} < $old_score->{'connectivity'};
        return 0 if $new_score->{'connectivity'} > $old_score->{'connectivity'};
        return 0;
    }
    if ($search_mode == GIRL_SEARCH) {
        my $val_new = score_to_value($new_score, $pull_mode);
        my $val_old = score_to_value($old_score, $pull_mode);
        return 1 if $val_new > $val_old;
        return 0;
    }
    if ($search_mode != NORMAL) {
        if ($search_mode != BASE_SEARCH) {
            Carp::confess('verify search mode')
                if $search_mode != FORWARD_WITH_BASES;
        }
    }
    return 1 if $new_score->{'boxes_in_level'} < $old_score->{'boxes_in_level'};
    return 0 if $new_score->{'boxes_in_level'} > $old_score->{'boxes_in_level'};
    if ($pull_mode == 0) {
        return 1 if $new_score->{'packed_boxes'} > $old_score->{'packed_boxes'};
        return 0 if $new_score->{'packed_boxes'} < $old_score->{'packed_boxes'};
        return 1 if $new_score->{'connectivity'} < $old_score->{'connectivity'};
        return 0 if $new_score->{'connectivity'} > $old_score->{'connectivity'};
        return 1 if $new_score->{'rooms_score'} < $old_score->{'rooms_score'};
        return 0 if $new_score->{'rooms_score'} > $old_score->{'rooms_score'};
        return 1 if $new_score->{'out_of_plan'} < $old_score->{'out_of_plan'};
        return 0 if $new_score->{'out_of_plan'} > $old_score->{'out_of_plan'};
        return 1 if $new_score->{'hotspots'} < $old_score->{'hotspots'};
        return 0 if $new_score->{'hotspots'} > $old_score->{'hotspots'};
        return 1 if $new_score->{'dist_to_targets'} > $old_score->{'dist_to_targets'};
        return 0 if $new_score->{'dist_to_targets'} < $old_score->{'dist_to_targets'};
        return 0;
    } ## end if ($pull_mode == 0)
    return 1 if $new_score->{'connectivity'} < $old_score->{'connectivity'};
    return 0 if $new_score->{'connectivity'} > $old_score->{'connectivity'};
    return 1 if $new_score->{'boxes_on_targets'} < $old_score->{'boxes_on_targets'};
    return 0 if $new_score->{'boxes_on_targets'} > $old_score->{'boxes_on_targets'};
    return 1 if $new_score->{'rooms_score'} < $old_score->{'rooms_score'};
    return 0 if $new_score->{'rooms_score'} > $old_score->{'rooms_score'};
    return 1 if $new_score->{'dist_to_targets'} > $old_score->{'dist_to_targets'};
    return 0 if $new_score->{'dist_to_targets'} < $old_score->{'dist_to_targets'};
    return 0;
} ## end sub is_better_score

sub choose_advisor ($base_score, $moves_num, $scores, $criterion, $pull_mode) {
    my $best_move = -1;
    my $best_score;
    for my $i (0 .. $moves_num - 1) {
        next if $scores->[$i]{'packed_boxes'} < $base_score->{'packed_boxes'};
        if ($criterion == OPTIMIZE_PACKED) {
            next if $scores->[$i]{'packed_boxes'} <= $base_score->{'packed_boxes'};
        }
        elsif ($criterion == OPTIMIZE_CONNECTIVITY) {
            next if $scores->[$i]{'connectivity'} >= $base_score->{'connectivity'};
        }
        elsif ($criterion == OPTIMIZE_ROOMS) {
            next if $scores->[$i]{'rooms_score'} >= $base_score->{'rooms_score'};
        }
        elsif ($criterion == OPTIMIZE_HOTSPOTS) {
            next if $scores->[$i]{'hotspots'} >= $base_score->{'hotspots'};
        }
        elsif ($criterion == OPTIMIZE_OUT_OF_PLAN) {
            next if $scores->[$i]{'out_of_plan'} >= $base_score->{'out_of_plan'};
        }
        else {
            Carp::confess("bad optimizer\n");
        }
        if ($best_move == -1) {
            $best_move  = $i;
            $best_score = { %{ $scores->[$i] } };
        }
        next unless (is_better_score($scores->[$i], $best_score, $pull_mode, NORMAL));
        $best_score = { %{ $scores->[$i] } };
        $best_move  = $i;
    } ## end for my $i (0 .. $moves_num...)
    return $best_move;
} ## end sub choose_advisor

sub set_default_advisor ($base_score, $moves_num, $moves, $scores, $pull_mode, $search_mode, $already_expanded, $l) {
    my $s = {%$base_score};
    for my $i (0 .. $moves_num - 1) {
        if ($pull_mode) {
            next if vec($Target_holes, $Index_to_p[$moves->[$i]{'from'}], 8);
        }
        next if $already_expanded->[$i];
        next unless (is_better_score($scores->[$i], $s, $pull_mode, $search_mode));
        $s = { %{ $scores->[$i] } };
        $l->{'pack'} = $i;
    }
    return;
}

sub is_better_element ($q, $first, $second) {
    my $pull_mode   = $q->{'t'}{'pull_mode'};
    my $search_mode = $q->{'t'}{'search_mode'};
    my $e1          = $q->{'t'}{'expansions'}[$first];
    my $e2          = $q->{'t'}{'expansions'}[$second];
    return 1 if $e1->{'best_weight'} < $e2->{'best_weight'};
    return 0 if $e1->{'best_weight'} > $e2->{'best_weight'};
    my (%s1, %s2);
    @s1{ @{ +SCORE_KEYS } } = unpack 'd13', $e1->{'best_score'};
    @s2{ @{ +SCORE_KEYS } } = unpack 'd13', $e2->{'best_score'};
    return 1
        if is_better_score(\%s1, \%s2, $pull_mode, $search_mode);
    return 0
        if is_better_score(\%s2, \%s1, $pull_mode, $search_mode);
    return 1 if $first < $second;
    return 0;
}

sub heapify ($q, $i) {
    return if $q->{'heap_size'} == 0;
    my $elements = $q->{'elements'};
    my $l        = ($i * 2 + 1);
    my $r        = ($i * 2 + 2);
    my $largest  = $i;
    if ($l < $q->{'heap_size'}) {
        $largest = $l
            if is_better_element($q, $elements->[$l], $elements->[$i]);
    }
    if ($r < $q->{'heap_size'}) {
        $largest = $r
            if is_better_element($q, $elements->[$r], $elements->[$largest]);
    }
    if ($largest != $i) {
        @$elements[$i, $largest] = @$elements[$largest, $i];
        heapify($q, $largest);
    }
    return;
} ## end sub heapify

sub extarct_max ($q) {
    return -1 if $q->{'heap_size'} == 0;
    my $res = $q->{'elements'}[0];
    $q->{'elements'}[0] = $q->{'elements'}[$q->{'heap_size'} - 1];
    $q->{'heap_size'}--;
    heapify($q, 0);
    return $res;
}

sub heap_insert ($q, $val) {
    $q->{'heap_size'}++;
    my $i = $q->{'heap_size'} - 1;
    while ($i > 0
        and is_better_element($q, $val, $q->{'elements'}[int(($i - 1) / 2)]))
    {
        $q->{'elements'}[$i] = $q->{'elements'}[int(($i - 1) / 2)];
        $i = int(($i - 1) / 2);
    }
    $q->{'elements'}[$i] = $val;
    return;
}

sub remove_value_from_queue ($q, $val) {
    my $i;
    for ($i = 0; $i < $q->{'heap_size'}; $i++) {
        last if $q->{'elements'}[$i] == $val;
    }
    Carp::confess("can't find element") if $i == $q->{'heap_size'};
    while ($i > 0) {
        $q->{'elements'}[$i] = $q->{'elements'}[int(($i - 1) / 2)];
        $i = int(($i - 1) / 2);
    }
    extarct_max($q);
    return;
}

sub get_k_dist_pos_and_son ($positions, $pos_num, $pos_ref, $son_ref) {
    $$pos_ref = -1;
    my $best_score;
    for my $i (0 .. $pos_num - 1) {
        my $pi = $positions->[$i];
        next if $pi->{'position_deadlocked'};
        for my $j (0 .. $pi->{'moves_num'} - 1) {
            next if $pi->{'move_deadlocked'}[$j];
            next if defined $pi->{'place_in_positions'}[$j];
            next unless ($$pos_ref == -1 or is_better_score($pi->{'scores'}[$j], $best_score, 1, K_DIST_SEARCH));
            $best_score = { %{ $pi->{'scores'}[$j] } };
            $$pos_ref   = $i;
            $$son_ref   = $j;
        }
    }
    return;
} ## end sub get_k_dist_pos_and_son

sub set_best_move ($t, $e) {
    my $best_weight = 1000000;
    my ($best_score, $best_place);
    $e->{'best_move'}   = -1;
    $e->{'best_weight'} = 1000000;
    my $node_exp   = $t->{'node_expansion'};
    my $node_dead  = $t->{'node_deadlocked'};
    return if $node_dead->[$e->{'node'}];
    my $mh_move = $t->{'mh_move'};
    my $mh_node = $t->{'mh_node'};
    my $mh_dead = $t->{'mh_deadlocked'};
    my $mp      = $e->{'move_hash_place'};

    for my $i (0 .. $e->{'moves_num'} - 1) {
        next if $mh_dead->[$mp + $i];
        my $node_place = $mh_node->[$mp + $i];
        next                             if $node_exp->[$node_place] != -1;
        if ($node_dead->[$node_place]) {
            $mh_dead->[$mp + $i] = 1;
            next;
        }
        my $weight = ($mh_move->[$mp + $i] >> 30 & 3) - 1;
        next if $weight > $best_weight;
        my $s = score_hash($t, $node_place);
        if ($weight < $best_weight) {
            $best_weight      = $weight;
            $e->{'best_move'} = $i;
            $best_score       = $s;
            $best_place       = $node_place;
            next;
        }
        next if $t->{'search_mode'} == GIRL_SEARCH;
        next unless (is_better_score($s, $best_score, $t->{'pull_mode'}, $t->{'search_mode'}));
        $best_weight      = $weight;
        $e->{'best_move'} = $i;
        $best_score       = $s;
        $best_place       = $node_place;
        next;
    } ## end for my $i (0 .. $e->{'moves_num'...})
    if ($best_weight != 1000000) {
        $e->{'best_score'}  = $t->{'node_score'}[$best_place];
        $e->{'best_weight'} = $e->{'weight'} + $best_weight;
    }
    else {
        set_deadlock_status($t, $e);
    }
    return;
} ## end sub set_best_move

sub best_move_in_tree ($t, $label, $best_pos_ref, $best_son_ref) {
    $$best_son_ref = -1;
    $$best_pos_ref = -1;
    my $weight = 1000000;
    do {
        my $q_move = extarct_max($t->{'queues'}[$label]);
        return 1000000 if $q_move == -1;
        my $e = $t->{'expansions'}[$q_move];
        Carp::confess('should have a move') if $e->{'best_move'} == -1;
        if (best_move_is_available($t, $e)) {
            $$best_pos_ref = $q_move;
            $$best_son_ref = $e->{'best_move'};
            $weight        = $e->{'best_weight'};
        }
        set_best_move($t, $e);
        heap_insert($t->{'queues'}[$label], $q_move)
            if $e->{'best_move'} != -1;
    } while ($$best_son_ref == -1);
    return $weight;
} ## end sub best_move_in_tree

sub add_label_to_last_node ($t, $label, $h) {
    my $last_node = $t->{'expansions_num'} - 1;
    Carp::confess('negative label') if $label < 0;
    $t->{'expansions'}[$last_node]{'label'} = $label;
    if ($label >= $t->{'labels_num'}) {
        Carp::confess('label jumped?') if $label > $t->{'labels_num'};
        if ($label == $t->{'labels_num'}) {
            $t->{'queues'}[$label] //= {};
            init_queue($t->{'queues'}[$label], $t);
            $t->{'labels_num'}++;
        }
    }
    return
        if $t->{'search_mode'} == GIRL_SEARCH and $h->{'perimeter_found'} == 0;
    set_best_move($t, $t->{'expansions'}[$last_node])
        if $h->{'perimeter_found'};
    heap_insert($t->{'queues'}[$label], $last_node)
        if $t->{'expansions'}[$last_node]{'best_move'} != -1;
    return;
} ## end sub add_label_to_last_node

sub insert_all_tree_nodes_to_queues ($t) {
    Carp::confess("shouldn't be here")
        if $t->{'search_mode'} != GIRL_SEARCH;
    for my $i (0 .. $t->{'labels_num'} - 1) {
        Carp::confess('queue is active')
            if $t->{'queues'}[$i]{'heap_size'} != 0;
    }
    for my $i (0 .. $t->{'expansions_num'} - 1) {
        my $e = $t->{'expansions'}[$i];
        set_best_move($t, $e);
        heap_insert($t->{'queues'}[$e->{'label'}], $i)
            if $e->{'best_move'} != -1;
    }
    return;
} ## end sub insert_all_tree_nodes_to_queues

sub replace_in_queue ($t, $e) {
    my $label = $e->{'label'};
    remove_value_from_queue($t->{'queues'}[$label], $e->{'index'});
    heap_insert($t->{'queues'}[$label], $e->{'index'})
        if $e->{'best_move'} != -1;
    return;
}

sub check_if_perimeter_reached ($t, $h) {
    my $best_depth = 1000000;
    my $best_son   = -1;
    my $depth;
    my $e_depth = 0;
    my $e       = $t->{'expansions'}[$t->{'expansions_num'} - 1];
    my $mh_node = $t->{'mh_node'};
    my $mh_dead = $t->{'mh_deadlocked'};
    my $mp      = $e->{'move_hash_place'};
    $e_depth = 2000 + $e->{'weight'} if $e->{'weight'} < 0;

    for my $i (0 .. $e->{'moves_num'} - 1) {
        my $place = $mh_node->[$mp + $i];
        next if is_in_perimeter($t->{'node_hash'}[$place], \$depth, 1 - $t->{'pull_mode'}) == 0;
        next if $e->{'weight'} < 0 and $depth >= $e_depth;
        if ($mh_dead->[$mp + $i]) {
            next if $t->{'search_mode'} == GIRL_SEARCH;
            Carp::confess('perimeter move is deadlocked1');
        }
        if ($t->{'node_deadlocked'}[$place]) {
            Carp::confess('perimeter move is deadlocked2');
        }
        next if $t->{'node_expansion'}[$place] != -1;
        next unless ($depth < $best_depth);
        $best_depth = $depth;
        $best_son   = $i;
    } ## end for my $i (0 .. $e->{'moves_num'...})
    if ($h->{'perimeter_found'}) {
    }
    if ($best_son != -1) {
        if ($h->{'perimeter_found'} == 0 and $t->{'search_mode'} == GIRL_SEARCH) {
            insert_all_tree_nodes_to_queues($t);
        }
        $e->{'weight'} = -2000 + ($best_depth + 1);
        $t->{'mh_move'}[$mp + $best_son] &= ~MOVE_WEIGHT;
        set_best_move($t, $e);
        replace_in_queue($t, $e);
        $h->{'perimeter_found'} = 1;
        return 1;
    }
    return 0;
} ## end sub check_if_perimeter_reached

sub update_best_so_far ($t, $best_so_far_ref, $new_node, $pull_mode, $search_mode) {
    if (not defined $$best_so_far_ref) {
        $$best_so_far_ref = $new_node;
        return 1;
    }
    my $bsf = $$best_so_far_ref;
    if ($search_mode == GIRL_SEARCH) {
        if (is_better_score(score_hash($t, $new_node->{'node'}), score_hash($t, $bsf->{'node'}), $pull_mode, $search_mode)) {
            $$best_so_far_ref = $new_node;
            return 1;
        }
        return 0;
    }
    if (is_better_score(score_hash($t, $new_node->{'best_past'}), score_hash($t, $bsf->{'best_past'}), $pull_mode, $search_mode)) {
        $$best_so_far_ref = $new_node;
        return 1;
    }
    return 0;
} ## end sub update_best_so_far

sub best_node_in_tree ($t) {
    my $e          = $t->{'expansions'};
    my $node_dead  = $t->{'node_deadlocked'};
    my $res;
    for my $i (0 .. $t->{'expansions_num'} - 1) {
        next if $node_dead->[$e->[$i]{'node'}];
        if (not defined $res) {
            $res = $e->[$i];
            next;
        }
        next if $e->[$i]{'depth'} == 0;
        if ($res->{'depth'} == 0 and $e->[$i]{'depth'} != 0) {
            $res = $e->[$i];
            next;
        }
        next if $e->[$i]{'has_corral'};
        if ($res->{'has_corral'} and $e->[$i]{'has_corral'} == 0) {
            $res = $e->[$i];
            next;
        }
        $res = $e->[$i]
            if is_better_score(
                score_hash($t, $e->[$i]{'node'}),
                score_hash($t, $res->{'node'}),
                $t->{'pull_mode'}, $t->{'search_mode'}
            );
    } ## end for my $i (0 .. $t->{'expansions_num'...})
    return $res;
} ## end sub best_node_in_tree

sub set_rev_advisor ($brd, $base_score, $moves_num, $moves, $scores, $pull_mode, $search_mode, $already_expanded, $l) {
    my $s = {%$base_score};
    for my $i (0 .. $moves_num - 1) {
        if ($pull_mode == 0) {
            if (vec($Target_holes, $Index_to_p[$moves->[$i]{'to'}], 8)) {
                $l->{'pack'} = $i;
                return;
            }
        }
        next if $already_expanded->[$i];
        next unless (is_better_score($scores->[$i], $s, $pull_mode, $search_mode));
        $s = { %{ $scores->[$i] } };
        $l->{'pack'} = $i;
    }
    return;
} ## end sub set_rev_advisor

sub set_values_to_moves_tree ($t, $e) {
    my $mh_node = $t->{'mh_node'};
    my $mh_dead = $t->{'mh_deadlocked'};
    my $mp      = $e->{'move_hash_place'};
    score_set($t, $e->{'node'}, SC_VALUE,
        unpack('f', pack('f', score_to_value(score_hash($t, $e->{'node'}), $t->{'pull_mode'}))));
    for my $i (0 .. $e->{'moves_num'} - 1) {
        next if $mh_dead->[$mp + $i];
        my $node_place = $mh_node->[$mp + $i];
        score_set($t, $node_place, SC_VALUE,
            unpack('f', pack('f', score_to_value(score_hash($t, $node_place), $t->{'pull_mode'}))));
    }
    return;
} ## end sub set_values_to_moves_tree

sub find_best_RL_parking_node ($t) {
    my $max_value = -1000000;
    my $best_node;
    my $expansions        = $t->{'expansions'};
    my $max_allowed_depth = MAX_SOL_LEN - $Global_boxes_in_level;
    for my $i (0 .. $t->{'expansions_num'} - 1) {
        next if $expansions->[$i]{'depth'} >= $max_allowed_depth;
        next if $t->{'node_deadlocked'}[$expansions->[$i]{'node'}];
        my $value = score_to_value(score_hash($t, $expansions->[$i]{'node'}), 1);
        next unless ($value > $max_value);
        $max_value = $value;
        $best_node = $expansions->[$i];
    }
    my $dist = 0.1;
    my $e    = $best_node;
    while (defined $e) {
        my $value = score_to_value(score_hash($t, $e->{'node'}), 1);
        $best_node = $e if $value > ($max_value - $dist);
        $e         = $e->{'father'};
    }
    Carp::confess('could not find chain') unless defined $best_node;
    return $best_node;
} ## end sub find_best_RL_parking_node

sub conclude_parking ($t, $e, $h) {
    $e = find_best_RL_parking_node($t)
        if $t->{'search_mode'} == GIRL_SEARCH;
    if (not defined $e) {
        $h->{'parking_order_num'} = 0;
        return;
    }
    if ($e->{'depth'} >= (MAX_SOL_LEN - $Global_boxes_in_level - 2)) {
        $h->{'parking_order_num'} = 0;
        return;
    }
    get_parking_plan($t, $e, $h);
    return;
}

sub fill_girl_scores ($brd, $s, $pull_mode, $h) {
    $s->{'dist_to_targets'} = get_girl_distance($brd);
    if ($pull_mode == 0) {
        $s->{'packed_boxes'} = score_parked_boxes($brd, $h);
        $s->{'overlap'}      = overlap_score($brd, $h);
    }
    return;
}

sub init_imagine ($full, $n, $h) {
    my $p = 0;
    my ($brd, $fixed);
    my $permanent = 0;
    Carp::confess('imagine not allocated') unless defined $h->{'imagine'};
    my $im = $h->{'imagine'};
    $im->{'imagined_boards'}    //= [];
    $im->{'fixed_at_step'}      //= [];
    $im->{'imagine_packed_num'} //= [];
    $im->{'imagined_boards_num'} = 0;

    for my $i (0 .. $n - 1) {
        return if $full->[$i]{'from'} == -1;
    }
    for my $i (0 .. $n - 1) {
        next unless ($full->[$i]{'from'} == $full->[$i]{'to'});
        Carp::confess('shifting a box in place');
    }
    $brd = $Initial_board;
    $brd&.=$NOT_BOX;
    $brd&.=$NOT_SOKOBAN;
    $fixed = $ZERO_BOARD;
    for my $i (0 .. $n - 1) {
        my $to_p = $Index_to_p[$full->[$i]{'to'}];
        if ($full->[$i]{'until'} == -1) {
            $permanent++;
            vec($fixed, $to_p, 8) = 1;
        }
        if ($full->[$i]{'until'} == -1 and $full->[$i]{'from'} != -2) {
            $im->{'imagined_boards'}[$im->{'imagined_boards_num'}]    = $brd;
            $im->{'fixed_at_step'}[$im->{'imagined_boards_num'}]      = $fixed;
            $im->{'imagine_packed_num'}[$im->{'imagined_boards_num'}] = $permanent;
            $im->{'imagined_boards_num'}++;
        }
        $to_p = $Index_to_p[$full->[$i]{'to'}];
        vec($brd, $to_p, 8) |= BOX;
        next unless ($full->[$i]{'from'} >= 0);
        my $from_p = $Index_to_p[$full->[$i]{'from'}];
        vec($brd, $from_p, 8) &= 0xFF ^ BOX;
    } ## end for my $i (0 .. $n - 1)
    if ($im->{'imagined_boards_num'} == 0) {
        Carp::confess('corrupted plan') if $n != $Global_boxes_in_level;
        $im->{'imagined_boards'}[0]    = $brd;
        $im->{'fixed_at_step'}[0]      = $fixed;
        $im->{'imagine_packed_num'}[0] = $permanent;
        $im->{'imagined_boards_num'}   = 1;
    }
    return;
} ## end sub init_imagine

sub save_full_parking_order ($h) {
    for my $i (0 .. $h->{'parking_order_num'} - 1) {
        $h->{'full_parking_order'}[$i] = { %{ $h->{'parking_order'}[$i] } };
    }
    $h->{'full_parking_order_num'} = $h->{'parking_order_num'};
    for my $i (0 .. $h->{'parking_order_num'} - 1) {
        vec($h->{'used_in_plan'}, $Index_to_p[$h->{'full_parking_order'}[$i]{'to'}], 8) = 1;
    }
    init_imagine($h->{'full_parking_order'}, $h->{'full_parking_order_num'}, $h);
    return;
}

sub reduce_parking_order ($h) {
    my $init_num      = 0;
    my $parking_order = $h->{'parking_order'};
    save_full_parking_order($h);
    for my $i (0 .. $h->{'parking_order_num'} - 1) {
        $init_num++ if $parking_order->[$i]{'from'} == -2;
    }
    $h->{'boxes_were_removed'} = ($init_num == $Global_boxes_in_level ? 0 : 1);
    keep_only_perm($h) if $h->{'boxes_were_removed'} == 0;
    return;
}

sub get_imagined_board ($brd, $relevant_board_ref, $h) {
    Carp::confess('imagine not allocated') unless defined $h->{'imagine'};
    my $im           = $h->{'imagine'};
    my $packed_boxes = score_parked_boxes($brd, $h);
    if ($packed_boxes == $Global_boxes_in_level) {
        $$relevant_board_ref = $im->{'imagined_boards_num'} - 1;
        return $brd;
    }
    my $i;
    for ($i = 0; $i < $im->{'imagined_boards_num'}; $i++) {
        last if $im->{'imagine_packed_num'}[$i] > $packed_boxes;
    }
    $$relevant_board_ref = $i;
    return $im->{'imagined_boards'}[$i];
} ## end sub get_imagined_board

sub compute_imagine_distance ($brd, $base_score, $moves, $scores, $search_mode, $h) {
    return if $search_mode == FORWARD_WITH_BASES or $search_mode == GIRL_SEARCH;
    my $ctx;
    my (@mat, @newrow);
    my $imagined;
    if ($search_mode == NORMAL) {
        my $relevant_board;
        $imagined = get_imagined_board($brd, \$relevant_board, $h);
    }
    else {
        $imagined = $h->{'imagined_hf_board'};
    }
    my @boxes_indices   = (grep {vec($brd,      $Index_to_p[$_], 8) & BOX} 0 .. $Index_num - 1);
    my @targets_indices = (grep {vec($imagined, $Index_to_p[$_], 8) & BOX} 0 .. $Index_num - 1);
    my $boxes_num       = scalar @boxes_indices;
    my $targets_num     = scalar @targets_indices;
    Carp::confess('box num mismatch2') if $boxes_num != $targets_num;
    for my $i (0 .. $boxes_num - 1) {
        my $from = $boxes_indices[$i];
        for my $j (0 .. $targets_num - 1) {
            $mat[$i][$j] = vec($Distance_from_to, $from * $Index_num + $targets_indices[$j], 32);
        }
        next unless (is_box_2x2_frozen_at_index($brd, $from));
        for my $j (0 .. $targets_num - 1) {
            $mat[$i][$j] = $targets_indices[$j] == $from ? 0 : 1000000;
        }
    }
    $ctx = Games::Sokoban::Solver::Munkres::context(\@mat);
    $base_score->{'dist_to_imagined'} = $ctx->{'weight'};
    for my $t (0 .. $#$moves) {
        my $from = $moves->[$t]{'from'};
        my $to   = $moves->[$t]{'to'};
        $scores->[$t] //= {};
        if ($from == $to) {
            $scores->[$t]{'dist_to_imagined'} = $base_score->{'dist_to_imagined'};
            next;
        }
        my $row = $boxes_num;
        for my $i (0 .. $boxes_num - 1) {
            next unless ($boxes_indices[$i] == $from);
            $row = $i;
            last;
        }
        Carp::confess('internal error') if $row == $boxes_num;
        for my $j (0 .. $targets_num - 1) {
            $newrow[$j] = vec($Distance_from_to, $to * $Index_num + $targets_indices[$j], 32);
        }
        if (is_box_2x2_frozen_after_move($brd, $moves->[$t])) {
            for my $j (0 .. $targets_num - 1) {
                $newrow[$j] = $targets_indices[$j] == $to ? 0 : 1000000;
            }
        }
        $scores->[$t]{'dist_to_imagined'} =
            Games::Sokoban::Solver::Munkres::with_row($ctx, $row, \@newrow);
    } ## end for my $t (0 .. $#$moves)
    return;
} ## end sub compute_imagine_distance

sub set_imagine_data_in_node ($t, $e, $h) {
    my (@moves, @scores);
    if ($t->{'search_mode'} == REV_SEARCH and $t->{'pull_mode'}) {
        set_rev_distance($t, $e, $h, \@moves, \@scores);
        return;
    }
    return if $t->{'pull_mode'};
    return if $t->{'search_mode'} == GIRL_SEARCH;
    return if $t->{'search_mode'} == NAIVE_SEARCH;
    return if $t->{'search_mode'} == REV_SEARCH;
    my $mh_move = $t->{'mh_move'};
    my $mh_node = $t->{'mh_node'};
    my $mp      = $e->{'move_hash_place'};

    for my $i (0 .. $e->{'moves_num'} - 1) {
        $moves[$i]  = move_unpack($mh_move->[$mp + $i]);
        $scores[$i] = {};
        get_score_of_node($t, $mh_node->[$mp + $i], $scores[$i]);
    }
    my $brd = $e->{'b'};
    my $base = score_hash($t, $e->{'node'});
    compute_imagine_distance($brd, $base, \@moves, \@scores, $t->{'search_mode'}, $h);
    $t->{'node_score'}[$e->{'node'}] = score_pack($base);
    for my $i (0 .. $e->{'moves_num'} - 1) {
        my $place = $mh_node->[$mp + $i];
        score_set($t, $place, SC_DIST_TO_IMAGINED, $scores[$i]{'dist_to_imagined'});
    }
    return;
} ## end sub set_imagine_data_in_node

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
        if $h->{'parking_order_num'} != $Global_boxes_in_level;
    $imagined = get_imagined_board($brd, \$relevant_board, $h);
    my $im = $h->{'imagine'};

    for my $p (0 .. $Ncells - 1) {
        next unless (vec($brd, $p, 8) & BOX);
        if (vec($im->{'imagined_boards'}[$relevant_board], $p, 8) & BOX) {
            $sum++
                if vec($im->{'fixed_at_step'}[$relevant_board], $p, 8) == 0;
        }
    }
    return $sum;
} ## end sub imagine_score

sub score_board ($brd, $s, $pull_mode, $search_mode, $h) {
    $s->{'boxes_on_targets'} = 0;
    $s->{'dist_to_targets'}  = 0;
    $s->{'dist_to_imagined'} = 0;
    $s->{'boxes_in_level'}   = $Global_boxes_in_level;
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
    $s->{'boxes_in_level'}   = (($brd&.$BOX_ONLY) =~ tr/\x00//c);
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
        fill_hf_scores($brd, $s, $pull_mode, $search_mode, $h);
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
        $s->{'packed_boxes'} = score_parked_boxes($brd, $h);
        $s->{'hotspots'}     = hotspots_score($brd);
        $s->{'out_of_plan'}  = get_out_of_plan_score($brd, $s->{'packed_boxes'}, $h);
        $s->{'imagine'}      = imagine_score($brd, $search_mode, $h);
    }
    return;
} ## end sub score_board

sub set_scores_to_moves ($brd, $moves, $scores, $hashes, $pull_mode, $search_mode, $h) {
    for my $i (0 .. $#$moves) {
        my $c;
        $c            = $brd;
        $c            = apply_move($c, $moves->[$i], $search_mode);
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
    set_scores_to_moves($brd, $moves, $p->{'scores'}, $p->{'hashes'}, $pull_mode, $p->{'search_mode'}, $h);
    set_hash_indicators($p);
    set_place_in_positions($p, $positions, $pos_num);
    for my $i (0 .. $moves_num - 1) {
        my $q = $p->{'place_in_positions'}[$i];
        next unless (defined $q);
        $p->{'move_deadlocked'}[$i] = 1 if $q->{'position_deadlocked'};
    }
    return;
} ## end sub fill_position_structures

sub release_positions ($positions) {
    delete @{$_}{ 'father', 'place_in_positions' } for @$positions;
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
    $p->{'board'}       = $brd;
    my @moves = find_possible_moves($brd, $pull_mode, \$p->{'has_corral'}, $search_mode, $h);
    $p->{'moves_num'}      = scalar @moves;
    $p->{'position_score'} = {};
    score_board($brd, $p->{'position_score'}, $pull_mode, $search_mode, $h);
    allocate_position_structures($p);
    fill_position_structures($p, $brd, \@moves, $pull_mode, $positions, 0, $h);
    $p->{'position_hash'}       = get_board_hash($brd);
    $p->{'position_deadlocked'} = 0;

    if ($p->{'moves_num'} == 0) {
        if (position_is_solved($p) == 0) {
            $p->{'position_deadlocked'} = 1;
        }
    }
    return;
} ## end sub set_first_position

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
    $p->{'board'}       = $brd;
    my @moves = find_possible_moves($brd, $pull_mode, \$p->{'has_corral'}, $node->{'search_mode'}, $h);
    $p->{'moves_num'}      = scalar @moves;
    $p->{'position_score'} = { %{ $node->{'scores'}[$son] } };
    allocate_position_structures($p);
    fill_position_structures($p, $brd, \@moves, $pull_mode, $positions, $pos_num, $h);
    $p->{'weight'}                      = $node->{'weight'} + $node->{'moves'}[$son]{'attr'}{'weight'};
    $p->{'position_hash'}               = get_board_hash($brd);
    $p->{'depth'}                       = $node->{'depth'} + 1;
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
} ## end sub expand_position

sub get_k_dist_forced_boxes ($b_in, $k_dist_val) {
    my ($brd, $c);
    my ($kd_forced, $kd_adj4, $kd_adj9);
    my @z;
    my $removed_all = 0;
    my ($local_adj_4, $local_adj_9);
    my ($pos,         $son);
    my $h = init_helper();
    $h->{'k_dist_value'} = $k_dist_val;
    $brd                 = $b_in;
    $brd                 = go_to_final_position_with_given_walls($brd);
    my $positions       = [map {{ 'board' => undef, 'moves_num' => 0 }} 1 .. (K_DIST_MAX_POSITIONS)];
    my $start_zones_num = mark_connectivities($brd, \@z);
    my $pos_num         = 0;

    for my $i (0 .. $start_zones_num - 1) {
        $c = $brd;
        $c = put_sokoban_in_zone($c, \@z, $i);
        set_first_position($c, 1, [$positions->[$pos_num]], K_DIST_SEARCH, $h);
        $pos_num++;
    }
    for my $i (0 .. $pos_num - 1) {
        direct_other_sons_to_position($positions->[$i], $positions, $pos_num);
    }
    while ($pos_num < K_DIST_MAX_POSITIONS) {
        get_k_dist_pos_and_son($positions, $pos_num, \$pos, \$son);
        last if $pos == -1;
        expand_position($positions->[$pos], $son, 1, $positions, $pos_num, $h);
        $pos_num++;
        my $new_pos = $positions->[$pos_num - 1];
        next unless ($new_pos->{'position_score'}{'boxes_in_level'} == 0);
        $removed_all = 1;
        last;
    }
    $kd_forced = $ZERO_BOARD;
    $kd_adj4   = $ZERO_BOARD;
    $kd_adj9   = $ZERO_BOARD;
    my $search_terminated = ($pos_num >= K_DIST_MAX_POSITIONS ? 1 : 0);
    if ($search_terminated or $removed_all) {
        release_positions($positions);
        return ($search_terminated, $kd_forced, $kd_adj4, $kd_adj9);
    }
    for my $p (0 .. $Ncells - 1) {
        vec($kd_forced, $p, 8) = 1;
        vec($kd_adj4,   $p, 8) = 10;
        vec($kd_adj9,   $p, 8) = 10;
    }
    for my $q (0 .. $pos_num - 1) {
        $brd = $positions->[$q]{'board'};
        ($local_adj_4, $local_adj_9) = count_adjacent_boxes($brd);
        for my $p (0 .. $Ncells - 1) {
            vec($kd_forced, $p, 8) = 0 if (vec($brd, $p, 8) & BOX) == 0;
            vec($kd_adj4,   $p, 8) = vec($local_adj_4, $p, 8)
                if vec($local_adj_4, $p, 8) < vec($kd_adj4, $p, 8);
            vec($kd_adj9, $p, 8) = vec($local_adj_9, $p, 8)
                if vec($local_adj_9, $p, 8) < vec($kd_adj9, $p, 8);
        }
    }
    release_positions($positions);
    return ($search_terminated, $kd_forced, $kd_adj4, $kd_adj9);
} ## end sub get_k_dist_forced_boxes

sub check_deadlock_using_k_dist_cache ($brd) {
    my ($forced, $adj_4, $adj_9, $b_wallified, $w);
    $b_wallified = turn_fixed_boxes_into_walls($brd);
    $b_wallified = turn_target_holes_into_walls($b_wallified);
    $w           = $b_wallified&.$NOT_BOX;
    $w&.=$NOT_SOKOBAN;
    my $hash = get_board_hash($w);
    my $n    = find_in_k_dist_hash($hash);
    if ($n == -1) {
        (my $search_terminated, $forced, $adj_4, $adj_9) = get_k_dist_forced_boxes($w, 5);
        if ($search_terminated) {
            (undef, $forced, $adj_4, $adj_9) = get_k_dist_forced_boxes($w, 3);
        }
        insert_to_k_dist_hash($hash, $w, $forced, $adj_4, $adj_9);
    }
    $n = find_in_k_dist_hash($hash);
    return 0 if $n == -1;
    ($adj_4, $adj_9) = count_adjacent_boxes($b_wallified);
    my $e = $K_dist_hash[$n];
    for my $p (0 .. $Ncells - 1) {
        if (vec($e->{'forced'}, $p, 8)) {
            if ((vec($brd, $p, 8) & BOX) == 0) {
                return 1;
            }
        }
        if (vec($adj_4, $p, 8) < vec($e->{'adj_4'}, $p, 8)) {
            return 1;
        }
        next unless (vec($adj_9, $p, 8) < vec($e->{'adj_9'}, $p, 8));
        return 1;
    }
    return 0;
} ## end sub check_deadlock_using_k_dist_cache

sub is_k_dist_deadlock ($brd) {
    return 0 if all_boxes_in_place($brd, 0);
    my $res = check_deadlock_using_k_dist_cache($brd);
    return $res;
}

sub can_put_all_on_targets ($brd, $max_size) {
    my $res = 0;
    my $son;
    my $h         = init_helper();
    my $positions = [map {{ 'board' => undef, 'moves_num' => 0 }} 1 .. $max_size];
    set_first_position($brd, 0, $positions, MINI_SEARCH, $h);
    my $pos_num = 1;
    while (1) {
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
        next unless ($pos_num == $max_size);
        $res = -1;
        last;
    } ## end while (1)
    release_positions($positions);
    return $res;
} ## end sub can_put_all_on_targets

sub rooms_deadlock_search_actual ($brd, $pull_mode, $tested_deadlock_room) {
    my $res = 0;
    my $son;
    my $h = init_helper();
    $h->{'tested_deadlock_room'} = $tested_deadlock_room;
    return NOT_DEADLOCK if all_boxes_in_place($brd, $pull_mode);
    my $positions = [map {{ 'board' => undef, 'moves_num' => 0 }} 1 .. (MAX_ROOMS_DEADLOCK_SEARCH)];
    set_first_position($brd, $pull_mode, $positions, ROOMS_DEADLOCK_SEARCH, $h);
    my $pos_num = 1;

    while (1) {
        my $total_leaves = estimate_uniqe_moves($positions, $pos_num);
        if ($total_leaves > MAX_ROOMS_DEADLOCK_SEARCH) {
            $res = SEARCH_EXCEEDED;
            last;
        }
        my $pos = get_best_rooms_deadlock_move($positions, $pos_num, \$son);
        if ($pos == -1) {
            $res = IS_DEADLOCK;
            last;
        }
        expand_position($positions->[$pos], $son, $pull_mode, $positions, $pos_num, $h);
        $pos_num++;
        my $c = $positions->[$pos_num - 1]{'board'};
        if (all_boxes_in_place($c, $pull_mode)) {
            $res = NOT_DEADLOCK;
            last;
        }
        next unless ($pos_num == MAX_ROOMS_DEADLOCK_SEARCH);
        $res = SEARCH_EXCEEDED;
        last;
    } ## end while (1)
    release_positions($positions);
    return $res;
} ## end sub rooms_deadlock_search_actual

sub rooms_deadlock_search ($brd, $pull_mode, $tested_deadlock_room) {
    my $hash = get_board_hash($brd);
    my $res  = (($Cache{ join '/', $hash, $pull_mode, ROOMS_DEADLOCK_SEARCH } // $CACHE_MISS)->[0]);
    return $res if $res >= 0 and $res <= 2;
    $res = rooms_deadlock_search_actual($brd, $pull_mode, $tested_deadlock_room);
    insert_to_deadlock_cache($hash, $res, $pull_mode, ROOMS_DEADLOCK_SEARCH);
    if ($res == IS_DEADLOCK) {
    }
    return $res;
}

sub is_rooms_deadlock ($b_in, $pull_mode, $last_move) {
    return 0 if $last_move->{'base'} or $last_move->{'kill'};
    return 0 if $Rooms_num == 1;
    my $p = $Index_to_p[$last_move->{'to'}];
    my $brd;
    $brd = $b_in;
    $brd&.=$NOT_BASE if $pull_mode;
    for my $t (0 .. $Rooms_num - 1) {
        next if vec($Room_with_corridors[$t], $p, 8) == 0;
        next if $Room_size[$t] >= 25;
        my $n = boxes_in_room($brd, $t);
        next if $n <= 1 or $n > 5;
        next if $n == 5 and $Room_size[$t] > 17;
        next if $n == 4 and $Room_size[$t] > 20;
        my $c;
        $c = $brd;
        $c = keep_boxes_in_room($c, $t);
        my $res = rooms_deadlock_search($c, $pull_mode, $t);
        return 1 if $res == 1;
    }
    return 0;
} ## end sub is_rooms_deadlock

sub fill_expansion_structures ($t, $e, $h) {
    my ($brd, $c);
    $brd = $e->{'b'};
    $e->{'has_corral'} = 0;
    my @moves     = find_possible_moves($brd, $t->{'pull_mode'}, \$e->{'has_corral'}, $t->{'search_mode'}, $h);
    my $moves_num = scalar @moves;
    $e->{'moves_num'} = $moves_num;
    my $mp      = $e->{'move_hash_place'} = $t->{'move_hashes_num'};
    my $mh_move = $t->{'mh_move'};
    my $mh_node = $t->{'mh_node'};
    my $mh_dead = $t->{'mh_deadlocked'};

    for my $i (0 .. $moves_num - 1) {
        $c = $e->{'b'};
        $c = apply_move($c, $moves[$i], $t->{'search_mode'});
        my $hash = get_board_hash($c);
        $mh_move->[$mp + $i] = move_pack($moves[$i]);
        $mh_dead->[$mp + $i] = 0;
        my $place = $t->{'node_of_hash'}{$hash};
        unless (defined $place) {
            my $s = {};
            score_board($c, $s, $t->{'pull_mode'}, $t->{'search_mode'}, $h);
            add_node_to_tree($t, $hash, $s);
            $place = $t->{'nodes_num'} - 1;
        }
        $mh_node->[$mp + $i] = $place;
    }
    $t->{'move_hashes_num'} += $moves_num;
    set_leaf_direction($t, $e);
    return;
} ## end sub fill_expansion_structures

sub add_board_to_tree ($t, $brd, $h) {
    my $hash = get_board_hash($brd);
    my $s    = {};
    score_board($brd, $s, $t->{'pull_mode'}, $t->{'search_mode'}, $h);
    add_node_to_tree($t, $hash, $s);
    return;
}

sub set_root ($t, $brd, $h) {
    Carp::confess('search mode not initialized')
        if $t->{'search_mode'} == -1;
    my $nodes_before_expansion = $t->{'nodes_num'};
    my $hash                   = get_board_hash($brd);
    my $s                      = {};
    score_board($brd, $s, $t->{'pull_mode'}, $t->{'search_mode'}, $h);
    my $node_place = ($t->{'node_of_hash'}{$hash} // -1);
    if ($node_place == -1) {
        add_node_to_tree($t, $hash, $s);
    }
    else {
        Carp::confess('root is already in tree')
            if $t->{'node_expansion'}[$node_place] != -1;
    }
    $node_place = ($t->{'node_of_hash'}{$hash} // -1);
    $t->{'node_expansion'}[$node_place] = $t->{'expansions_num'};
    my $e = $t->{'expansions'}[$t->{'expansions_num'}] = {};
    $e->{'index'} = $t->{'expansions_num'};
    $t->{'expansions_num'}++;
    $e->{'node'}        = $node_place;
    $e->{'b'}           = $brd;
    $e->{'best_past'}   = $node_place;
    $e->{'label'}       = -1;
    $e->{'weight'}      = 0;
    $e->{'depth'}       = 0;
    $e->{'father'}      = undef;
    $e->{'best_move'}   = -1;
    $e->{'best_weight'} = 1000000;
    fill_expansion_structures($t, $e, $h);
    set_deadlock_status($t, $e);
    $e->{'subtree_size'}      = 1;
    $e->{'next_son_to_check'} = 0;
    block_existing_sons_tree($t, $e, $nodes_before_expansion)
        if $t->{'search_mode'} == GIRL_SEARCH;
    return;
} ## end sub set_root

sub expand_node ($t, $e, $son, $h) {
    my $nodes_before_expansion = $t->{'nodes_num'};
    my $mh_move                = $t->{'mh_move'};
    my $mp                     = $e->{'move_hash_place'};
    my $node_place             = $t->{'mh_node'}[$mp + $son];
    my $hash                   = $t->{'node_hash'}[$node_place];
    my $n_score = score_hash($t, $node_place);
    Carp::confess('already expanded')
        if $t->{'node_expansion'}[$node_place] != -1;
    Carp::confess('expanding a leaf which is known to be deadlocked')
        if $t->{'node_deadlocked'}[$node_place];
    $t->{'node_expansion'}[$node_place] = $t->{'expansions_num'};
    my $next = $t->{'expansions'}[$t->{'expansions_num'}] = {};
    $next->{'index'} = $t->{'expansions_num'};
    $t->{'expansions_num'}++;
    my $brd          = $e->{'b'};
    my $move_to_play = move_unpack($mh_move->[$mp + $son]);
    $brd = apply_move($brd, $move_to_play, $t->{'search_mode'});
    Carp::confess('hash error') if get_board_hash($brd) != $hash;
    $next->{'node'}      = $node_place;
    $next->{'b'}         = $brd;
    $next->{'best_past'} = $e->{'best_past'};
    $next->{'best_past'} = $node_place
        if is_better_score($n_score, score_hash($t, $e->{'best_past'}), $t->{'pull_mode'}, $t->{'search_mode'});
    $next->{'label'}        = -1;
    $next->{'weight'}       = $e->{'weight'} + $move_to_play->{'attr'}{'weight'};
    $next->{'depth'}        = $e->{'depth'} + 1;
    $next->{'best_weight'}  = 1000000;
    $next->{'best_move'}    = -1;
    $next->{'father'}       = $e;
    $next->{'subtree_size'} = 0;
    fill_expansion_structures($t, $next, $h);
    set_deadlock_status($t, $next);
    update_subtree_size($t, $next);
    $next->{'next_son_to_check'} = 0;
    block_existing_sons_tree($t, $next, $nodes_before_expansion)
        if $t->{'search_mode'} == GIRL_SEARCH;
    return;
} ## end sub expand_node

sub wobblers_search_actual ($brd, $pull_mode, $max_positions) {
    my $res = 0;
    my $son;
    my $h = init_helper();
    return NOT_DEADLOCK if all_boxes_in_place($brd, $pull_mode);
    my $positions = [map {{ 'board' => undef, 'moves_num' => 0 }} 1 .. $max_positions];
    set_first_position($brd, $pull_mode, $positions, WOBBLERS_SEARCH, $h);
    my $pos_num = 1;
    while (1) {
        my $total_leaves = estimate_uniqe_moves($positions, $pos_num);
        if ($total_leaves > $max_positions) {
            $res = SEARCH_EXCEEDED;
            last;
        }
        my $pos = get_best_wobblers_move($positions, $pos_num, \$son);
        if ($pos == -1) {
            $res = IS_DEADLOCK;
            last;
        }
        expand_position($positions->[$pos], $son, $pull_mode, $positions, $pos_num, $h);
        $pos_num++;
        my $c = $positions->[$pos_num - 1]{'board'};
        if (all_boxes_in_place($c, $pull_mode)) {
            $res = NOT_DEADLOCK;
            last;
        }
        next unless ($pos_num == $max_positions);
        $res = SEARCH_EXCEEDED;
        last;
    } ## end while (1)
    release_positions($positions);
    return $res;
} ## end sub wobblers_search_actual

sub start_zone_is_deadlocked ($brd) {
    my $res = wobblers_search_actual($brd, 1, 1000);
    return 1 if $res == 1;
    return 0;
}

sub wobbler_deadlock_search ($brd, $pull_mode) {
    my $hash = get_board_hash($brd);
    my $res  = (($Cache{ join '/', $hash, $pull_mode, WOBBLERS_SEARCH } // $CACHE_MISS)->[0]);
    return $res if $res >= 0 and $res <= 2;
    $res = wobblers_search_actual($brd, $pull_mode, MAX_WOBBLERS_DEADLOCK_SEARCH);
    insert_to_deadlock_cache($hash, $res, $pull_mode, WOBBLERS_SEARCH);
    return $res;
}

sub is_wobblers_deadlock ($b_in, $pull_mode) {
    my $brd;
    return 0 if $pull_mode == 0;
    if ($pull_mode == 0) {
        $brd = turn_fixed_boxes_into_walls($b_in);
    }
    else {
        $brd = $b_in;
        $brd&.=$NOT_BASE;
    }
    $brd = remove_boxes_with_no_player_access($brd, $pull_mode, 0);
    $brd = remove_wobblers($brd, $pull_mode);
    my $n = (($brd&.$BOX_ONLY) =~ tr/\x00//c);
    return 0 if $n == 0;
    return 0 if $n == $Global_boxes_in_level;
    my $res = wobbler_deadlock_search($brd, $pull_mode);
    return 1 if $res == IS_DEADLOCK;
    return 0;
} ## end sub is_wobblers_deadlock

sub xy_search_actual ($brd, $pull_mode, $max_positions) {
    my $res = 0;
    my $son;
    my $h = init_helper();
    return NOT_DEADLOCK if all_boxes_in_place($brd, $pull_mode);
    my $positions = [map {{ 'board' => undef, 'moves_num' => 0 }} 1 .. $max_positions];
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
        expand_position($positions->[$pos], $son, $pull_mode, $positions, $pos_num, $h);
        $pos_num++;
        my $c = $positions->[$pos_num - 1]{'board'};
        if (all_boxes_in_place($c, $pull_mode)) {
            $res = NOT_DEADLOCK;
            last;
        }
        next unless ($pos_num == $max_positions);
        $res = SEARCH_EXCEEDED;
        last;
    } ## end while (1)
    release_positions($positions);
    return $res;
} ## end sub xy_search_actual

sub xy_deadlock_search ($brd, $pull_mode) {
    my $hash = get_board_hash($brd);
    my $res  = (($Cache{ join '/', $hash, $pull_mode, XY_SEARCH } // $CACHE_MISS)->[0]);
    return $res if $res >= 0 and $res <= 2;
    $res = xy_search_actual($brd, $pull_mode, MAX_XY_DEADLOCK_SEARCH);
    insert_to_deadlock_cache($hash, $res, $pull_mode, XY_SEARCH);
    if ($res == 2) {
    }
    return $res;
}

sub distill_pattern ($brd, $pull_mode, $distill_method) {
    my $i = 0;
    while ($i < $Height) {
        my $j = 0;
        while ($j < $Width) {
            if (vec($brd, $i * $Width + $j, 8) & BOX) {
                my $c = $brd;
                vec($c, $i * $Width + $j, 8) &= 0xFF ^ BOX;
                $c = expand_sokoban_cloud($c);
                my $deadlocked = 0;
                if (not all_boxes_in_place($c, $pull_mode)) {
                    if ($distill_method == DISTILL_ON_TARGETS) {
                        Carp::confess('bad distill') if $pull_mode;
                        $deadlocked = 1              if can_put_all_on_targets($c, 1000) == 0;
                    }
                    elsif ($distill_method == DISTILL_XY) {
                        $deadlocked = 1
                            if xy_deadlock_search($c, $pull_mode) == 1;
                    }
                    else {
                        Carp::confess('bad method');
                    }
                    if ($deadlocked) {
                        $brd = $c;
                        $i   = 0;
                        $j   = 0;
                    }
                } ## end if (not all_boxes_in_place...)
            } ## end if (vec($brd, $i * $Width...))
            $j++;
        } ## end while ($j < $Width)
        $i++;
    } ## end while ($i < $Height)
    return $brd;
} ## end sub distill_pattern

sub slow_xy_deadlock ($b_in, $pull_mode) {
    my $brd;
    $brd = $b_in;
    return if is_in_stuck_patterns($brd, $pull_mode);
    $brd = remove_wobblers($brd, $pull_mode)
        if $pull_mode == 0;
    $brd = clear_xy_boxes($brd, $pull_mode);
    my $n = (($brd&.$BOX_ONLY) =~ tr/\x00//c);
    return if $n == 0;
    return if $n > MAX_STUCK_PATTERN_SIZE;
    return if $n == $Global_boxes_in_level;
    my $res = xy_deadlock_search($brd, $pull_mode);

    if ($res == 1) {
        $brd = distill_pattern($brd, $pull_mode, DISTILL_XY);
        add_stuck_pattern($brd, $pull_mode);
    }
    return;
} ## end sub slow_xy_deadlock

sub learn_from_subtrees ($t, $e) {
    my $pull_mode = $t->{'pull_mode'};
    while (defined $e) {
        if ($e->{'subtree_size'} == 64 + 64 * $pull_mode) {
            my $brd = $e->{'b'};
            slow_xy_deadlock($brd, $pull_mode);
        }
        $e = $e->{'father'};
    }
    return;
}

sub corral_deadlock_search_actual ($brd, $pull_mode, $search_size) {
    my $result = -1;
    my $son;
    my $h = init_helper();
    if ($pull_mode == 0) {
        return NOT_DEADLOCK if work_left_in_deadlock_zone($brd) == 0;
    }
    my $deadlock_positions = [map {{ 'board' => undef, 'moves_num' => 0 }} 1 .. $search_size];
    set_first_position($brd, $pull_mode, $deadlock_positions, DEADLOCK_SEARCH, $h);
    my $deadlock_pos_num = 1;
    while (1) {
        my $total_leaves = estimate_uniqe_moves($deadlock_positions, $deadlock_pos_num);
        if ($total_leaves > $search_size) {
            $result = SEARCH_EXCEEDED;
            last;
        }
        if (son_can_break_free($deadlock_positions->[$deadlock_pos_num - 1], $pull_mode)) {
            $result = NOT_DEADLOCK;
            last;
        }
        mark_deadlocked_sons_using_cache($deadlock_positions, $deadlock_pos_num);
        my $node = choose_deadlock_son($deadlock_positions, $deadlock_pos_num, \$son);
        if ($node == -1) {
            $result = IS_DEADLOCK;
            last;
        }
        expand_position($deadlock_positions->[$node], $son, $pull_mode, $deadlock_positions, $deadlock_pos_num, $h);
        $deadlock_pos_num++;
        next unless ($deadlock_pos_num >= $search_size);
        $result = SEARCH_EXCEEDED;
        last;
    } ## end while (1)
    insert_positions_to_deadlock_cache($deadlock_positions, $deadlock_pos_num, $result);
    release_positions($deadlock_positions);
    return $result;
} ## end sub corral_deadlock_search_actual

sub mini_corral ($brd) {
    my $c;
    return NOT_DEADLOCK if (($brd&.$BOX_ONLY) =~ tr/\x00//c) > 5;
    my $hash = get_board_hash($brd);
    my $res  = (($Cache{ join '/', $hash, 0, MINI_CORRAL } // $CACHE_MISS)->[0]);
    return $res if $res == IS_DEADLOCK or $res == NOT_DEADLOCK;
    if ($res == -1) {
        insert_to_deadlock_cache($hash, SEARCH_EXCEEDED, 0, MINI_CORRAL);
        return SEARCH_EXCEEDED;
    }
    do {my $e = $Cache{ join '/', $hash, 0, MINI_CORRAL }; $e->[1]++ if defined $e};
    return SEARCH_EXCEEDED if (($Cache{ join '/', $hash, 0, MINI_CORRAL } // $CACHE_MISS)->[1]) != 100;
    if (all_boxes_in_place($brd, 0)) {
        insert_to_deadlock_cache($hash, NOT_DEADLOCK, 0, MINI_CORRAL);
        return NOT_DEADLOCK;
    }
    $res = can_put_all_on_targets($brd, 1000);
    if ($res == 0) {
        insert_to_deadlock_cache($hash, IS_DEADLOCK, 0, MINI_CORRAL);
        return IS_DEADLOCK;
    }
    else {
        insert_to_deadlock_cache($hash, NOT_DEADLOCK, 0, MINI_CORRAL);
    }
    return NOT_DEADLOCK;
} ## end sub mini_corral

sub advanced_deadlock_search ($brd, $pull_mode) {
    my $hash = get_board_hash($brd);
    my $res  = (($Cache{ join '/', $hash, $pull_mode, DEADLOCK_SEARCH } // $CACHE_MISS)->[0]);
    do {my $e = $Cache{ join '/', $hash, $pull_mode, DEADLOCK_SEARCH }; $e->[1]++ if defined $e};
    if ($res == SEARCH_EXCEEDED) {
        my $queries = (($Cache{ join '/', $hash, $pull_mode, DEADLOCK_SEARCH } // $CACHE_MISS)->[1]);
        if (should_reevaluate($queries)) {
            $res = corral_deadlock_search_actual($brd, $pull_mode, $queries);
            insert_to_deadlock_cache($hash, $res, $pull_mode, DEADLOCK_SEARCH)
                if $res != SEARCH_EXCEEDED;
        }
    }
    return $res if $res >= 0 and $res <= 2;
    $res = corral_deadlock_search_actual($brd, $pull_mode, MAX_DEADLOCK_SEARCH);
    insert_to_deadlock_cache($hash, $res, $pull_mode, DEADLOCK_SEARCH);
    return $res;
} ## end sub advanced_deadlock_search

sub advanced_deadlock_pull_mode ($b_in, $without_wobblers) {
    my ($brd, $c);
    $brd = $b_in;
    $brd&.=$NOT_BASE;
    return 0 if get_connectivity($brd) == 1;
    $brd = remove_wobblers($brd, 1) if $without_wobblers;
    $brd = set_deadlock_zone_in_pull_mode($brd);
    $c   = $brd;
    $c   = clear_boxes_out_of_deadlock_zone($c);
    return NOT_DEADLOCK
        if (($c&.$BOX_ONLY) =~ tr/\x00//c) == $Global_boxes_in_level;
    my $res = advanced_deadlock_search($c, 1);
    return 0 if $res == NOT_DEADLOCK or $res == SEARCH_EXCEEDED;

    if (work_left_outside_deadlock_zone($brd) == 0) {
        return NOT_DEADLOCK;
    }
    return 1;
} ## end sub advanced_deadlock_pull_mode

sub corral_deadlock ($b_in, $pull_mode) {
    my @dist;
    my ($brd, $c);
    my @checked;
    my $res;
    return 0 if board_is_solved($b_in, $pull_mode);
    if ($pull_mode) {
        $res = advanced_deadlock_pull_mode($b_in, 0);
        return $res;
    }
    $brd = turn_fixed_boxes_into_walls($b_in);
    my $connect_num = mark_connectivities($brd, \@dist);
    return 0 if $connect_num >= 51;
    for my $i (0 .. $connect_num - 1) {
        for my $j (0 .. $connect_num - 1) {
            $checked[$i][$j] = 0;
        }
    }
    my @search_exceeded = (0) x $connect_num;
    my $sokoban_comp    = $dist[get_sokoban_position($brd)];
    for my $c1 (0 .. $connect_num - 1) {
        next if $c1 == $sokoban_comp;
        $checked[$c1][$c1] = 1;
        $c                 = $brd;
        $c                 = keep_two_components($c, \@dist, $c1, $c1, $pull_mode);
        $c                 = clear_boxes_out_of_deadlock_zone($c);
        $c                 = clear_frozen_boxes_away_from_deadlock_zone($c);
        $res               = advanced_deadlock_search($c, $pull_mode);
        return 1 if $res == IS_DEADLOCK;
        $search_exceeded[$c1] = 1 if $res == SEARCH_EXCEEDED;
        $res = mini_corral($c);
        return $res if $res == IS_DEADLOCK;
    }
    for my $p (0 .. $Ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;
        my @list = get_components_around_place($p, \@dist);
        for my $k1 (0 .. $#list) {
            for my $k2 ($k1 .. $#list) {
                my $c1 = $list[$k1];
                my $c2 = $list[$k2];
                next if $c1 == $sokoban_comp;
                next if $c2 == $sokoban_comp;
                next if $checked[$c1][$c2];
                next if $search_exceeded[$c1];
                next if $search_exceeded[$c2];
                $checked[$c1][$c2] = 1;
                $checked[$c2][$c1] = 1;
                $c                 = $brd;
                $c                 = keep_two_components($c, \@dist, $c1, $c2, $pull_mode);
                $c                 = clear_boxes_out_of_deadlock_zone($c);
                $c                 = clear_frozen_boxes_away_from_deadlock_zone($c);
                $res               = advanced_deadlock_search($c, $pull_mode);
                return 1 if $res == IS_DEADLOCK;
                $res = mini_corral($c);
                return $res if $res == IS_DEADLOCK;
            } ## end for my $k2 ($k1 .. $#list)
        } ## end for my $k1 (0 .. $#list)
    } ## end for my $p (0 .. $Ncells...)
    return 0;
} ## end sub corral_deadlock

sub board_is_deadlocked ($brd, $pull_mode, $search_mode) {
    return 1 if check_matching_deadlock($brd, $pull_mode, $search_mode);
    if ($pull_mode) {
        return 1 if free_pull_deadlock($brd);
    }
    if ($pull_mode == 0) {
        return 1 if try_pulling_all_zones($brd) == 0;
    }
    return 1 if is_in_stuck_patterns($brd, $pull_mode);
    if (get_connectivity($brd) != 1) {
        return 1
            if corral_deadlock($brd, $pull_mode);
    }
    if ($pull_mode == 0) {
        return 1 if is_diag_deadlock($brd);
        return 1 if is_k_dist_deadlock($brd);
    }
    return 1
        if is_wobblers_deadlock($brd, $pull_mode);
    return 0;
} ## end sub board_is_deadlocked

sub move_is_deadlocked ($b_in, $m, $pull_mode, $search_mode) {
    return 0 if $m->{'kill'} or $m->{'base'};
    my $brd = $b_in;
    $brd = apply_move($brd, $m, NORMAL);
    my $res = board_is_deadlocked($brd, $pull_mode, $search_mode);
    return 1 if $res;
    return 1
        if is_rooms_deadlock($brd, $pull_mode, $m);
    return 0;
}

sub choose_imagine_advisor ($base_score, $moves_num, $scores, $search_mode) {
    my $best_son = -1;
    my $min_dist = 0;
    return -1
        if $search_mode == FORWARD_WITH_BASES or $search_mode == GIRL_SEARCH;
    for my $i (0 .. $moves_num - 1) {
        next if $scores->[$i]{'packed_boxes'} < $base_score->{'packed_boxes'};
        next if $scores->[$i]{'imagine'} <= $base_score->{'imagine'};
        next unless ($best_son == -1 or $scores->[$i]{'dist_to_imagined'} < $min_dist);
        $min_dist = $scores->[$i]{'dist_to_imagined'};
        $best_son = $i;
    }
    return $best_son;
}

sub set_imagined_hf_board ($brd, $h) {
    my $c;
    $c = $brd;
    for my $p (0 .. $Ncells - 1) {
        vec($c, $p, 8) &= 0xFF ^ TARGET;
        vec($c, $p, 8) |= BASE if vec($c, $p, 8) & BOX;
    }
    $h->{'imagined_hf_board'} = $c;
    return;
}

sub are_new_moves ($brd, $c, $pull_mode) {
    for my $p (0 .. $Ncells - 1) {
        next if (vec($brd, $p, 8) & BOX) == 0;
        next if (vec($c,   $p, 8) & BOX) == 0;
        for my $k (0 .. 3) {
            my $sp  = $p + $Delta_p[$k];
            my $val = vec($brd, $sp, 8);
            next if $val & SOKOBAN;
            next if $val & BOX;
            next if (vec($c, $sp, 8) & SOKOBAN) == 0;
            if ($pull_mode == 0) {
                my $pp = $p - $Delta_p[$k];
                return 1 if (vec($c, $pp, 8) & OCCUPIED) == 0;
            }
            else {
                my $pp = $p + 2 * $Delta_p[$k];
                return 1 if (vec($c, $pp, 8) & OCCUPIED) == 0;
            }
        } ## end for my $k (0 .. 3)
    } ## end for my $p (0 .. $Ncells...)
    return 0;
} ## end sub are_new_moves

sub explorer ($brd, $base_score, $moves_num, $moves, $scores, $pull_mode) {
    my ($c, $blocked_area);
    my $best_score;
    my $best_move = -1;
    $blocked_area = $ZERO_BOARD;
    for my $i (0 .. $Index_num - 1) {
        my $p   = $Index_to_p[$i];
        my $val = vec($brd, $p, 8);
        next unless ($val == 0 or $val == TARGET);
        vec($blocked_area, $p, 8) = 1;
    }
    for my $i (0 .. $moves_num - 1) {
        next if $scores->[$i]{'packed_boxes'} < $base_score->{'packed_boxes'};
        if ($pull_mode == 0) {
            next
                if vec($Distance_from_to, $moves->[$i]{'to'} * $Index_num + $moves->[$i]{'from'}, 32) == 1000000;
        }
        $c = $brd;
        $c = apply_move($c, $moves->[$i], NORMAL);
        my $res = are_new_moves($brd, $c, $pull_mode);
        next if $res == 0;
        if ($best_move == -1) {
            $best_score = { %{ $scores->[$i] } };
            $best_move  = $i;
            next;
        }
        next unless (is_better_score($scores->[$i], $best_score, $pull_mode, NORMAL));
        $best_score = { %{ $scores->[$i] } };
        $best_move  = $i;
    } ## end for my $i (0 .. $moves_num...)
    return $best_move;
} ## end sub explorer

sub pick_opener ($brd, $base_score, $moves_num, $moves, $scores, $pull_mode, $h) {
    my $min_dist_from = 1000000;
    my $max_dist_to   = 0;
    my $best_move     = -1;
    for my $i (0 .. $moves_num - 1) {
        return -1
            if $scores->[$i]{'packed_boxes'} > $base_score->{'packed_boxes'};
    }
    my $blocker_index = next_parking_place($brd, $h);
    return -1 if $blocker_index == -1;
    if (vec($brd, $Index_to_p[$blocker_index], 8) & BOX) {
        Carp::confess('box in place?');
    }
    my $connectivity = $base_score->{'connectivity'};
    my $rooms_score  = $base_score->{'rooms_score'};
    my $packed_boxes = $base_score->{'packed_boxes'};
    for my $i (0 .. $moves_num - 1) {
        next if $scores->[$i]{'packed_boxes'} < $packed_boxes;
        next if $scores->[$i]{'connectivity'} > $connectivity;
        next if $scores->[$i]{'rooms_score'} > $rooms_score;
        my $dist1 = vec($Bfs_distance_from_to, $blocker_index * $Index_num + $moves->[$i]{'from'}, 32);
        my $dist2 = vec($Bfs_distance_from_to, $blocker_index * $Index_num + $moves->[$i]{'to'},   32);
        next if $dist2 < $dist1;
        next if $dist1 > $min_dist_from;
        if ($dist1 < $min_dist_from) {
            $min_dist_from = $dist1;
            $best_move     = $i;
            $max_dist_to   = $dist2;
            next;
        }
        next unless ($dist1 == $min_dist_from);
        if ($dist2 > $max_dist_to) {
            $max_dist_to = $dist2;
            $best_move   = $i;
        }
    } ## end for my $i (0 .. $moves_num...)
    return $best_move;
} ## end sub pick_opener

sub set_advisors_inner ($brd, $base_score, $moves_num, $moves, $scores, $pull_mode, $search_mode, $l, $already_expanded, $h) {
    $l->{'pack'}         = -1;
    $l->{'connectivity'} = -1;
    $l->{'rooms'}        = -1;
    $l->{'hotspots'}     = -1;
    $l->{'opener'}       = -1;
    $l->{'out_of_plan'}  = -1;
    $l->{'explorer'}     = -1;
    $l->{'imagine'}      = -1;
    return if $search_mode == GIRL_SEARCH;
    return if $search_mode == NAIVE_SEARCH;
    return if $search_mode == SNAIL_SEARCH;

    if (   $search_mode == HF_SEARCH
        or $search_mode == BICON_SEARCH
        or $search_mode == MAX_DIST_SEARCH
        or $search_mode == MAX_DIST_SEARCH2
        or $search_mode == NETLOCK_SEARCH)
    {
        set_default_advisor($base_score, $moves_num, $moves, $scores, $pull_mode, $search_mode, $already_expanded, $l);
        return;
    }
    if ($search_mode == REV_SEARCH) {
        set_rev_advisor($brd, $base_score, $moves_num, $moves, $scores, $pull_mode, $search_mode, $already_expanded, $l);
        return;
    }
    if ($pull_mode) {
        $l->{'pack'}         = packing_search_advisor($brd, $base_score, $moves_num, $moves, $scores, $search_mode);
        $l->{'connectivity'} = choose_advisor($base_score, $moves_num, $scores, OPTIMIZE_CONNECTIVITY, 1);
        $l->{'rooms'}        = choose_advisor($base_score, $moves_num, $scores, OPTIMIZE_ROOMS,        1);
        $l->{'explorer'}     = explorer($brd, $base_score, $moves_num, $moves, $scores, $pull_mode);
        discard_advisors_in_base_search($moves, $l)
            if $search_mode == BASE_SEARCH;
        return;
    }
    $l->{'pack'}         = choose_advisor($base_score, $moves_num, $scores, OPTIMIZE_PACKED,       0);
    $l->{'connectivity'} = choose_advisor($base_score, $moves_num, $scores, OPTIMIZE_CONNECTIVITY, 0);
    $l->{'rooms'}        = choose_advisor($base_score, $moves_num, $scores, OPTIMIZE_ROOMS,        0);
    $l->{'hotspots'}     = choose_advisor($base_score, $moves_num, $scores, OPTIMIZE_HOTSPOTS,     0);
    $l->{'imagine'}      = choose_imagine_advisor($base_score, $moves_num, $scores, $search_mode);
    $l->{'out_of_plan'}  = new_oop_advisor($brd, $base_score, $moves_num, $moves, $scores, $pull_mode, $h);
    $l->{'opener'}       = pick_opener($brd, $base_score, $moves_num, $moves, $scores, $pull_mode, $h);
    $l->{'explorer'}     = explorer($brd, $base_score, $moves_num, $moves, $scores, $pull_mode);
    return;
} ## end sub set_advisors_inner

sub set_advisors_in_node ($t, $e, $h) {
    my (@moves, @scores, @already_expanded);
    my $mh_move = $t->{'mh_move'};
    my $mh_node = $t->{'mh_node'};
    my $mp      = $e->{'move_hash_place'};
    for my $i (0 .. $e->{'moves_num'} - 1) {
        $moves[$i]  = move_unpack($mh_move->[$mp + $i]);
        $scores[$i] = {};
        get_score_of_node($t, $mh_node->[$mp + $i], $scores[$i]);
    }
    for my $i (0 .. $e->{'moves_num'} - 1) {
        my $place = $mh_node->[$mp + $i];
        $already_expanded[$i] =
            ($t->{'node_expansion'}[$place] == -1 ? 0 : 1);
    }
    my $brd = $e->{'b'};
    my %adv;
    set_advisors_inner($brd, score_hash($t, $e->{'node'}),
        $e->{'moves_num'}, \@moves, \@scores, $t->{'pull_mode'}, $t->{'search_mode'}, \%adv, \@already_expanded,
        $h);
    $e->{'advisors'} = pack 'l8', @adv{ @{ +ADVISOR_KEYS } };
    return;
} ## end sub set_advisors_in_node

sub set_advisors_and_weights_to_last_node ($t, $h) {
    Carp::confess('internal error') if $t->{'expansions_num'} <= 0;
    my $e = $t->{'expansions'}[$t->{'expansions_num'} - 1];
    set_naive_data_in_node($t, $e, $h)
        if $t->{'search_mode'} == NAIVE_SEARCH;
    if (   $t->{'search_mode'} == MAX_DIST_SEARCH
        or $t->{'search_mode'} == MAX_DIST_SEARCH2
        or $t->{'search_mode'} == SNAIL_SEARCH)
    {
        set_max_dist_data_in_node($t, $e, $h);
    }
    set_imagine_data_in_node($t, $e, $h);
    set_advisors_in_node($t, $e, $h);
    set_weight_to_node_moves($t, $e, $h);
    set_best_move($t, $e);
    return;
} ## end sub set_advisors_and_weights_to_last_node

sub FESS ($brd, $time_allocation, $search_mode, $t, $h) {
    my $solved = 0;
    my $c;
    my $iter_num = 0;
    my $last_best;
    my $perimeter_entries = 0;
    my ($tree_pos, $tree_son);
    my $depth;
    return if $time_allocation <= 0;
    init_scored_distance($brd, 0, $h);
    my $local_start_time = time();
    reset_tree($t);
    $t->{'pull_mode'}                = 0;
    $t->{'search_mode'}              = $search_mode;
    $h->{'perimeter_found'}          = 0;
    $h->{'enable_inefficient_moves'} = 0;
    $h->{'enable_inefficient_moves'} = 1
        if is_in_perimeter(get_board_hash($brd), \$depth, 1);
    set_root($t, $brd, $h);
    my $new_node = $t->{'expansions'}[$t->{'expansions_num'} - 1];
    set_advisors_and_weights_to_last_node($t, $h);
    $new_node->{'best_past'} = $new_node->{'node'};
    if ($search_mode == GIRL_SEARCH) {
        set_values_to_moves_tree($t, $new_node);
        back_propagate_values_tree($t, $new_node);
    }
    init_requests($h);
    my $s = score_hash($t, $new_node->{'best_past'});
    add_request($s, $h);
    my $label = get_label_of_score($s, 0, $h);
    add_label_to_last_node($t, $label, $h);
    my $best_so_far = $new_node;
    $perimeter_entries += insert_node_into_perimeter($t, $new_node, 1);

    while (1) {
        $iter_num++;
        last if time_limit_exceeded($time_allocation, $local_start_time);
        last if run_aborted();
        last if $Any_core_solved;
        my $req = {};
        if (($iter_num & 1) or $h->{'perimeter_found'}) {
            get_next_request($req, $h);
        }
        else {
            get_request_of_score($req, score_hash($t, $best_so_far->{'best_past'}), $h);
        }
        my $tree_weight;
        if ($search_mode != GIRL_SEARCH or $h->{'perimeter_found'}) {
            $label       = get_label_of_request($req, $h);
            $tree_weight = best_move_in_tree($t, $label, \$tree_pos, \$tree_son);
        }
        else {
            $tree_weight = 0;
            choose_pos_son_to_expand_Epsilon_greedy_tree($t, \$tree_pos, \$tree_son, $h);
            Carp::confess('bad tree') if $tree_pos == -1;
        }
        next if $h->{'perimeter_found'} and $tree_weight >= 0;
        if ($tree_weight == 1000000) {
            next;
        }
        my $expanded_node = $t->{'expansions'}[$tree_pos];
        my $played_move   = move_unpack($t->{'mh_move'}[$expanded_node->{'move_hash_place'} + $tree_son]);
        $c = $expanded_node->{'b'};
        if (move_is_deadlocked($c, $played_move, 0, $search_mode)) {
            set_node_as_deadlocked($t, $tree_pos, $tree_son);
            if ($h->{'perimeter_found'}) {
                my $son_depth;
                my $hash = $t->{'node_hash'}[ $t->{'mh_node'}[$expanded_node->{'move_hash_place'} + $tree_son] ];
                if (is_in_perimeter($hash, \$son_depth, 1)) {
                }
            }
            next;
        }
        ++$Solve_nseen;
        expand_node($t, $t->{'expansions'}[$tree_pos], $tree_son, $h);
        set_advisors_and_weights_to_last_node($t, $h);
        $new_node = $t->{'expansions'}[$t->{'expansions_num'} - 1];
        if ($search_mode == GIRL_SEARCH) {
            set_values_to_moves_tree($t, $new_node);
            back_propagate_values_tree($t, $new_node);
        }
        add_request(score_hash($t, $new_node->{'best_past'}), $h);
        $label = get_label_of_score(score_hash($t, $new_node->{'best_past'}), 0, $h);
        add_label_to_last_node($t, $label, $h);
        update_best_so_far($t, \$best_so_far, $new_node, 0, $search_mode);

        if (node_is_solved($t, $new_node)) {
            $solved = 1;
            last;
        }
        check_cycle_deadlock($t, $best_so_far, $h);
        if ($t->{'node_deadlocked'}[$best_so_far->{'node'}]) {
            $best_so_far = best_node_in_tree($t);
        }
        if (not defined $best_so_far) {
            last;
        }
        learn_from_subtrees($t, $new_node);
        my $prev_perimeter = $h->{'perimeter_found'};
        if (check_if_perimeter_reached($t, $h)) {
            set_next_request_to_score(score_hash($t, $new_node->{'best_past'}), $h);
        }
        next unless ($h->{'perimeter_found'} == 0);
        $perimeter_entries += insert_node_into_perimeter($t, $new_node, 1);
    } ## end while (1)
    if ($solved) {
        store_solution_in_helper($t, $new_node, $h);
        $Any_core_solved = 1;
    }
    $h->{'level_solved'} = $solved;
    setup_rev_board($best_so_far, $h)
        if $t->{'search_mode'} == REV_SEARCH;
    return;
} ## end sub FESS

sub compute_start_zones ($start_zones) {
    my $brd;
    $brd = $Initial_board&.$NOT_BOX;
    $brd = turn_targets_into_walls($brd);
    my $zones_num = mark_connectivities($brd, $start_zones);
    return $zones_num;
}

sub declare_roots ($t, $brd, $start_zones, $start_zones_num, $h) {
    my $c;
    for my $i (0 .. $start_zones_num - 1) {
        $c = $brd;
        $c = put_sokoban_in_zone($c, $start_zones, $i);
        next if has_pull_moves($c) == 0;
        add_board_to_tree($t, $c, $h);
    }
    return;
}

sub packing_search ($b_in, $time_allocation, $search_mode, $t, $h) {
    my ($brd, $c);
    my $iter_num            = 0;
    my $cleared_all_targets = -1;
    my $failed_cell         = 0;
    my $best_so_far;
    my ($tree_pos, $tree_son, $tree_weight);
    my $new_node;
    my $last_best;
    my @start_zones;
    my $perimeter_entries = 0;
    my $testing_best;
    my $trim = 0;
    return if $time_allocation <= 0;
    init_scored_distance($b_in, 1, $h);
    reset_tree($t);
    $t->{'pull_mode'}   = 1;
    $t->{'search_mode'} = $search_mode;
    my $local_start_time = time();
    $h->{'perimeter_found'}          = 0;
    $h->{'enable_inefficient_moves'} = 0;
    $brd                             = $b_in;

    if ($search_mode == BASE_SEARCH) {
        $brd = enter_reverse_mode($brd, 1);
    }
    else {
        $brd = enter_reverse_mode($brd, 0);
    }
    my $start_zones_num = compute_start_zones(\@start_zones);
    init_pack_requets($h);
    declare_roots($t, $brd, \@start_zones, $start_zones_num, $h);
    for my $i (0 .. $start_zones_num - 1) {
        $c = $brd;
        $c = put_sokoban_in_zone($c, \@start_zones, $i);
        next if has_pull_moves($c) == 0;
        if (start_zone_is_deadlocked($c)) {
            next;
        }
        set_root($t, $c, $h);
        $new_node = $t->{'expansions'}[$t->{'expansions_num'} - 1];
        set_advisors_and_weights_to_last_node($t, $h);
        $new_node->{'best_past'} = $new_node->{'node'};
        my $s = score_hash($t, $new_node->{'best_past'});
        add_pack_request($s, $h);
        my $label = get_label_of_score($s, 1, $h);
        add_label_to_last_node($t, $label, $h);
        if ($search_mode == GIRL_SEARCH) {
            set_values_to_moves_tree($t, $t->{'expansions'}[$t->{'expansions_num'} - 1]);
            back_propagate_values_tree($t, $t->{'expansions'}[$t->{'expansions_num'} - 1]);
        }
        update_best_so_far($t, \$best_so_far, $new_node, 1, $search_mode);
        $perimeter_entries += insert_node_into_perimeter($t, $new_node, 1);
    } ## end for my $i (0 .. $start_zones_num...)
    while (1) {
        $iter_num++;
        last if time_limit_exceeded($time_allocation, $local_start_time);
        last if run_aborted();
        last if $Any_core_solved;
        $testing_best = 0;
        my $req = {};
        if (($iter_num & 1) or $h->{'perimeter_found'}) {
            get_next_pack_request($req, $h);
        }
        else {
            get_pack_request_of_score($req, score_hash($t, $best_so_far->{'best_past'}), $h);
            $testing_best = 1;
        }
        if ($search_mode != GIRL_SEARCH or $h->{'perimeter_found'}) {
            my $label = get_label_of_pack_request($req, $h);
            $tree_weight = best_move_in_tree($t, $label, \$tree_pos, \$tree_son);
        }
        else {
            choose_pos_son_to_expand_Epsilon_greedy_tree($t, \$tree_pos, \$tree_son, $h);
            if ($tree_pos == -1) {
                last;
            }
        }
        next if $h->{'perimeter_found'} and $tree_weight >= 0;
        last if $failed_cell >= 10000;
        if ($tree_pos == -1) {
            $failed_cell++;
            next;
        }
        $failed_cell = 0;
        my $expanded_node = $t->{'expansions'}[$tree_pos];
        my $move_to_play  = move_unpack($t->{'mh_move'}[$expanded_node->{'move_hash_place'} + $tree_son]);
        $brd = $expanded_node->{'b'};
        if (move_is_deadlocked($brd, $move_to_play, 1, $search_mode)) {
            $trim++;
            set_node_as_deadlocked($t, $tree_pos, $tree_son);
            if ($h->{'perimeter_found'}) {
                my $son_depth;
                my $hash = $t->{'node_hash'}[ $t->{'mh_node'}[$expanded_node->{'move_hash_place'} + $tree_son] ];
                if (is_in_perimeter($hash, \$son_depth, 0)) {
                }
            }
            next;
        }
        if (can_played_reversed($brd, $move_to_play, 1, $search_mode) == 0) {
            $t->{'mh_deadlocked'}[$t->{'expansions'}[$tree_pos]->{'move_hash_place'} + $tree_son] = 1;
            set_deadlock_status($t, $t->{'expansions'}[$tree_pos]);
            next;
        }
        expand_node($t, $t->{'expansions'}[$tree_pos], $tree_son, $h);
        set_advisors_and_weights_to_last_node($t, $h);
        $new_node = $t->{'expansions'}[$t->{'expansions_num'} - 1];
        ++$Solve_nseen;
        if ($search_mode == GIRL_SEARCH) {
            set_values_to_moves_tree($t, $new_node);
            back_propagate_values_tree($t, $new_node);
        }
        add_pack_request(score_hash($t, $new_node->{'best_past'}), $h);
        my $label = get_label_of_score(score_hash($t, $new_node->{'best_past'}), 1, $h);
        add_label_to_last_node($t, $label, $h);
        my $res = update_best_so_far($t, \$best_so_far, $new_node, 1, $search_mode);

        if ($res) {
            $cleared_all_targets = $iter_num if $cleared_all_targets != -1;
        }
        last if node_is_solved($t, $new_node);
        check_cycle_deadlock($t, $best_so_far, $h);
        $best_so_far = best_node_in_tree($t)
            if $t->{'node_deadlocked'}[$best_so_far->{'node'}];
        if (not defined $best_so_far) {
            last;
        }
        learn_from_subtrees($t, $new_node);
        if (is_in_stuck_patterns($best_so_far->{'b'}, $t->{'pull_mode'})) {
            recheck_tree_with_patterns($t);
            $best_so_far = best_node_in_tree($t);
        }
        if (score_field($t, $new_node->{'node'}, SC_BOXES_IN_LEVEL) == 0) {
            last;
        }
        my $prev_perimeter = $h->{'perimeter_found'};
        if (check_if_perimeter_reached($t, $h)) {
            set_next_pack_request_to_score(score_hash($t, $new_node->{'best_past'}), $h);
        }
        if ($h->{'perimeter_found'} == 0) {
            $perimeter_entries += insert_node_into_perimeter($t, $new_node, 1);
        }
        else {
            $perimeter_entries += insert_node_into_perimeter($t, $new_node, 0);
        }
    } ## end while (1)
    if (not defined $best_so_far) {
        $best_so_far = $t->{'expansions'}[0];
    }
    $c = $best_so_far->{'b'};
    set_imagined_hf_board($c, $h);
    conclude_parking($t, $best_so_far, $h);
    return;
} ## end sub packing_search

sub init_dragonfly () {
    $Dragonfly_nodes     = [];
    dragonfly_init_queue(\%Dragonfly_q, $Dragonfly_nodes);
    return;
}

sub dist_from_bases ($brd) {
    my $base_score = {};
    compute_base_distance($brd, $base_score, [], []);
    return $base_score->{'dist_to_targets'};
}

sub add_dragonfly_root ($brd) {
    my $e = $Dragonfly_nodes->[$Dragonfly_nodes_num] = {};
    $Dragonfly_roots[$Dragonfly_roots_num] = $brd;
    $Dragonfly_roots_num++;
    Carp::confess('too many roots')
        if $Dragonfly_roots_num >= MAX_DRAGONFLY_ROOTS;
    $e->{'board'}            = $Dragonfly_roots_num - 1;
    $e->{'depth'}            = 0;
    $e->{'father'}           = -1;
    $e->{'move_from'}        = 65535;
    $e->{'move_to'}          = 65535;
    $e->{'sokoban_position'} = 4;
    $e->{'dist'}             = dist_from_bases($brd);
    $e->{'packed'}           = boxes_on_bases($brd);
    $Dragonfly_nodes_num++;
    dragonfly_heap_insert(\%Dragonfly_q, $Dragonfly_nodes_num - 1);
    my $hash = get_board_hash($brd);
    dragonfly_update_perimeter([$hash], [0], 1, 0);
    return;
} ## end sub add_dragonfly_root

sub dragonfly_get_board ($e) {
    my @moves;
    my $p;
    my $player = $e->{'sokoban_position'};
    if ($e->{'board'} != 0xff) {
        return $Dragonfly_roots[$e->{'board'}];
    }
    while ($e->{'board'} == 0xff) {
        push @moves, { 'from' => $e->{'move_from'}, 'to' => $e->{'move_to'} };
        $e = $Dragonfly_nodes->[$e->{'father'}];
    }
    my $b = $Dragonfly_roots[$e->{'board'}];
    for my $i (reverse 0 .. $#moves) {
        $p = $Index_to_p[$moves[$i]{'from'}];
        Carp::confess('bad1') if (vec($b, $p, 8) & BOX) == 0;
        vec($b, $p, 8) &= 0xFF ^ BOX;
        $p = $Index_to_p[$moves[$i]{'to'}];
        Carp::confess('bad2') if vec($b, $p, 8) & OCCUPIED;
        vec($b, $p, 8) |= BOX;
    }
    $b&.=$NOT_SOKOBAN;
    my $sok_p = $p + $Delta_p[$player];
    vec($b, $sok_p, 8) |= SOKOBAN;
    $b = expand_sokoban_cloud($b, $sok_p);
    return $b;
} ## end sub dragonfly_get_board

sub mark_moves_when_corral ($brd, $moves, $n, $last_move, $possible) {
    for my $i (0 .. $n - 1) {
        $possible->[$i] = 1;
    }
    return if get_connectivity($brd) == 1;
    my ($w, $corral_options);
    $w = turn_fixed_boxes_into_walls($brd);
    (my $has_corral, $corral_options) = detect_corral($w);
    return if $has_corral == 0;
    my $p2 = $Index_to_p[$last_move];
    for my $i (0 .. $n - 1) {
        if ($moves->[$i]{'from'} == $last_move) {
            $possible->[$i] = 0;
            next;
        }
        my $c;
        $c = $brd;
        $c = apply_move($c, $moves->[$i], NORMAL);
        next if board_is_solved($c, 1);
        my $j;
        for ($j = 0; $j < 4; $j++) {
            my $p     = $p2 + $Delta_p[$j];
            my $delta = vec($c, $p, 8) ^ vec($brd, $p, 8);
            last if $delta & SOKOBAN;
        }
        $possible->[$i] = 0 if $j == 4;
    } ## end for my $i (0 .. $n - 1)
    return;
} ## end sub mark_moves_when_corral

sub dragonfly_expand_node ($node_index, $h) {
    my $e = $Dragonfly_nodes->[$node_index];
    my ($brd, $c);
    my (@moves, @hashes, @visited, @scores, @packed, @possible);
    return 0 if $e->{'depth'} >= MAX_SOL_LEN;
    if ($e->{'board'} == 0xff) {
        my $father = $Dragonfly_nodes->[$e->{'father'}];
        $brd = dragonfly_get_board($father);
        my $m = {
            'from'             => $e->{'move_from'},
            'to'               => $e->{'move_to'},
            'sokoban_position' => $e->{'sokoban_position'},
            'kill'             => 0,
            'base'             => 0,
        };
        if (move_is_deadlocked($brd, $m, 1, DRAGONFLY)) {
            return 0;
        }
    }
    $brd = dragonfly_get_board($e);
    my $has_corral = 0;
    @moves = find_possible_moves($brd, 1, \$has_corral, NORMAL, $h);
    my $moves_num = scalar @moves;
    return 0 if $moves_num == 0;
    mark_moves_when_corral($brd, \@moves, $moves_num, $e->{'move_to'}, \@possible);
    for my $i (0 .. $moves_num - 1) {
        $c          = $brd;
        $c          = apply_move($c, $moves[$i], NORMAL);
        $hashes[$i] = get_board_hash($c);
        $packed[$i] = boxes_on_bases($c);
    }
    dragonfly_mark_visited_hashes(\@hashes, $moves_num, \@visited);
    my $base_score = {};
    compute_base_distance($brd, $base_score, \@moves, \@scores);
    if ($e->{'dist'} >= 0) {
        Carp::confess('dist bug')
            if $base_score->{'dist_to_targets'} != $e->{'dist'};
    }
    for my $i (0 .. $moves_num - 1) {
        next if $visited[$i] == 1;
        if ($possible[$i] == 0) {
            $visited[$i] = 1;
            next;
        }
        if ($scores[$i]{'dist_to_targets'} >= 1000000) {
            $visited[$i] = 1;
            next;
        }
        my $new_node = {
            'board'            => 0xff,
            'depth'            => $e->{'depth'} + 1,
            'dist'             => $scores[$i]{'dist_to_targets'},
            'father'           => $node_index,
            'move_from'        => $moves[$i]{'from'},
            'move_to'          => $moves[$i]{'to'},
            'sokoban_position' => $moves[$i]{'sokoban_position'},
            'packed'           => $packed[$i],
        };
        if ($visited[$i] < 0) {
            if ($h->{'perimeter_found'} == 0) {
                $h->{'perimeter_found'} = 1;
            }
            $new_node->{'dist'} = $visited[$i];
        }
        $Dragonfly_nodes->[$Dragonfly_nodes_num++] = $new_node;
        dragonfly_heap_insert(\%Dragonfly_q, $Dragonfly_nodes_num - 1);
    } ## end for my $i (0 .. $moves_num...)
    dragonfly_update_perimeter(\@hashes, \@visited, $moves_num, $e->{'depth'} + 1);
    return 1;
} ## end sub dragonfly_expand_node

sub dragonfly_node_is_solved ($e) {
    my $brd;
    return 0 if $e->{'dist'} > 0;
    $brd = dragonfly_get_board($e);
    return board_is_solved($brd, 1);
}

sub dragonfly_search ($b_in, $time_allocation, $h) {
    my @start_zones;
    my ($brd, $c);
    my $start_time = time();
    (\%Dragonfly_q)->{'elements'}  = [];
    (\%Dragonfly_q)->{'heap_size'} = 0;
    $Dragonfly_nodes_num    = 0;
    $Dragonfly_roots_num    = 0;
    $Dragonfly_nodes->@*    = ();
    $h->{'perimeter_found'} = 0;
    $brd                    = $b_in;
    $brd                    = enter_reverse_mode($brd, 0);
    my $start_zones_num = compute_start_zones(\@start_zones);

    for my $i (0 .. $start_zones_num - 1) {
        $c = $brd;
        $c = put_sokoban_in_zone($c, \@start_zones, $i);
        add_dragonfly_root($c);
    }
    my $best_so_far = $Dragonfly_nodes->[0];
    while (1) {
        last if $Any_core_solved;
        last if time() > $start_time + $time_allocation;
        last if run_aborted();
        my $node_index = dragonfly_extarct_max(\%Dragonfly_q);
        if ($node_index == -1) {
            last;
        }
        ++$Solve_nseen;
        my $e = $Dragonfly_nodes->[$node_index];
        if (dragonfly_node_is_solved($e)) {
            last;
        }
        my $res = dragonfly_expand_node($node_index, $h);
        $best_so_far = $e
            if $res == 1
            and $e->{'dist'} < $best_so_far->{'dist'}
            and $e->{'dist'} >= 0;
        next unless (perimeter_is_full());
        last;
    } ## end while (1)
    (\%Dragonfly_q)->{'elements'}  = [];
    (\%Dragonfly_q)->{'heap_size'} = 0;
    return;
} ## end sub dragonfly_search

sub _allocate () {
    return if $Allocated;
    $Log_perimeter_size = 25;
    %Perimeter          = ();
    allocate_deadlock_cache();
    init_dragonfly();
    $Tree = {};
    init_tree($Tree);
    $Helper = Storable::dclone($HELPER_TEMPLATE);
    $Allocated = 1;
    return;
}
sub modes () {return @FF_NAME}

sub _install ($fest, $group) {
    for my $e (@ANALYSIS_STATE) {
        my ($g, $k, $r) = @$e;
        next if $g ne $group;
        Carp::confess("initvars: the stored analysis has no '$k' -- " . 'it was built by different code, analyse the level again')
            unless exists $fest->{$k};
        if    (ref $r eq 'ARRAY') {@$r = @{ Storable::dclone($fest->{$k}) }}
        elsif (ref $fest->{$k})   {$$r = Storable::dclone($fest->{$k})}
        else                      {$$r = $fest->{$k}}
    }
    return;
}
sub initvars_FF_GIRL ($fest) {return _install($fest, 'FF_GIRL')}

sub prepare_pattern_offsets () {
    for my $pt (@Patterns, @Pull_patterns) {
        my @f;
        push @f, $_->[0] * $Width + $_->[1], $_->[2] for @{ $pt->{'cells'} };
        $pt->{'flat'} = \@f;
    }
    return;
}

sub derive_from_analysis () {
    init_board_geometry();
    $Initial_sokoban_p = $Global_initial_sokoban_y * $Width + $Global_initial_sokoban_x;

    # The two sets the matching-distance subs pair the boxes AGAINST. Both are
    # properties of the level, and both used to be rebuilt with a whole-board
    # scan on every scored position: measured over 11 games x 8 modes, they came
    # out as ONE set per game against 1241 and 1537 different box layouts, i.e.
    # 3410 scans that produced the same answer every time.
    #
    # The bases are constant by construction rather than by measurement:
    # $Initial_board has two writes in the whole module (this file's init and the
    # install from the blob) against 24 reads.
    #
    # THE CHECK THAT STOOD BEHIND EACH SCAN STAYS, comparing the box count with
    # the stored count. What was measured is that the set did not vary in those
    # runs, NOT that it cannot -- turn_targets_into_walls rewrites target bits
    # somewhere -- so the scan goes and the assertion does not.
    @Target_indices = grep {vec($Initial_board, $Index_to_p[$_], 8) & TARGET} 0 .. $Index_num - 1;
    @Base_indices   = grep {vec($Initial_board, $Index_to_p[$_], 8) & BOX} 0 .. $Index_num - 1;
    $INNER_ONLY     = join '', map {vec($Inner, $_, 8) ? "\xFF" : "\0"} 0 .. $Ncells - 1;
    $Inv_epsilon    = $Global_boxes_in_level + 1;
    $DZ_len         = -1;
    _dz_masks();
    prepare_pattern_offsets();
    return;
} ## end sub derive_from_analysis

sub initvars ($fest) {
    Carp::confess('initvars: no level analysis (the frozen analysis is empty?)')
        unless ref $fest eq 'HASH';
    _install($fest, 'core');
    derive_from_analysis();
    return;
}

sub load_level ($blob, $alg) {
    my $fest = eval {Storable::thaw(Compress::Zlib::uncompress($blob))};
    Carp::confess('load_level: the frozen analysis is empty, corrupt, or stamped by analysis '
            . "code this engine does not read (it reads '" . FEST_STAMP . "') "
            . '-- analyse the level again with Games::Sokoban::Solver::Festival::Analysis')
        unless ref $fest eq 'HASH' and ($fest->{'stamp'} // q{}) eq FEST_STAMP;
    $Girl_distance = [];
    initvars($fest);
    initvars_FF_GIRL($fest) if $alg == $FF_MODE{'FF_GIRL'} or $alg == -1;
    Carp::confess('$BLOK_REPLACES is on but this analysis has no blok key '
            . '-- the deadlock battery would be skipped with nothing standing in '
            . 'for it (Festival::Analysis::with_blok puts the Parser\'s table there)')
        if $BLOK_REPLACES and !exists $fest->{'blok'};
    if   ($BLOK_REPLACES) {$Blok_usable = set_blok($fest->{'blok'}) > 0 ? 1 : 0}
    else                  {undef %Blok_sets; $Blok_usable = 0}
    undef $fest;
    %Cache                        = ();
    %Perimeter                    = ();
    $Total_deadlock_cache_entries = 0;
    $Total_perimeter_entries      = 0;
    $K_dist_hash_num              = 0;
    @Stuck_patterns               = ();
    $Global_fail_reason           = 'Unknown reason';
    return expand_sokoban_cloud($Initial_board);
} ## end sub load_level

sub setup_plan_features ($search_type, $h) {
    return 1 if $search_type == HF_SEARCH;
    return 1 if $search_type == BICON_SEARCH;
    return 1 if $search_type == MAX_DIST_SEARCH;
    return 1 if $search_type == MAX_DIST_SEARCH2;
    return 1 if $search_type == REV_SEARCH;
    return 1 if $search_type == NAIVE_SEARCH;
    return 1 if $search_type == DRAGONFLY;
    if ($h->{'parking_order_num'} == 0) {
        $Global_fail_reason = 'Could not find packing order';
        return 0;
    }
    for my $i (0 .. $h->{'parking_order_num'}) {
        $h->{'oop'}{'oop_zone_for_step'}[$i] = $ZERO_BOARD;
    }
    verify_parking_order($h);
    reduce_parking_order($h);
    return 1 if $search_type == GIRL_SEARCH;
    prepare_oop_zones($h);
    return 1;
} ## end sub setup_plan_features

sub packing_search_control ($brd, $time_allocation, $search_type, $t, $h) {
    my $end_time = time() + $time_allocation;
    if ($time_allocation <= 0) {
        $Global_fail_reason = 'No time for packing search';
        return;
    }
    $Progress{'phase'}      = 'pack';
    $h->{'weighted_search'} = 1;
    $search_type            = set_snail_parameters($search_type, 1, $h);
    $search_type            = set_netlock_parameters($search_type, 1, $h);
    $time_allocation *= 2 if $search_type == SNAIL_SEARCH;
    $time_allocation *= 2 if $search_type == NETLOCK_SEARCH;
    $time_allocation *= 3 if $search_type == DRAGONFLY;

    if ($search_type == REV_SEARCH) {
        FESS($brd, $time_allocation, $search_type, $t, $h);
        return;
    }
    if ($search_type == DRAGONFLY) {
        dragonfly_search($brd, $time_allocation, $h);
        return;
    }
    packing_search($brd, $time_allocation, $search_type, $t, $h);
    return;
} ## end sub packing_search_control

sub forward_search_control ($brd, $time_allocation, $search_type, $t, $h) {
    my $end_time = time() + $time_allocation;
    if ($time_allocation <= 0) {
        $Global_fail_reason = 'No time for forward search';
        return;
    }
    $Progress{'phase'}      = 'fwd';
    $h->{'weighted_search'} = 1;
    $search_type            = set_snail_parameters($search_type, 0, $h);
    $search_type            = set_netlock_parameters($search_type, 0, $h);
    if (($search_type == HF_SEARCH or $search_type == REV_SEARCH)
        and length($h->{'imagined_hf_board'}) < $Ncells)
    {
        $Global_fail_reason = 'No imagined board';
        return;
    }
    if ($search_type == HF_SEARCH) {
        $h->{'weighted_search'} = 0;
        FESS($brd, int($time_allocation * 3 / 4), $search_type, $t, $h);
        return if $h->{'level_solved'};
        $h->{'weighted_search'} = 1;
        $time_allocation = $end_time - time();
        FESS($brd, $time_allocation, $search_type, $t, $h);
        return;
    }
    if ($search_type == REV_SEARCH) {
        packing_search($brd, $time_allocation, $search_type, $t, $h);
        if ($h->{'perimeter_found'} == 0) {
            $Global_fail_reason = 'Perimeter not reached';
            return;
        }
        $time_allocation = $end_time - time();
    }
    FESS($brd, $time_allocation, $search_type, $t, $h);
    return;
} ## end sub forward_search_control

sub solve_with_alg ($brd, $time_allocation, $strategy_index, $h) {
    my @backward_search_type =
        (BASE_SEARCH, MAX_DIST_SEARCH2, GIRL_SEARCH, HF_SEARCH, BICON_SEARCH, MAX_DIST_SEARCH, REV_SEARCH, DRAGONFLY,);
    my @forward_search_type =
        (FORWARD_WITH_BASES, HF_SEARCH, GIRL_SEARCH, HF_SEARCH, HF_SEARCH, HF_SEARCH, REV_SEARCH, NAIVE_SEARCH,);
    if ($time_allocation <= 0) {
        $Global_fail_reason = 'No time to start';
        return;
    }
    reset_helper($h);
    my $t                = $Tree;
    my $search_type      = $backward_search_type[$strategy_index];
    my $local_start_time = time();
    packing_search_control($brd, int($time_allocation / 3), $search_type, $t, $h);
    return if setup_plan_features($search_type, $h) == 0;
    my $remaining_time = $local_start_time + $time_allocation - time();
    $search_type = $forward_search_type[$strategy_index];
    forward_search_control($brd, $remaining_time, $search_type, $t, $h);
    return;
} ## end sub solve_with_alg

sub sol_moves_string ($h) {
    my $sok_p = $Initial_sokoban_p;
    my $brd;
    $brd = $Initial_board;
    my $sol = '';
    my $n   = $h->{'sol_len'};
    for my $i (0 .. $n - 1) {
        my $m               = $h->{'sol_move'}[$i];
        my $start_box_index = $m->{'from'};
        my $end_box_index   = $m->{'to'};
        my $next_sok_p      = $Index_to_p[$end_box_index] + $Delta_p[$m->{'sokoban_position'}];
        $sol .=
            find_sol_move($brd, $Y_x_to_index_table[$sok_p], $start_box_index, $Y_x_to_index_table[$next_sok_p], $end_box_index);
        $sok_p = $next_sok_p;
        $brd   = apply_move($brd, $m, NORMAL);
    }
    return $sol;
} ## end sub sol_moves_string

sub report_ending ($label, $gameid, $reason, $path, $doba) {
    my $ending = sprintf ENDING,
        $label, $gameid, $Global_boxes_in_level, $Index_num, $reason,
        (defined $path ? length $path         : 0),
        (defined $path ? ($path =~ tr/UDRL//) : 0),
        $doba, q{}, sprintf('%.0f', $Solve_nseen / $doba), q{},
        ($Helper->{'sol_len'} // 0), $Solve_nseen;
    barva($reason,$ending);
    return;
}

sub solve ($gameid, $blob, $limit = 60, $mode = undef) {
    _allocate();
    $LastFail     = '';
    $Abort_reason = '';
    $Solve_nseen  = 0;
    my $t0 = Time::HiRes::time();
    $Time_limit = $limit;
    my $alg =
        defined $mode && $mode ne 'FF_ALL'
        ? ($FF_MODE{$mode} // Carp::confess("unknown Festival mode $mode"))
        : -1;
    $Next_poll = time() + ($alg > 0 ? $alg : 0);
    $Tick      = 0;    # the race flag's own one-second gate, per solve
    %Progress = ('label' => $mode // 'FF_ALL', 'gameid' => $gameid, 't0' => $t0, 'phase' => 'load');
    my $start_time = time();
    $Any_core_solved = 0;
    reset_helper($Helper);
    my $won = $alg;
    my $brd = load_level($blob, $alg);

    if ($alg != -1) {
        solve_with_alg($brd, int(($start_time + $Time_limit - time()) * (1.0)), $alg, $Helper);
    }
    else {
        for my $i (0 .. 7) {
            $Progress{'label'} = '*' . $FF_NAME[$i];
            solve_with_alg($brd, int(($start_time + $Time_limit - time()) * (1 / (8 - $i))), $i, $Helper);
            $won = $i;
            last if $Helper->{'level_solved'} or $Abort_reason;
        }
    }
    my $doba = Time::HiRes::time() - $t0;
    $doba = 0.000001 if $doba < 0.000001;
    my ($reason, $path);
    if ($Helper->{'level_solved'}) {
        $reason = 'SOLVED';
        $path   = Games::Sokoban::Solver::Path::rebuilt(
            'path'   => sol_moves_string($Helper),
            'width'  => $Width,
            'floor'  => [grep {!(vec($Initial_board, $_, 8) & WALL)} 0 .. $Ncells - 1],
            'goals'  => [grep {vec($Initial_board, $_, 8) & TARGET} 0 .. $Ncells - 1],
            'boxes'  => [grep {vec($Initial_board, $_, 8) & BOX} 0 .. $Ncells - 1],
            'player' => $Initial_sokoban_p,
        );
    }
    elsif ($Abort_reason) {$reason = $Abort_reason}
    else {
        $LastFail = $Global_fail_reason;
        $reason   = ($doba >= $limit || $Global_fail_reason eq 'Unknown reason') ? 'TIMEOUT' : 'FAILED';
    }
    my $label =
        (defined $mode && $mode ne 'FF_ALL')
        ? $mode
        : ($reason eq 'SOLVED' && $won >= 0 ? '*' . $FF_NAME[$won] : 'FF_ALL');
    report_ending($label, $gameid, $reason, $path, $doba);
    return ($reason, $path, $doba, $Solve_nseen);
} ## end sub solve
1;
