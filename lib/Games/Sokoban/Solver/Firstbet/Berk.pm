# Storage twin of Games::Sokoban::Solver::Firstbet -- SAME search, state on disk.
# Comment-free by design: the why lives in Berk.pod beside this file and in the
# baseline. In the Sokoban project this file (Games::Sokoban::FirstbetBerk 3.8)
# was REBUILT from the promoted baseline by a generator, never hand-edited; here
# it is that build with its dependencies rewired, as the baseline's were.
package Games::Sokoban::Solver::Firstbet::Berk;


our $VERSION = '0.01';

use v5.42;
use experimental 'refaliasing', 'declared_refs';
use warnings FATAL => 'uninitialized';
no warnings 'recursion';
use Carp           ('confess');
use Time::HiRes    ('tv_interval', 'gettimeofday');
use Storable       ('thaw', 'dclone');
use List::Util     ('max');
use Compress::Zlib;
use Term::ANSIColor;
use Games::Sokoban::Solver::Berkeley ();
use Games::Sokoban::Solver::Console  ('backline', 'backlinen', 'podil');
use Games::Sokoban::Solver::Data     ();
use Games::Sokoban::Solver::Heap     ();
use Games::Sokoban::Solver::Memory   ();
use Games::Sokoban::Solver::Munkres  ();
use Games::Sokoban::Solver::Path     ();

my (%Game, @Goal, @Target, %Cm, %Cmk, @Baggage, @Maze, $W);
my (%Parent, $Start);
my ($PaintId, @Vis);
my ($PaintId_fr, @Vis_fr);
my @Buf;
my $BIG = 1_000_000;

my $ENDING = '%-12s %5d %3d %4d %-10s %6d %6d %12.4f %8s %8s %8s %8s %9s';

my (
    @Cg, %Pis, @Priority, $Has_hole, $Has_wall,
    $Has_corridor, $Hole, $Wall, $Corridor, $Blok, $Gameid
   );
my $BlokVec;
my ($Nbox, %Sols, $Distance, $MaxP, $MaxVal, $corridors, $holes);
my ($DistRaw, $Value);
my ($Route, $RouteBonus, $Has_cp, %CPath);
my (%CPathIdx, @CPathArr, %ToGoal);
my ($RouteMoves, $RouteMust, $Has_routes);
my $Macro_step = 0;
my ($Pex, %Tahy, $Bestbet, $pu);
my @Blk;
my @Buf_fr;
my @IsWall;

my (%CanonMap, @Vis_c, @Buf_c, $PaintId_c, %SolsC, $SolvedLay, $ManOff);

my $Feat_mode = 0;
my (%FCellQ, @FCellKey, $FCellPtr);
my %ExplMark;
my %RegCells;
my %StanceIdx;
my (@RoomOf, @DoorAt);
my $NRooms;
my @PlanNeed;
my (@PlanPair, @PlanInit, @PlanWaves);
my $Plan_waves = 0;
my (@Vis_ci, @FloorCells);
my $PaintId_ci = 0;

my (%ReachG, %Selective);
my (%Rev, %ReachW);
my $Walled_on    = 0;
my $Match_active = 0;

my $CP_mode_ok = 1;

my ($FLOW_W, $FLOW_Q) = (100_000, 4);

$corridors = Games::Sokoban::Solver::Data::load('corridor_pattern.stor');
$holes     = Games::Sokoban::Solver::Data::load('hole_pattern.stor');

our $CACHE = 536870912;
our $STORE_PER_MODE = 0;
my %MemBad;
my ($UseBerk, $UseBwd);
my $Nseen  = 0;
my $BackN  = 0;

our $QUIET = 0;

my $SCREEN = 6;

our ($RACE_FLAG, $RACE_GID);
sub race_lost() { $RACE_FLAG && $RACE_GID && $RACE_FLAG->{$RACE_GID} }

our $MAX_GB = 0;
sub mem_over() { $MAX_GB && Games::Sokoban::Solver::Memory::used_gb() > $MAX_GB }

sub clamp_doba($doba) { $doba < 0.000001 ? 0.000001 : $doba }

sub barva($reason,$ending) {
   return if $QUIET > 1;
   state $colour = {'SOLVED', 'bright_green', 'TIMEOUT', 'bright_yellow', 'IGNORE', 'white' };
   my $color = $colour->{$reason} // 'bright_red';
   backlinen(Term::ANSIColor::colored($ending,$color));
}

sub state_init($gameid, $mode) {
    %MemBad = ();
    %Tahy   = ();
    %Parent = ();
    if    ($UseBerk) {Games::Sokoban::Solver::Berkeley::fb_init($gameid, $CACHE, $STORE_PER_MODE ? $mode : q{})}
    elsif ($UseBwd)  {Games::Sokoban::Solver::Berkeley::fb_bwd_init($gameid, $CACHE)}
    $Nseen = 0;
}

sub state_close($solved) {
    if ($UseBerk) {
        my $n = Games::Sokoban::Solver::Berkeley::fb_pos_count();
        Carp::confess("seen-set accounting: \$Nseen=$Nseen, table holds $n")
            if $n != $Nseen;
        Games::Sokoban::Solver::Berkeley::fb_close();
    }
    elsif ($UseBwd) {Games::Sokoban::Solver::Berkeley::fb_bwd_close()}
}

sub setbad($p)       {$UseBerk ? Games::Sokoban::Solver::Berkeley::fb_setbad($p)       : ($MemBad{$p} = 1)}
sub isbad($p)        {$UseBerk ? Games::Sokoban::Solver::Berkeley::fb_isbad($p)        : exists $MemBad{$p}}
sub tahy_get($p)     {$UseBerk ? Games::Sokoban::Solver::Berkeley::fb_tahy_get($p)     : $Tahy{$p}}
sub tahy_set($p, $k) {$UseBerk ? Games::Sokoban::Solver::Berkeley::fb_tahy_set($p, $k) : ($Tahy{$p} = $k)}
sub tahy_del($p)     {$UseBerk ? Games::Sokoban::Solver::Berkeley::fb_tahy_del($p)     : delete $Tahy{$p}}

sub seen_has($p)     {$UseBerk ? Games::Sokoban::Solver::Berkeley::fb_pos_present($p) : exists $Parent{$p}}
sub discover($p, $f) {++$Nseen; $UseBerk ? Games::Sokoban::Solver::Berkeley::fb_pos_set($p, $f) : ($Parent{$p} = $f)}
sub parent_get($p)   {$UseBerk ? Games::Sokoban::Solver::Berkeley::fb_pos_parent($p)  : $Parent{$p}}

sub node_del($p) {
    if ($UseBerk) {
        return unless Games::Sokoban::Solver::Berkeley::fb_pos_present($p);
        my $father = Games::Sokoban::Solver::Berkeley::fb_pos_parent($p);
        --$Nseen;
        Games::Sokoban::Solver::Berkeley::fb_pos_del($p);
        return $father;
    }
    return unless exists $Parent{$p};
    --$Nseen;
    return delete $Parent{$p};
}

sub bseen_has($p)     {Games::Sokoban::Solver::Berkeley::fb_bseen_has($p)}
sub bseen_get($p)     {Games::Sokoban::Solver::Berkeley::fb_bseen_get($p)}
sub bseen_set($p, $v) {Games::Sokoban::Solver::Berkeley::fb_bseen_set($p, $v); ++$BackN; return}


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
    %Pis          = ();
    %Sols         = ();
    @Target       = ();
}

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
}

sub replay_check($path) {
    my %step = ('l', -1, 'r', 1, 'u', -$W, 'd', $W);
    my %box  = map(($_, 1), @Baggage);
    my $cell = $Game{'player'};
    my $i    = -1;
    foreach my $ch (split //, $path) {
        ++$i;
        my $d = $step{ lc $ch } // confess("the solution does not replay: step $i is '$ch'");
        my $to = $cell + $d;
        confess("the solution does not replay: step $i '$ch' walks into a wall")
            if $to < 0 or $to > $#Maze or $Maze[$to] eq '9' or $Maze[$to] eq '1';
        if (exists $box{$to}) {
            my $beyond = $to + $d;
            confess("the solution does not replay: step $i '$ch' pushes the box on cell $to against a wall or another box")
                if $beyond < 0 or $beyond > $#Maze or $Maze[$beyond] eq '9' or $Maze[$beyond] eq '1' or exists $box{$beyond};
            delete $box{$to};
            $box{$beyond} = 1;
        }
        $cell = $to;
    }
    for my $g (@Goal) {
        confess("the solution does not replay: after its last step the goal on cell $g holds no box") unless exists $box{$g};
    }
    return;
}

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
    while (($p = parent_get($p))) {
        confess 'INFINITE CYCLE!' if $vidi{$p}++;
        unshift @postup, $p;
    }
    confess 'NOT A START' unless $Start eq $postup[0];
    return @postup;
}

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
        $cell = $source;
        @fb   = @sb;
        $father = $son;
    }
    return $path;
}

sub initvars_common($gameid, $gm, $mode) {
    clearvars();
    $UseBerk = $mode ne 'BACKWARD' && $mode ne 'ORDER';
    $UseBwd  = $mode eq 'BACKWARD';
    state_init($gameid, $mode);
    $Gameid    = $gameid;
    $Feat_mode = $mode eq 'FEATURE' ? 1 : 0;
    %Game   = %{ thaw(uncompress($gm)); };
    my $maze = $Game{'code'};
    $maze =~ tr/,//d;
    $maze =~ tr/45678/00233/;
    @Maze         = split(//a, $maze, 0);
    $Game{'maze'} = &dclone(\@Maze);
    @IsWall       = map {$_ eq '9' ? 1 : 0} @Maze;
    @Goal         = @{ $Game{'goal'}; };
    @Target       = ();
    $Target[$_]   = 1 foreach @Goal;
    %Cm           = %{ $Game{'cm'};  };
    %Cmk          = %{ $Game{'cmk'}; };
    @Cg           = ();
    $Cg[$_]       = $Game{'cg'}{$_} foreach keys %{ $Game{'cg'} };
    @Baggage      = @{ $Game{'baggage'}; };
    $W            = $Game{'w'};
    %Pis          = (-1, 'l', 1, 'r', $W, 'd', -$W, 'u');
    $Nbox         = scalar @Baggage;
    @Priority     = ();
    $Priority[$_] = $Game{'order'}{$_} foreach keys %{ $Game{'order'} };
    ($Has_hole, $Has_wall, $Has_corridor) = @Game{ 'has_hole', 'has_wall', 'has_corridor' };
    ($Blok, $BlokVec) = _blok_both($Game{'blok'});
    $Hole     = &dclone($Game{'hole'})     if $Has_hole;
    $Wall     = &dclone($Game{'walls'})    if $Has_wall;
    $Corridor = &dclone($Game{'corridor'}) if $Has_corridor;

    _corral_geom();

    $Pex = 'Games::Sokoban::Solver::Heap'->new;
    %ExplMark  = ();
    %RegCells  = ();
    %StanceIdx = ();
    if ($Feat_mode) {
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
    $Bestbet    = undef;
    %Sols       = %{ $Game{'sols'} };
    $PaintId    = 0;
    $PaintId_fr = 0;
    @Blk        = (0) x scalar @Maze;
    @Vis        = (0) x scalar @Maze;
    @Vis_fr     = (0) x scalar @Maze;

    $pu    = $Game{'vzp'};
    $Start = pack($pu, $Game{'player'}, @{ $Game{'baggage'} });

    %CanonMap  = ();
    %SolsC     = ();
    @Vis_c     = (0) x scalar @Maze;
    $PaintId_c = 0;
    $ManOff    = length pack($pu, 0);
    $SolvedLay = (@Goal == $Nbox) ? pack($pu, sort {$a <=> $b} @Goal) : undef;
    foreach my $k (keys %Sols) {
        my $t = $Sols{$k};
        next unless defined $t && $t =~ /[A-Za-z]/;
        my ($m, @bb) = unpack($pu, $k);
        my $ck = canon_key($m, \@bb);
        $SolsC{$ck} = [$m, $t] if !exists $SolsC{$ck} || length($t) < length($SolsC{$ck}[1]);
    }
}

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
}



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
            $Vis_c[$t] = $PaintId_c;
            $Buf_c[$bt++] = $t;
            $min = $t if $t < $min;
        }
    }
    my $key = pack($pu, $min, @$bag);

    if ($Feat_mode) {
        my @new = grep {$Vis[$_] != $PaintId} @Buf_c[ 0 .. $bt - 1 ];
        $RegCells{$key} = \@new if @new;
    }
    return $key;
}

sub _ck($man, $bag) {
    return $CanonMap{ pack($pu, $man, @$bag) } //= canon_key($man, $bag);
}

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

            next if $Vis[$t] == $PaintId || $Blk[$t] == $PaintId;
            $Vis[$t] = $PaintId;
            $Buf[$bt++] = $t;
        }
    }
}

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
}

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
                next if exists $frozen{$stance};
                next unless $Vis_fr[$stance] == $PaintId_fr;
                $movable = 1;
                last;
            }
            push @still_frozen, $bx unless $movable;
        }
        last if scalar @still_frozen == scalar %frozen;
        %frozen = map(($_, 1), @still_frozen);
    }
    return ('', ()) unless %frozen;
    for (keys %frozen) {return ('frozen', ()) unless $Target[$_]}
    return ('', keys %frozen);
}


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
}

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
                if ($num[$y]) { $low[$x] = $num[$y] if $num[$y] < $low[$x] }
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
                    $low[$p] = $low[$x] if $low[$x] < $low[$p];
                    $door{$p} = 1 if $p != $root && $low[$x] >= $num[$p];
                }
            }
        }
        $door{$root} = 1 if $rootkids > 1;
    }

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

    $RoomOf[$_] = 0 for keys %door;
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
                push @q, $y;
            }
        }
        my %rooms;
        for my $c (@cells) {
            $rooms{ $RoomOf[$_] } = 1 for grep {$RoomOf[$_]} @{ $Cg[$c] // [] };
        }
        next if keys(%rooms) < 2;
        my $door = [[@cells], [keys %rooms]];
        $DoorAt[$_] = $door for @cells;
    }
    return;
}

sub room_groups($t_bag) {
    return 1 unless $NRooms;
    my @up = (0 .. $NRooms);
    my $n  = $NRooms;
    my %done;
    for my $d (0 .. $#DoorAt) {
        my $door = $DoorAt[$d] or next;
        next if $done{$door}++;
        my ($cells, $ids) = @$door;
        next if grep {exists $t_bag->{$_}} @$cells;
        my $a = $ids->[0];
        $a = $up[$a] while $up[$a] != $a;
        for my $i (1 .. $#$ids) {
            my $b = $ids->[$i];
            $b = $up[$b] while $up[$b] != $b;
            next if $a == $b;
            $up[$b] = $a;
            --$n;
        }
    }
    return $n;
}

sub build_planneed() {
    @PlanNeed = ();
    for my $p (@PlanPair) {
        my ($goal, undef, undef, $pulls) = @$p;
        my %c;
        for my $step (@$pulls) { $c{ $step->[0] } = 1; $c{ $step->[1] } = 1 }
        delete $c{$goal};
        $PlanNeed[$goal] = [keys %c] if %c;
    }
    return;
}

sub out_of_plan($t_bag) {
    return 0 unless @PlanNeed;
    my %hit;
    for my $goal (0 .. $#PlanNeed) {
        my $need = $PlanNeed[$goal] or next;
        next if exists $t_bag->{$goal};
        for my $c (@$need) { $hit{$c} = 1 if exists $t_bag->{$c} && !$Target[$c] }
    }
    return scalar keys %hit;
}

sub feat_counts($pozice) {
    my (undef, @bb) = unpack($pu, $pozice);
    my %bag = map(($_, 1), @bb);
    return (plan_odometer(\@bb), conn_islands(\%bag), room_groups(\%bag), out_of_plan(\%bag));
}

sub feat_key($pozice) { join ',', feat_counts($pozice) }

sub feat_better($x, $y) {
    return $x->[1] > $y->[1] if $x->[1] != $y->[1];
    return $x->[2] < $y->[2] if $x->[2] != $y->[2];
    return $x->[3] < $y->[3] if $x->[3] != $y->[3];
    return $x->[4] < $y->[4] if $x->[4] != $y->[4];
    return 0;
}

sub feat_advise($kids, $b_odo, $b_isl, $b_room, $b_out) {
    my $n = 0;
    for my $crit (0 .. 4) {
        my $best;
        for my $k (@$kids) {
            next if $k->[1] < $b_odo;
            my $speaks =
                  $crit == 0 ? $k->[1] > $b_odo
                : $crit == 1 ? $k->[2] < $b_isl
                : $crit == 2 ? $k->[3] < $b_room
                : $crit == 3 ? $k->[4] < $b_out
                :              $k->[5];
            next unless $speaks;
            $best = $k if !defined $best || feat_better($k, $best);
        }
        next unless $best;
        ++$n unless $best->[6];
        $best->[6] = 1;
    }
    my $best;
    for my $k (@$kids) {
        next if $k->[1] < $b_odo;
        $best = $k if !defined $best || $k->[7] < $best->[7];
    }
    if ($best) {
        ++$n unless $best->[6];
        $best->[6] = 1;
    }
    return $n;
}


sub value_score($bx, $t, $t_bag) {
    my (@free, $index, $value);
    @free = grep(!exists $t_bag->{$_}, @Goal);
    return 0 unless @free;
    $index = &max(@Priority[@free]);
    @free  = grep(($Priority[$_] >= $index), @free);
    $value = $MaxVal;
    foreach my $box (keys %$t_bag) {
        my $pb = $Priority[$box];
        if (defined $pb and $pb >= $index) {

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
    }

    $value -= $RouteBonus
        if !$Macro_step && exists $Route->{$bx} && exists $Route->{$bx}{$t};
    return $value;
}

sub value_assign($bx, $t, $t_bag) {
    my @bag = grep {!$Target[$_]} keys %$t_bag;
    return 0 unless @bag;
    my @free = grep {!exists $t_bag->{$_}} @Goal;
    return $DistRaw->{ $bag[0] }{ $free[0] } // $BIG if @bag == 1;
    my @matrix;
    for my $g (@free) {
        push @matrix, [map {$DistRaw->{$_}{$g} // $BIG} @bag];
    }
    return Games::Sokoban::Solver::Munkres::assign(\@matrix);
}

sub raw_table($src) {
    my %out;
    for my $bx (keys %$src) {
        my $row = $src->{$bx};
        $out{$bx}{$_} = (!defined $row->{$_} || $row->{$_} eq 'Inf') ? $BIG : $row->{$_}
            for keys %$row;
    }
    return \%out;
}

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

sub value_route($bx, $t, $t_bag) {
    return 0 if $Macro_step;
    my $r = $Route->{$bx};
    my $v = 0;
    $v -= 2 if $r          && $r->{$t};
    $v -= 1 if $CPath{$bx} && $CPath{$bx}{$t};
    return $v;
}

sub value_flow($bx, $t, $t_bag) {
    my $r     = $Route->{$bx};
    my $route = 0;
    unless ($Macro_step) {
        $route -= 2 if $r          && $r->{$t};
        $route -= 1 if $CPath{$bx} && $CPath{$bx}{$t};
    }

    my $sum = 0;
    for my $b (keys %$t_bag) {
        next if $Target[$b];
        my $row  = $DistRaw->{$b} or next;
        my $best = $BIG;
        for my $g (@Goal) {
            next if exists $t_bag->{$g};
            my $v = $row->{$g};
            $best = $v if defined $v && $v < $best;
        }
        $sum += $best if $best != $BIG;
    }
    return $route * $FLOW_W + int($sum / $FLOW_Q);
}


sub is_bad($bx, $t, $t_bag, $vb = undef) {

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

        BLK: foreach my $bl (@$blok) {
                foreach (@$bl) {
                    next BLK unless exists $t_bag->{$_};
                }
                return 'blok';
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
        }
    }
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
}

sub set_bad($pozice) {
    return if isbad $pozice;
    setbad $pozice;
    my @bads;

    if (my $cached = tahy_get($pozice)) {
        tahy_del($pozice);
        @bads = @$cached;
    }
    if (my $father = node_del($pozice)) {
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
}

sub matching_deadlock(@boxes) {

    my $any_sel = 0;
    for my $b (@boxes) {$any_sel = 1, last if $Selective{$b}}
    return 0 unless $any_sel;

    my %union;
    for my $b (@boxes) {
        my $rg = $ReachG{$b} or return 0;
        $union{$_} = 1 for keys %$rg;
    }
    return 1 if keys %union < @boxes;

    my @matrix;
    for my $b (@boxes) {
        my $rg = $ReachG{$b};
        push @matrix, [map {$rg->{$_} ? 0 : $BIG} @Goal];
    }
    return Games::Sokoban::Solver::Munkres::assign(\@matrix) >= $BIG ? 1 : 0;
}

sub fix_diagonals ($bag, $wall) {
    my %w     = %$wall;
    my $h     = int(@Maze / $W);
    my $ncell = scalar @Maze;

    my %cand;
    for my $b (keys %$bag) {
        $cand{ $b - $W } = 1;
        $cand{ $b + $W } = 1;
        $cand{ $b - 1 }  = 1;
        $cand{ $b + 1 }  = 1;
    }

    my (@inner, @pocket);
    for my $p (keys %cand) {
        next if $p < 0 || $p >= $ncell;
        my $i = int($p / $W);
        my $j = $p % $W;
        next if $i < 1 || $i > $h - 2 || $j < 1 || $j > $W - 2;
        next if $IsWall[$p] || $w{$p} || $bag->{$p};
        next if $Vis[$p] == $PaintId;
        my $n = $p - $W;
        next unless $IsWall[$n] || $w{$n} || $bag->{$n};
        $n = $p + $W;
        next unless $IsWall[$n] || $w{$n} || $bag->{$n};
        $n = $p + 1;
        next unless $IsWall[$n] || $w{$n} || $bag->{$n};
        $n = $p - 1;
        next unless $IsWall[$n] || $w{$n} || $bag->{$n};
        $inner[$p] = 1;
        push @pocket, $p;
    }

    my (@dr, @dl, @chain);
    for my $p (@pocket) {
        my $i = int($p / $W);
        my $j = $p % $W;
        for my $dir (1, -1) {
            my $up = $dir == 1 ? $p - $W - 1 : $p - $W + 1;
            my $sd = $dir == 1 ? $p - 1      : $p + 1;
            next unless ($IsWall[$up] || $w{$up} || $bag->{$up})
                || (($IsWall[ $p - $W ] || $w{ $p - $W }) && ($IsWall[$sd] || $w{$sd}));
            my $k = 1;
            ++$k while $inner[ ($i + $k) * $W + $j + $dir * $k ];
            my $ep = ($i + $k) * $W + $j + $dir * $k;
            my $ed = $dir == 1 ? $ep - 1 : $ep + 1;
            next unless ($IsWall[$ep] || $w{$ep} || $bag->{$ep})
                || (($IsWall[ $ep - $W ] || $w{ $ep - $W }) && ($IsWall[$ed] || $w{$ed}));
            if   ($dir == 1) {$dr[$p] = $k}
            else             {$dl[$p] = $k}
        }
        push @chain, $p if $dr[$p] || $dl[$p];
    }

    for my $p (sort {$a <=> $b} @chain) {
        my $i = int($p / $W);
        my $j = $p % $W;
        for my $set ([$dr[$p], 1], [$dl[$p], -1]) {
            my ($k, $dir) = @$set;
            next unless $k;
            my $goal = 0;
            for my $n (0 .. $k - 1) {$goal = 1 if $Target[ ($i + $n) * $W + $j + $dir * $n ]}
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
        }
    }
    delete $w{$_} foreach grep {!$bag->{$_}} keys %w;
    return \%w;
}

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
    }
    return $ReachW{$key} = \%by_goal;
}

sub matching_dead_walled ($boxes, $wall) {
    return 0 unless $Walled_on;
    my $key = join(',', sort {$a <=> $b} keys %$wall);
    return 0 unless length $key;
    my $wr = walled_reach($wall, $key);
    my @b  = grep {!$wall->{$_}} @$boxes;
    return 0 unless @b;
    my @g = grep {!$wall->{$_}} @Goal;
    return 1 if @b > @g;

    my (@matrix, %union);
    for my $b (@b) {
        my $rg = $ReachG{$b} or return 0;
        my @row;
        for my $goal (@g) {
            my $ok = ($rg->{$goal} && $wr->{$goal} && $wr->{$goal}{$b}) ? 1 : 0;
            $union{$goal} = 1 if $ok;
            push @row, $ok ? 0 : $BIG;
        }
        push @matrix, \@row;
    }
    return 1 if keys %union < @b;
    return Games::Sokoban::Solver::Munkres::assign(\@matrix) >= $BIG ? 1 : 0;
}


sub _macro_fill($cells_ref, $levels, $perm, $nb_ref, $man_start) {
    return () unless defined $levels;
    my @cells   = @$cells_ref;
    my %cur_bag = map(($_, 1), @$nb_ref);
    my $k       = (grep {exists $cur_bag{$_}} @cells[ 1 .. $#cells ]) - $perm;
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

        unless ($Vis_fr[$push_pos] == $PaintId_fr && !grep { $_ == $push_pos } @cur_nb) {

            if (@chain && !defined $chain[-1]) {
                my ($pf, $pt) = @{ $pushes->[$pi - 1] }[ 0, 1 ];
                $chain[-1] = $Value->($pf, $pt, { map(($_, 1), @cur_nb) });
            }
            last;
        }
        @cur_nb = grep($_ != $from, @cur_nb);
        my $j = 0;
        ++$j while $j < @cur_nb && $cur_nb[$j] < $to;
        splice(@cur_nb, $j, 0, $to);
        my $mc = _ck($from, \@cur_nb);
        push @chain, $mc, ($to == $target ? $Value->($from, $to, { map(($_, 1), @cur_nb) }) : undef);
    }
    return @chain;
}

sub _route_deliver($baggage, $bx, $moves, $me) {
    for my $b (@$baggage) {
        return () if $b != $bx && $me->{$b};
    }

    my $g     = $moves->[-1];
    my @fnb   = sort {$a <=> $b} map {$_ == $bx ? $g : $_} @$baggage;
    my $final = _ck($moves->[-2], \@fnb);
    return () if seen_has($final);

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
    }
    return @chain;
}

sub _cp_deliver($baggage, $start_idx) {
    my @cur = @$baggage;
    my %bag = map(($_, 1), @cur);
    my (@chain, $man, $missed, $last_child, $last_sc);
    for my $i ($start_idx .. $#CPathArr) {
        my ($s, $t) = @{ $CPathArr[$i] };
        unless (exists $bag{$s} && !exists $bag{$t}) {$missed = 1; next;}
        my $stance = $Cm{$s}{$t};
        unless (defined $stance) {$missed = 1; next;}
        if (defined $man) {
            paint_fr($man, @cur);
            unless ($Vis_fr[$stance] == $PaintId_fr && !grep {$_ == $stance} @cur) {$missed = 1; next;}
        }
        my @nb = grep {$_ != $s} @cur;
        my $j  = 0;
        ++$j while $j < @nb && $nb[$j] < $t;
        splice(@nb, $j, 0, $t);
        my %nbag  = map(($_, 1), @nb);
        my $child = _ck($s, \@nb);
        if (seen_has($child)) {$missed = 1; last;}
        if (is_bad($s, $t, \%nbag)) {set_bad($child); $missed = 1; last;}
        if (isbad($child))          {$missed = 1; last;}
        my $sc = $Value->($s, $t, \%nbag);
        push @chain, $child, [$sc];
        ($last_child, $last_sc) = ($child, $sc);
        @cur = @nb;
        %bag = %nbag;
        $man = $s;
    }
    return @chain if $missed || !defined $last_child || !%ToGoal;

    my @free = grep {!exists $bag{$_}} @Goal;
    return @chain unless @free;
    my $index = &max(map {$Priority[$_] // 0} @free);
    @free = grep {($Priority[$_] // 0) == $index} @free;
    my $first_attempt = 1;
GOAL: foreach my $g (@free) {
        my $tg = $ToGoal{$g} or next GOAL;
        push @chain, $last_child, [$last_sc] unless $first_attempt;
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
            unless ($Vis_fr[$stance] == $PaintId_fr && !grep {$_ == $stance} @dcur) {$ok = 0; last;}
            my @nb = grep {$_ != $s} @dcur;
            my $j  = 0;
            ++$j while $j < @nb && $nb[$j] < $t;
            splice(@nb, $j, 0, $t);
            my %nbag  = map(($_, 1), @nb);
            my $child = _ck($s, \@nb);
            if (seen_has($child)) {$ok = 0; last;}
            if (is_bad($s, $t, \%nbag)) {set_bad($child); $ok = 0; last;}
            if (isbad($child))          {$ok = 0; last;}
            my $sc = $Value->($s, $t, \%nbag);
            push @chain, $child, [$sc];
            @dcur = @nb;
            %dbag = %nbag;
            $dman = $s;
        }
        last GOAL if $ok;
    }
    return @chain;
}

my (@CComp, @CFloor, @CInC, @CorralCells, @CStamp, @CTouch, @Nb4, @Nb8);
my ($CGen, $CTag, $CTouchGen) = (0, 0, 0);

sub _corral_geom() {
    @CFloor = ();
    @Nb4    = ();
    @Nb8    = ();
    my $n = scalar @Maze;
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
    @CComp   = (0) x $n;
    @CInC    = (0) x $n;
    @CStamp  = (0) x $n;
    @CTouch  = (0) x $n;
    ($CGen, $CTag, $CTouchGen) = (0, 0, 0);
    return;
}

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
    my $btag   = $CTouchGen;

    my $active = 0;
    for my $p (@ccells)   {$active = 1, last if $Target[$p]}
    if (!$active) { for my $b (@$cboxes) {$active = 1, last unless $Target[$b]} }
    return undef unless $active;

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
        }
        last EXPAND unless defined $add;
        $used[$add] = 1;
        push @ccells, @{ $CorralCells[$add] };
        $CInC[$_] = $tag foreach @{ $CorralCells[$add] };
        $cboxes = _corral_boxes($pid, \@ccells);
        $btag   = $CTouchGen;
    }

    for my $b (@$cboxes) {
        foreach my $t (@{ $Cmk{$b} }) {
            next if $CTouch[$t] == $btag or $CInC[$t] == $tag;
            my $st = $Cm{$b}{$t};
            next unless defined $st;
            next if $CTouch[$st] == $btag or $CInC[$st] == $tag;
            return undef;
        }
    }

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
            next if $CTouch[$st] == $btag or $CInC[$st] == $tag;
            $allowed{$b} = 1 if $Vis[$st] == $pid;
        }
    }
    return %allowed ? \%allowed : undef;
}

sub corral_allowed($bag) {
    my $g   = ++$CGen;
    my $pid = $PaintId;

    my $nc = 0;
    @CorralCells = (undef);
    for my $p (@CFloor) {
        next if $Vis[$p] == $pid or $Blk[$p] == $pid or $CStamp[$p] == $g;
        my $c = ++$nc;
        my @s = ($p);
        $CStamp[$p] = $g;
        $CComp[$p]  = $c;
        for (my $i = 0; $i < @s; ++$i) {
            foreach my $t (@{ $Cg[ $s[$i] ] }) {
                next if $CStamp[$t] == $g or $Vis[$t] == $pid or $Blk[$t] == $pid;
                $CStamp[$t] = $g;
                $CComp[$t]  = $c;
                push @s, $t;
            }
        }
        $CorralCells[$c] = \@s;
    }
    return undef unless $nc;

    my @cand = (0) x ($nc + 1);
    foreach my $bx (@$bag) {
        foreach my $t (@{ $Cmk{$bx} }) {
            next if $Blk[$t] == $pid;
            my $st = $Cm{$bx}{$t};
            next unless defined $st and $Vis[$st] == $pid;
            next unless $CStamp[$t] == $g and $CComp[$t];
            $cand[ $CComp[$t] ] = 1;
        }
    }

    for my $c (1 .. $nc) {
        next unless $cand[$c];
        my $allowed = _corral_try($g, $pid, $c, $nc);
        return $allowed if defined $allowed;
    }
    return undef;
}


sub tahy($pozice) {
    my ($man, @baggage) = unpack($pu, $pozice);
    my ($s, $child, @tahy, @nomove, @children, %bags);
    my $skipped = 0;
    %bags = map(($_, 1), @baggage);
    paint($man, @baggage);
    @tahy = ();

    if (defined(my $cached = tahy_get($pozice))) {
        foreach my $ch (@$cached) {
            next if isbad($ch);
            my (undef, @nb) = unpack($pu, $ch);
            my %nbag = map(($_, 1), @nb);
            my ($t)  = grep {!exists $bags{$_}} @nb;
            my ($bx) = grep {!exists $nbag{$_}} @baggage;
            my $sc = $Value->($bx, $t, \%nbag);
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
        }
        if    (!@children)            {tahy_del($pozice)}
        elsif (@children != @$cached) {tahy_set($pozice, [@children])}
        return _tahy_macros($pozice, $man, \@baggage, \%bags, \@tahy);
    }

    my $vb = '';
    vec($vb, $_, 1) = 1 foreach @baggage;

    my $callow = corral_allowed(\@baggage);

    foreach my $bx (@baggage) {
        my $movable = 0;
        my $cskip   = $callow && !$callow->{$bx};

        delete $bags{$bx};
        vec($vb, $bx, 1) = 0;
        foreach my $t (@{ $Cmk{$bx}; }) {
            next if exists $bags{$t};
            $s = $Cm{$bx}{$t};
            next unless $Vis[$s] == $PaintId;
            ++$movable;
            next if $cskip;
            my @nb = grep($_ != $bx, @baggage);
            my $i  = 0;
            ++$i while $i < @nb && $nb[$i] < $t;
            splice(@nb, $i, 0, $t);

            $child = $CanonMap{ pack($pu, $bx, @nb) } //= canon_key($bx, \@nb);
            if (isbad($child)) {
                next;
            }

            if (seen_has($child)) {
                ++$skipped;
                push @children, $child;
                next;
            }
            $bags{$t} = 1;
            vec($vb, $t, 1) = 1;

            my $bad = is_bad($bx, $t, \%bags, $vb);
            if ($bad) {
                set_bad $child;
            }
            elsif ($Match_active && $Selective{$t} && matching_deadlock(@nb)) {

                set_bad $child;
            }
            else {
                if ($Feat_mode && exists $Cm{$t}{$bx} && $RegCells{$child}) {
                CELL: for my $c (@{ $RegCells{$child} }) {
                        for my $pair (@{ $StanceIdx{$c} // [] }) {
                            my ($ob, $ot) = @$pair;
                            next if $ob == $t;
                            next unless exists $bags{$ob};
                            next if exists $bags{$ot};
                            $ExplMark{$child} = 1;
                            last CELL;
                        }
                    }
                }
                my $sc = $Value->($bx, $t, \%bags);
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
                if (@chain) {
                    push @tahy,     $child, [$sc];
                    push @tahy,     @chain;
                    push @children, $child;
                }
                else {
                    push @tahy, $child, $sc;
                    push @children, $child;
                }
            }
            delete $bags{$t};
            vec($vb, $t, 1) = 0;
        }
        $bags{$bx} = 1;
        vec($vb, $bx, 1) = 1;
        push @nomove, $bx unless $movable;
    }
    if (@children) {
        tahy_set($pozice, [@children]);
    }

    my @frozen_set;
    if (@nomove) {
        my $frozen_bad;
        ($frozen_bad, @frozen_set) = is_frozen($man, @nomove);
        if ($frozen_bad) {
            set_bad $pozice;
            return ();
        }
        if (@frozen_set) {
            my @open = grep {!exists $bags{$_}} @Goal;
            if (@open) {

                for my $g (@open) {
                    if ($Vis_fr[$g] != $PaintId_fr) {
                        set_bad $pozice;
                        return ();
                    }
                }
            }
        }
    }

    if ($Walled_on) {
        my %wall = map(($_, 1), @frozen_set);
        while (1) {
            my $more = fix_diagonals(\%bags, \%wall);
            my $grew = 0;
            for my $c (keys %$more) {$grew = 1 unless $wall{$c}++}
            last unless $grew;
        }
        if (%wall) {

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
        }
    }
    return _tahy_macros($pozice, $man, \@baggage, \%bags, \@tahy, $skipped);
}

sub _tahy_macros($pozice, $man, $baggage, $bags, $tahy, $skipped = 0) {
    \my @baggage = $baggage;
    \my %bags    = $bags;
    \my @tahy    = $tahy;

    if ($Has_routes) {
        my @open = grep {!$bags{$_}} @Goal;
        for my $bx (@baggage) {
            my $rb = $RouteMoves->{$bx} or next;
            for my $g (@open) {
                my $moves = $rb->{$g} or next;
                next unless @$moves >= 2;
                my $first = $moves->[0];
                next if $bags{$first};
                my $st1 = $Cm{$bx}{$first};
                next unless defined $st1 && $Vis[$st1] == $PaintId;
                my @chain = _route_deliver(\@baggage, $bx, $moves, $RouteMust->{$bx}{$g}) or next;
                push @tahy, @chain;
            }
        }
    }

    if ($Has_cp && $CP_mode_ok) {
        for my $bx (@baggage) {
            my $row = $CPathIdx{$bx} or next;
            for my $t (keys %$row) {
                next if exists $bags{$t};
                my $st = $Cm{$bx}{$t};
                next unless defined $st && $Vis[$st] == $PaintId;

                my @ride = _cp_deliver(\@baggage, $row->{$t}) or next;
                $ride[-1] = $ride[-1][0];
                push @tahy, @ride;
            }
        }
    }

    if (@tahy) {
        return @tahy;
    }
    elsif ($skipped) {

        return ();
    }
    else {
        set_bad $pozice;
        return ();
    }
}

sub initvars_score($mode) {

    $CP_mode_ok = $mode eq 'MOVE_SUM' ? 0 : 1;

    if ($Feat_mode) {

        $MaxP     = $Game{'maxp_steps'}   // $Game{'maxp_push'};
        $MaxVal   = $Game{'maxval_steps'} // $Game{'maxval_push'};
        $Distance = &dclone($Game{'steps_quad'} // $Game{'zbytek'});
        $Value    = \&value_score;
    }
    elsif ($mode eq 'PUSH_ASSIGN') {

        $DistRaw = raw_table($Game{'steps'} // $Game{'zbytek_raw'});
        $Value   = \&value_assign;
    }
    elsif ($mode eq 'MOVE_SUM') {

        $DistRaw = raw_table($Game{'distance_raw'} // $Game{'distance'});
        $Value   = \&value_move_sum;
    }
    elsif ($mode eq 'ROUTE') {

        $Value = \&value_route;
    }
    elsif ($mode eq 'FLOW') {

        $DistRaw = raw_table($Game{'steps'} // $Game{'zbytek_raw'});
        $Value   = \&value_flow;
    }
    else {
        if ($mode eq 'MOVE_SCORE') {

            $MaxP     = $Game{'maxp'};
            $MaxVal   = $Game{'maxval'};
            $Distance = &dclone($Game{'distance_quad'} // $Game{'distance'});
        }
        else {
            $MaxP     = $Game{'maxp_steps'}   // $Game{'maxp_push'};
            $MaxVal   = $Game{'maxval_steps'} // $Game{'maxval_push'};
            $Distance = &dclone($Game{'steps_quad'} // $Game{'zbytek'});
        }
        $Value = \&value_score;
    }

    $RouteBonus = defined $MaxP ? int sqrt($MaxP) : 0;
    $Route      = $Game{'route'} // {};

    $RouteMoves = {};
    $RouteMust  = {};
    {
        my $rt = $Game{'routes'} // {};
        foreach my $bx (keys %$rt) {
            my $row = $rt->{$bx};
            foreach my $g (keys %$row) {
                my $r = $row->{$g};
                if (ref $r eq 'ARRAY') {
                    $RouteMoves->{$bx}{$g} = [unpack 'n*', $r->[0]];
                    $RouteMust->{$bx}{$g}  = {map(($_, 1), unpack 'n*', $r->[1])};
                }
                else {
                    $RouteMoves->{$bx}{$g} = $r->{'moves'};
                    $RouteMust->{$bx}{$g}  = $r->{'must_empty'};
                }
            }
        }
    }
    $Has_routes = %$RouteMoves ? 1 : 0;

    $Has_cp = $Game{'has_cp'} // $Game{'has_common_path'} // 0;
    %CPath  = ();
    if ($Has_cp) {

        my $cp_arr = $Game{'c_path'};
        for my $j (0 .. $#$cp_arr) {
            my ($bx, $t) = @{ $cp_arr->[$j] };
            $CPath{$bx}{$t} = 1;
        }
    }

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

    if ($Feat_mode) {
        @FloorCells = grep {defined $Cg[$_]} 0 .. $#Cg;
        @Vis_ci     = (0) x scalar @Maze;
        $PaintId_ci = 0;
    }

    %ReachG    = ();
    %Selective = ();
    {
        my $zr = $Game{'steps'} // $Game{'zbytek_raw'} // {};
        for my $c (keys %$zr) {
            my $row = $zr->{$c};
            for my $g (keys %$row) {
                my $v = $row->{$g};
                $ReachG{$c}{$g} = 1 if defined $v && $v ne 'Inf';
            }
        }
        $ReachG{$_}{$_} = 1 foreach @Goal;
        my $ng         = scalar @Goal;
        my $has_ng_sel = 0;
        for my $c (keys %ReachG) {
            next unless keys %{ $ReachG{$c} } < $ng;
            $Selective{$c} = 1;
            $has_ng_sel = 1 unless $Target[$c];
        }
        $Match_active = $has_ng_sel;
    }

    %Rev       = ();
    %ReachW    = ();
    $Walled_on = @Goal ? 1 : 0;
    for my $c (keys %Cmk) {
        push @{ $Rev{$_} }, $c foreach @{ $Cmk{$c} };
    }
}



sub solve_forward($limit, $mode) {
    my $gameid = $Gameid;
    my ($pozice, $nopen, $MaxOpen, $counter, $timer, $cas, $tick, $elapsed, $doba, $reason, $path, $plen, $steps, $bc, $ending);
    discover($Start, '');
    if ($Feat_mode) {
        my $key = feat_key($Start);
        %FCellQ   = ($key => 'Games::Sokoban::Solver::Heap'->new);
        @FCellKey = ($key);
        $FCellPtr = 0;
        $FCellQ{$key}->add($Start, 0);
    }
    else { $Pex->add($Start, 0) }
    $nopen   = 1;
    $MaxOpen = 1;
    $bc      = 0;
    $counter = 0;
    $reason  = 'UNSOLVABLE';
    $cas     = time();
    $tick    = $cas;
    $timer   = [&gettimeofday()];
LMAIN: while ($nopen) {

        my $pweight = 0;
        if ($Feat_mode) {

            my $n = @FCellKey;
            my $i = 0;
            ++$i while $i < $n && !$FCellQ{ $FCellKey[ ($FCellPtr + $i) % $n ] }->size;
            confess "\nFEATURE: $nopen positions open but every cell is empty" if $i == $n;
            my $j = ($FCellPtr + $i) % $n;
            $FCellPtr = ($j + 1) % $n;
            my $Q    = $FCellQ{ $FCellKey[$j] };
            my $node = $Q->[0];
            $pweight = $node->[0] if ref $node;
            $pozice  = $Q->next;
        }
        else {
            $pozice = $Pex->next;
        }
        --$nopen;

        if (isbad($pozice)) {
            next;
        }
        confess "\nNO PARENT FOR POSITION!" unless seen_has($pozice);
        my (@tahy) = tahy($pozice);

        my ($fb_odo, $fb_isl, $fb_room, $fb_out);
        ($fb_odo, $fb_isl, $fb_room, $fb_out) = feat_counts($pozice)
            if $Feat_mode;

        my $chain_parent = $pozice;
        my $broken       = 0;
        my @fkids;
        foreach my ($child, $score)(@tahy) {
            ++$bc;
            my $start = ref $score;
            my $real  = $start ? $score->[0] : $score;
            my $ends  = (defined $real && !$start) ? 1 : 0;
            if (isbad($child)) {
                $broken       = $ends ? 0 : 1;
                $chain_parent = $pozice;
                next;
            }
            if (seen_has($child)) {
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
            discover($child, $chain_parent);

            if (   (defined $SolvedLay ? substr($child, $ManOff) eq $SolvedLay : _lay_solved($child))
                || exists $SolsC{$child})
            {
                $Bestbet = $child;
                last LMAIN;
            }
            if (defined $real) {
                if ($Feat_mode) {

                    push @fkids, [$child, feat_counts($child), ($ExplMark{$child} ? 1 : 0), 0, $real];
                    $chain_parent = $start ? $child : $pozice;
                    next;
                }
                $Pex->add($child, $real);
                ++$nopen;
                $MaxOpen      = $nopen if $nopen > $MaxOpen;
                $chain_parent = $start ? $child : $pozice;
            }
            else {
                $chain_parent = $child;
            }
        }

        if (@fkids) {
            feat_advise(\@fkids, $fb_odo, $fb_isl, $fb_room, $fb_out);
            for my $k (@fkids) {
                my $key = join ',', @$k[ 1 .. 4 ];
                my $cq  = $FCellQ{$key};
                unless ($cq) {
                    $cq = $FCellQ{$key} = 'Games::Sokoban::Solver::Heap'->new;
                    push @FCellKey, $key;
                }
                my $sc = $k->[7];
                $cq->add($k->[0],
                    int($pweight) + ($k->[6] ? 0 : 1)
                        + 0.5 + $sc / (2 * (abs($sc) + ($MaxVal || 1000))));
                ++$nopen;
                $MaxOpen = $nopen if $nopen > $MaxOpen;
            }
        }
    }
    continue {
        unless (++$counter % 100) {
            $doba = tv_interval($timer);
            if ($limit and $doba > $limit) {$reason = 'TIMEOUT'; last LMAIN}
            $elapsed = time();
            if ($elapsed != $tick) {
                $tick = $elapsed;
                if (race_lost()) {$reason = 'IGNORE'; last LMAIN}
                if ($elapsed - $cas >= $SCREEN) {
                    $cas = $elapsed;
                    $QUIET or backline(
                        sprintf '%-11s %8d ... %12d %9d  %s  %12.2f %12.0f %12.0f',
                        $mode, $gameid, $counter, $nopen, podil($nopen, $MaxOpen),
                        $doba,
                        $bc / $doba,
                        $counter / $doba
                    );
                    if (mem_over()) {$reason = 'MEMCAP'; last LMAIN}
                }
            }
        }
    }
    $path  = undef;
    $doba  = clamp_doba(tv_interval($timer));
    $plen  = undef;
    $steps = 0;
    if ($Bestbet) {
        $path = get_path($Bestbet);
        if (my $sc = $SolsC{$Bestbet}) {
            my ($M, $T) = @$sc;
            my (undef, @bb) = unpack($pu, $Bestbet);
            my %bb   = map(($_, 1), @bb);
            my $par  = parent_get($Bestbet);
            my $cell = (defined $par && length $par)
                ? (grep {!exists $bb{$_}} (unpack($pu, $par))[ 1 .. $Nbox ])[0]
                : $Game{'player'};
            $path .= ($cell == $M ? '' : cesta($cell, $M, \@bb)) . $T;
        }
        $path = rebuilt_path($path);
        replay_check($path);
        $plen   = length($path);
        $steps  = $path =~ tr/UDRL//;
        $reason = 'SOLVED';
    }
    my $qsize = 0;
    if   ($Feat_mode) { $qsize += $_->size for values %FCellQ }
    else              { $qsize = $Pex->size }
    $ending = sprintf $ENDING,
        $mode, $gameid, $Game{'nbox'}, $Game{'ncell'}, $reason, $plen // $limit, $steps, $doba,
        sprintf('%.0f', $bc / $doba), sprintf('%.0f', $counter / $doba),
        $MaxOpen,
        $qsize, $Nseen;
    barva($reason,$ending);
    state_close(($reason eq 'SOLVED') ? 1 : 0);
    my $nseen = $Nseen;
    return ($reason, $path, $doba, $nseen);
}



my (%OSeen, $OTimer, $ODeadline, $OTimeUp, $ONseen, $ONmacro, $Otick);
my ($ORaceUp, $OMemUp, $ORaceNext, $OMemNext);
my $ORDER_NUDGE_CAP = 8;

sub order_alive($open, $boxes, $locked) {
    my %parked = %$locked;
    my (%vis, @q);
    for my $b (grep {!exists $parked{$_}} @$boxes) {
        push @q, $b unless $vis{$b}++;
    }
    while (defined(my $c = shift @q)) {
        foreach my $t (@{ $Cmk{$c}; }) {
            next if exists $vis{$t} || exists $parked{$t};
            next if exists $parked{ $Cm{$c}{$t} };
            $vis{$t} = 1;
            push @q, $t;
        }
    }
    exists $vis{$_} or return 0 foreach @$open;
    return 1;
}

sub order_push_path($man, $bx, $goal, $boxes, $nseen_ref, $block = undef) {
    my @others = grep {$_ != $bx} @$boxes;
    my %obag   = map(($_, 1), @others);
    my (%seenst, %prevst, @queue);
    paint($man, $bx, @others);
    my $rm;
    for my $c (0 .. $#Vis) { if ($Vis[$c] == $PaintId) { $rm = $c; last } }
    confess 'EMPTY PLAYER REGION' unless defined $rm;
    my $key0 = $bx . ',' . $rm;
    $seenst{$key0} = 1;
    push @queue, [$bx, $man, $key0];
    while (my $st = shift @queue) {
        my ($b, $p, $key) = @$st;

        unless (++$$nseen_ref % 500) {
            if (time() - $Otick > 6) {
                $Otick = time();
                my $doba = tv_interval($OTimer);
                $QUIET or backline(
                    sprintf '%-11s %8d ... %12d %9d %6d %12.2f %12.0f',
                    'ORDER',  $Gameid, $ONseen, scalar %OSeen,
                    $ONmacro, $doba,   $ONseen / $doba
                );
            }
        }

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

            paint($b, $t, @others);
            my $rm2;
            for my $c (0 .. $#Vis) { if ($Vis[$c] == $PaintId) { $rm2 = $c; last } }
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
        }
    }
    return undef;
}

sub odfs($pos, $man, $boxes, $depth, $nnudge, $locked) {
    my %bags = map(($_, 1), @$boxes);
    my @open = grep {!exists $bags{$_}} @Goal;
    return $pos unless @open;
    my $ot = tv_interval($OTimer);
    if ($ODeadline and $ot > $ODeadline) {$OTimeUp = 1; return undef}
    if ($ot > $ORaceNext) {
        $ORaceNext = $ot + 1;
        if (race_lost()) {$ORaceUp = 1; $OTimeUp = 1; return undef}
    }
    if ($ot > $OMemNext) {
        $OMemNext = $ot + $SCREEN;
        if (mem_over()) {$OMemUp = 1; $OTimeUp = 1; return undef}
    }
    return undef if $depth > 5000;

    return undef unless order_alive(\@open, $boxes, $locked);
    my $zr      = $Game{'steps'} // $Game{'zbytek_raw'};
    my @movable = grep {!exists $locked->{$_}} @$boxes;

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

    my %block;
    my $toprank = $Priority[ $goals[0] ] // 0;
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
    goto LOWER if $nnudge >= $ORDER_NUDGE_CAP;

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
    }

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
}

sub order_commit($pos, $boxes, $macro, $depth, $nnudge, $locked, $lockcell) {
    my $moved = $macro->[0][0];
    my ($from, $to) = @{ $macro->[-1] };
    my @nb = grep {$_ != $moved} @$boxes;
    my $i  = 0;
    ++$i while $i < @nb && $nb[$i] < $to;
    splice(@nb, $i, 0, $to);
    my $cpos = pack($pu, $from, @nb);
    return undef if $OSeen{$cpos}++;
    ++$ONmacro if @$macro > 1;
    my @cur = @$boxes;

    for my $step (@$macro) {
        my ($f, $t) = @$step;
        my @nx = grep {$_ != $f} @cur;
        my $j  = 0;
        ++$j while $j < @nx && $nx[$j] < $t;
        splice(@nx, $j, 0, $t);
        my $child = pack($pu, $f, @nx);

        discover($child, $pos) unless seen_has($child);
        $pos = $child;
        @cur = @nx;
    }
    $locked = { %$locked, $lockcell, 1 } if defined $lockcell;
    return odfs($pos, $from, \@nb, $depth + 1, $nnudge, $locked);
}

sub solve_order($limit) {
    my $timer = [&gettimeofday()];
    ($OTimer, $ODeadline, $OTimeUp) = ($timer, $limit, 0);
    ($ORaceUp, $OMemUp, $ORaceNext, $OMemNext) = (0, 0, 1, $SCREEN);
    ($ONseen, $ONmacro, $Otick)     = (0, 0, time());
    %OSeen = ($Start, 1);
    discover($Start, '');
    my ($man, @boxes) = unpack($pu, $Start);

    my $final  = odfs($Start, $man, \@boxes, 0, 0, {});
    my $reason = defined $final ? 'SOLVED' : $ORaceUp ? 'IGNORE' : $OMemUp ? 'MEMCAP' : $OTimeUp ? 'TIMEOUT' : 'GIVEUP';
    my $doba   = clamp_doba(tv_interval($timer));
    my ($path, $sollen, $steps) = ('', 0, 0);
    if ($reason eq 'SOLVED') {
        $path = get_path($final);
        my $tail = $Sols{$final};
        $path  .= $tail if defined $tail && $tail =~ /[A-Za-z]/;
        $path = rebuilt_path($path);
        replay_check($path);
        $sollen = length($path);
        $steps  = $path =~ tr/DLRU//;
    }
    my $ending = sprintf $ENDING,
        'ORDER', $Gameid, $Game{'nbox'}, $Game{'ncell'}, $reason, $sollen || $limit,
        $steps, $doba, q{}, q{}, q{}, $ONmacro, $ONseen;
    barva($reason,$ending);
    %OSeen = ();
    state_close($reason eq 'SOLVED' ? 1 : 0);
    return ($reason, $path, $doba, $ONseen);
}



my (%Pull, %PullMan, $StartBoxKey);
my (@IsStart, @PullTo, $Far);

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
                $Far   = $d[$t] if $d[$t] > $Far;
                push @q, $t;
            }
        }
        $PullTo[$s] = \@d;
    }
    ++$Far;
}

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
}

sub build_tail($key) {
    my @tail;
    while (length(my $v = bseen_get($key))) {
        push @tail, [unpack('nn', $v)];
        $key = substr($v, 4);
    }
    return \@tail;
}

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
}

sub initvars_backward() {
    $StartBoxKey = pack($pu, sort {$a <=> $b} @Baggage);
    build_pull();
    build_pull_to();
}

sub solve_backward($limit) {
    my $timer = [&gettimeofday()];
    my $cas   = time();
    my $tick  = $cas;
    $BackN    = 0;
    my @goals  = sort {$a <=> $b} @Goal;
    my %Q;
    my $Hq     = 'Games::Sokoban::Solver::Heap'->new;
    my $found;
    my $reason = 'UNSOLVABLE';

    my ($bc, $nopen, $MaxOpen, $hbest) = (0, 0, 0, ~0);
    for my $m (solved_regions()) {
        my $pos = pack($pu, $m, @goals);
        next if bseen_has($pos);
        bseen_set($pos, '');
        if (pack($pu, @goals) eq $StartBoxKey) {
            paint_fr($m, @goals);
            if ($Vis_fr[ $Game{'player'} ] == $PaintId_fr) {$found = $pos; last}
        }
        my $h = 0;
        if (my @off = grep {!$IsStart[$_]} @goals) {
            for my $s (grep {!$Target[$_]} @Baggage) {
                my $row = $PullTo[$s];
                $h += $row->[$_] // $Far for @off;
            }
        }
        $hbest = $h if $h < $hbest;
        push @{ $Q{$h} //= do {$Hq->add($h, $h); []} }, $pos;
        ++$nopen;
    }
    $MaxOpen = $nopen;
    my $counter = 0;
    while (!defined $found && $nopen) {
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
                next if bseen_has($npos);
                bseen_set($npos, pack('nn', $b, $c) . $pos);

                if (pack($pu, @nb) eq $StartBoxKey) {
                    paint_fr($ma, @nb);
                    if ($Vis_fr[ $Game{'player'} ] == $PaintId_fr) {$found = $npos; last GEN}
                }

                my $h = 0;
                if (my @off = grep {!$IsStart[$_]} @nb) {
                    for my $s (@Baggage) {
                        next if $s == $b or $s != $c && exists $bag{$s};
                        my $row = $PullTo[$s];
                        $h += $row->[$_] // $Far for @off;
                    }
                }
                $hbest = $h if $h < $hbest;
                push @{ $Q{$h} //= do {$Hq->add($h, $h); []} }, $npos;
                ++$nopen;
                $MaxOpen = $nopen if $nopen > $MaxOpen;
            }
        }
        unless (++$counter % 200) {
            my $doba = tv_interval($timer);
            if ($limit and $doba > $limit) {$reason = 'TIMEOUT'; last}
            my $now = time();
            if ($now != $tick) {
                $tick = $now;
                if (race_lost()) {$reason = 'IGNORE'; last}
                if ($now - $cas >= $SCREEN) {
                    $cas = $now;
                    $QUIET or backline(
                        sprintf '%-11s %8d ... %12d %9d  %s  %6d %12.2f %12.0f %12.0f',
                        'BACKWARD', $Gameid, $counter, $nopen, podil($nopen, $MaxOpen),
                        $hbest,     $doba,
                        $bc / $doba,
                        $counter / $doba
                    );
                    if (mem_over()) {$reason = 'MEMCAP'; last}
                }
            }
        }
    }
    my $doba = clamp_doba(tv_interval($timer));
    my ($path, $sollen, $steps) = ('', 0, 0);
    if (defined $found) {
        $path   = rebuilt_path(stitch_tail($Start, build_tail($found)));
        replay_check($path);
        $reason = 'SOLVED';
        $sollen = length($path);
        $steps  = $path =~ tr/DLRU//;
    }

    my $rate_div = $doba || 1;
    my $ending   = sprintf $ENDING,
        'BACKWARD', $Gameid, $Game{'nbox'}, $Game{'ncell'}, $reason, $sollen || $limit, $steps, $doba,
        sprintf('%.0f', $bc / $rate_div), sprintf('%.0f', $counter / $rate_div),
        $MaxOpen,
        $nopen, $BackN;
    barva($reason,$ending);
    state_close($reason eq 'SOLVED' ? 1 : 0);
    my $nseen = $BackN;
    return ($reason, $path, $doba, $nseen);
}



my (%ConvCP, @ConvCR, %ConvTG);

sub _conv_boxes($pos) { my (undef, @b) = unpack($pu, $pos); return @b; }

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
        @heap = sort { $seen{$a} <=> $seen{$b} } @heap;
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
            if ($t == $goal) { $bestlen = $sl; $best = $c; $seen{$c} = $sl; $parent{$c} = $p; next; }
            next if exists $seen{$c} && $sl >= $seen{$c};
            $seen{$c}   = $sl;
            $parent{$c} = $p;
            push @heap, $c;
        }
    }
    return ({}, []) unless defined $best;
    my @u = ($best);
    my $p = $best;
    while ($p = $parent{$p}) { unshift @u, $p; }
    my (%st, @route);
    for my $pos (@u) { my ($man, $bag) = unpack('n*', $pos); ++$st{$man}{$bag}; push @route, [$man, $bag]; }
    return (\%st, \@route);
}

sub _conv_route_to_goal($man, $box, $g, $blocked) {
    my %bag = map { ($_, 1) } @$blocked;
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
        my $r = _conv_walk($m, { %bag, $bx => 1 });
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
            if ($t == $g) { $bestlen = $sl; $best = $c; next; }
            push @heap, $c;
        }
    }
    return () unless defined $best;
    my @u = ([unpack('n*', $best)]);
    my $p = $best;
    while ($p = $parent{$p}) { unshift @u, [unpack('n*', $p)]; }
    shift @u;
    return @u;
}

sub build_conveyor() {
    %ConvCP = ();
    @ConvCR = ();
    %ConvTG = ();

    my (%common, %routes);
    my $nvalid = 0;
    for my $bx (@Baggage) {
        for my $g (@Goal) {
            next if $bx == $g;
            my ($pc, $route) = _conv_route_cp($bx, $g);
            next unless @$route;
            ++$nvalid;
            for my $s (keys %$pc) { for my $t (keys %{ $pc->{$s} }) { $common{$s}{$t} += $pc->{$s}{$t}; } }
            $routes{$bx}{$g} = $route;
        }
    }
    my $req = $nvalid;
    my %gh = map { ($_, 1) } @Goal;
    my %cp_count;
    for my $bx (keys %common) {
        my $th = $common{$bx};
        while (my ($t, $v) = each %$th) {

            next if $gh{$t};
            $cp_count{$bx}{$t} = 1 if $v == $req;
        }
    }
    for my $bx (keys %routes) {
        my $th = $routes{$bx};
        while (my ($g, $v) = each %$th) {
            for my $x (@$v) { my ($s, $t) = @$x; push @$x, (exists $cp_count{$s}{$t} ? 1 : 0); }
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
                    if ($common{ $s->[0] }{ $s->[1] } != $idx) { %ConvCP = (); return; }
                    ++$idx;
                }
            }
        }
    }
    unless (%common) { %ConvCP = (); return; }
    for my $bx (keys %common) { while (my ($t, $i) = each %{ $common{$bx} }) { $ConvCR[$i] = [$bx, $t]; } }
    unless (@ConvCR && defined $ConvCR[-1]) { %ConvCP = (); @ConvCR = (); return; }
    %ConvCP = %common;

    my ($man, $box) = @{ $ConvCR[-1] };
    my @ng = sort { ($Priority[$b] // 0) <=> ($Priority[$a] // 0) } @Goal;
    my $g = shift @ng;
    my (@blk, %tg);
    my $found = 0;
    my @p = _conv_route_to_goal($man, $box, $g, \@blk);
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
}

sub conv_moves($pos) {
    my ($man, @boxes) = unpack($pu, $pos);
    my %bag = map { ($_, 1) } @boxes;
    paint($man, @boxes);
    my @moves;
    for my $bx (@boxes) {
        for my $t (@{ $Cmk{$bx} // [] }) {
            next if $bag{$t};
            my $s = $Cm{$bx}{$t};
            next unless $Vis[$s] == $PaintId;
            my %tbag = map { ($_, 1) } ($t, grep { $_ != $bx } @boxes);
            next if is_bad($bx, $t, \%tbag);
            push @moves, [$bx, $t];
        }
    }
    return @moves;
}

sub conv_to_goal($pos, $box, $tg) {
    my ($man, @boxes) = unpack($pu, $pos);
    for my $mv (@$tg) {
        paint($man, @boxes);
        my %bag = map { ($_, 1) } @boxes;
        my ($m, $bx) = @$mv;
        my $player = $Cm{$m}{$bx};
        return 0 unless defined $player && $Vis[$player] == $PaintId;
        return 0 if $bag{$bx};
        my @nb    = sort { $a <=> $b } map { $_ == $box ? $bx : $_ } @boxes;
        my $child = pack($pu, $box, @nb);
        my %nbag  = map { ($_, 1) } @nb;
        if (is_bad($box, $bx, \%nbag)) { set_bad($child); return 0; }
        return 0 if isbad($child);
        return 0 if seen_has($child);
        discover($child, $pos);
        if (exists $Sols{$child}) { $Bestbet = $child; return 1; }
        $Pex->add($child, value_score($box, $bx, \%nbag));
        $man = $m; $box = $bx; @boxes = @nb; $pos = $child;
    }
    return 1;
}

sub conv_to_end($pos, $source, $target) {
    my $start_idx = $ConvCP{$source}{$target};
    return unless defined $start_idx;
    my ($man, @boxes) = unpack($pu, $pos);
    my %bag = map { ($_, 1) } @boxes;
    return unless $bag{$source};
    my $parent = $pos;
    my ($last_added, $last_box);
    my %to_add = map { ($_, 1) } ($start_idx .. $#ConvCR);
    for my $i ($start_idx .. $#ConvCR) {
        my ($cs, $ct) = @{ $ConvCR[$i] };
        next unless $bag{$cs};
        next if $bag{$ct};
        my $player = $Cm{$cs}{$ct};
        next unless defined $player;
        paint($man, @boxes);
        next unless $Vis[$player] == $PaintId;
        my @nb    = sort { $a <=> $b } map { $_ == $cs ? $ct : $_ } @boxes;
        my $child = pack($pu, $cs, @nb);
        my %nbag  = map { ($_, 1) } @nb;
        if (is_bad($cs, $ct, \%nbag)) { set_bad($child); last; }
        last if isbad($child);
        last if seen_has($child);
        discover($child, $parent);
        delete $to_add{$i};
        $last_added = $child;
        $last_box   = $ct;
        $Pex->add($child, value_score($cs, $ct, \%nbag));
        $parent = $child;
        $man    = $cs;
        @boxes  = @nb;
        %bag    = %nbag;
    }
    return if %to_add;
    return unless defined $last_added;
    ($man, @boxes) = unpack($pu, $last_added);
    %bag = map { ($_, 1) } @boxes;
    my @free = grep { !$bag{$_} } @Goal;
    return unless @free;
    my $index = &max(map { $Priority[$_] // 0 } @free);
    @free = grep { ($Priority[$_] // 0) == $index } @free;
    for my $g (@free) {
        next unless exists $ConvTG{$g};
        last if conv_to_goal($last_added, $last_box, $ConvTG{$g});
    }
    return;
}

sub solve_conveyor($limit) {
    my $timer = [&gettimeofday()];
    $Bestbet = undef;
    build_conveyor();

    unless (@ConvCR) {
        my $doba = clamp_doba(tv_interval($timer));
        backlinen(sprintf '%-12s %5d %3d %4d %-10s', 'CONVEYOR', $Gameid, $Game{'nbox'}, $Game{'ncell'}, 'NOCP')
            if $QUIET < 2;
        state_close(0);
        return ('NOCP', '', $doba, 0);
    }
    discover($Start, '');
    $Pex->add($Start, 0);
    my $nseen   = 1;
    my $counter = 0;
    my $reason  = 'GIVEUP';
    my ($CRaceNext, $CMemNext) = (1, $SCREEN);
    while ($Pex->size) {
        my $pozice = $Pex->next;
        next if isbad($pozice);
        unless (++$counter % 200) {
            my $ot = tv_interval($timer);
            if ($limit and $ot > $limit) { $reason = 'TIMEOUT'; last; }
            if ($ot > $CRaceNext) {
                $CRaceNext = $ot + 1;
                if (race_lost()) { $reason = 'IGNORE'; last; }
            }
            if ($ot > $CMemNext) {
                $CMemNext = $ot + $SCREEN;
                if (mem_over()) { $reason = 'MEMCAP'; last; }
            }
        }
        my @boxes = _conv_boxes($pozice);
        for my $mv (conv_moves($pozice)) {
            my ($src, $tgt) = @$mv;
            my @nb    = sort { $a <=> $b } map { $_ == $src ? $tgt : $_ } @boxes;
            my $child = pack($pu, $src, @nb);
            next if isbad($child);
            if (exists $Sols{$child}) {
                discover($child, $pozice) unless seen_has($child);
                $Bestbet = $child;
                last;
            }
            next if seen_has($child);
            ++$nseen;
            if (exists $ConvCP{$src}{$tgt}) {
                conv_to_end($pozice, $src, $tgt);
                last if $Bestbet;
            }
            next if isbad($child) || seen_has($child);
            discover($child, $pozice);
            my %tbag = map { ($_, 1) } @nb;
            $Pex->add($child, value_score($src, $tgt, \%tbag));
        }
        last if $Bestbet;
    }
    my ($path, $sollen, $steps) = ('', 0, 0);
    if ($Bestbet) {
        $reason = 'SOLVED';
        $path   = get_path($Bestbet);
        my $tail = $Sols{$Bestbet};
        $path   .= $tail if defined $tail && $tail =~ /[A-Za-z]/;
        $path   = rebuilt_path($path);
        replay_check($path);
        $sollen = length $path;
        $steps  = $path =~ tr/DLRU//;
    }
    my $doba   = clamp_doba(tv_interval($timer));
    my $ending = sprintf $ENDING,
        'CONVEYOR', $Gameid, $Game{'nbox'}, $Game{'ncell'}, $reason, $sollen || $limit, $steps, $doba,
        q{}, q{}, q{}, q{}, $nseen;
    barva($reason,$ending);
    state_close($reason eq 'SOLVED' ? 1 : 0);
    return ($reason, $path, $doba, $nseen);
}


sub plan_odometer($boxes) {
    my %has = map {($_, 1)} @$boxes;
    my $init = grep {$has{$_}} @PlanInit;
    return $init if $init < @PlanInit;
    my $v = scalar @PlanInit;
    for my $w (@PlanWaves) {
        my $occ = grep {$has{$_}} @$w;
        $v += $occ;
        last if $occ < @$w;
    }
    return $v;
}

sub _plan_push_bfs($c, $blk) {
    my (%seen, @q);
    for my $s (@Baggage) {
        next if $blk->{$s};
        for my $t (@{ $Cmk{$s} // [] }) {
            next if $blk->{$t};
            my $stance = $Cm{$s}{$t};
            next if !defined $stance || $blk->{$stance};
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
            next if !defined $stance || $blk->{$stance} || $Vis[$stance] != $PaintId;
            return 1 if $t == $c;
            my $key = pack('nn', $t, $p);
            next if $seen{$key}++;
            push @q, [$t, $p];
        }
    }
    return 0;
}

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
    }
    return (\%hit, \%par, \%man);
}

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
    @PlanPair     = ();
    @PlanInit     = ();
    @PlanWaves    = ();
    $Plan_waves   = 0;
    return unless @Goal == $Nbox;
    build_pull();

    my %box  = map(($_, 1), @Goal);
    my %base = map(($_, 1), @Baggage);
    my $cur;

    for my $g (sort {$a <=> $b} grep {$base{$_}} keys %box) {
        push @PlanPair, [$g, $g, 0, [], undef];
        delete $box{$g};
        delete $base{$g};
    }

    my $NOEDGE = 100_000_000;
    my $DUMMY  = 1_000_000;

    while (%box) {
        ++$Plan_waves;

        my (@cand, %ptree, %mantab, %hits);
        for my $c (sort {$a <=> $b} keys %box) {
            my $blk = {%box};
            delete $blk->{$c};
            my ($hit, $par, $man) = _plan_bfs($c, $blk, $cur, \%base);
            next unless %$hit;

            next unless _plan_push_bfs($c, $blk);
            push @cand, $c;
            ($hits{$c}, $ptree{$c}, $mantab{$c}) = ($hit, $par, $man);
        }
        last unless @cand;

        my @bases = sort {$a <=> $b} keys %base;
        my $n     = @cand > @bases ? scalar @cand : scalar @bases;
        my @mx;
        for my $i (0 .. $n - 1) {
            my $c = $cand[$i];
            push @mx, [map {
                my $b = $bases[$_];
                (defined $c && defined $b) ? ($hits{$c}{$b} ? $hits{$c}{$b}[0] : $NOEDGE) : $DUMMY
            } 0 .. $n - 1];
        }
        my @out;
        Games::Sokoban::Solver::Munkres::assign(\@mx, \@out);
        my @todo;
        for my $i (0 .. $#cand) {
            my $b = $bases[ $out[$i] ] // next;
            my $e = $hits{ $cand[$i] }{$b} or next;
            push @todo, [$cand[$i], $b, @$e];
        }

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
        }
        last unless $done;
    }
    @PlanInit = map {$_->[0]} grep {$_->[2] == 0} @PlanPair;
    my %bywave;
    push @{ $bywave{ $_->[2] } }, $_->[0] for grep {$_->[2] > 0} @PlanPair;
    @PlanWaves = map {$bywave{$_}} sort {$b <=> $a} keys %bywave;
    return;
}


sub initvars($gameid, $gm, $mode = 'PUSH_SCORE') {
    initvars_common($gameid, $gm, $mode);
    if ($Feat_mode) {
        build_plan();
        build_planneed();
    }
    else { @PlanNeed = () }
    if   ($mode eq 'BACKWARD') { initvars_backward() }
    else                       { initvars_score($mode) }
}

sub solve($gameid, $gm, $limit, $mode = 'PUSH_SCORE') {
    initvars($gameid, $gm, $mode);
    return solve_backward($limit) if $mode eq 'BACKWARD';
    return solve_order($limit)    if $mode eq 'ORDER';
    return solve_conveyor($limit) if $mode eq 'CONVEYOR';
    return solve_forward($limit, $mode);
}


1;
