package Games::Sokoban::Solver::Parser;

# THE LEVEL ANALYSIS THE ENGINES SEARCH ON.
#
# One pass from the record Games::Sokoban::Solver::Code::prepare returns to the
# complete %Game the engines take: the push graph (%Cm: box cell -> target cell
# -> the cell the player pushes from; %Cmk: box cell -> [targets]) pruned to
# what a box can ever reach, the deadlock patterns of every push (the ones dead
# by themselves removed, the bloks of the rest -- see Games::Sokoban::Solver::
# Finder), the wall / corridor / hole deadlock tables, the goal-fill order (two
# ranking algorithms compete, the deeper wins), the terminal positions %sols,
# the single-box routes from every cell to every goal with the raw and the
# quadratized distance tables, the common path of a conveyor level and its
# delivery macros, and the pack template of a position.
#
# What the Sokoban project's Parser did with a frozen pattern database -- look
# every pattern of the level up -- is done here by a BLOK SOURCE: a procedure
# given the level's patterns and the number of boxes, returning the blok string
# of every pattern (the Finder's blok_table by default, serial in this process;
# a caller with a pool of workers hands over one that deals the patterns out)
# under a time budget. A pattern the budget cut has fewer bloks than the full
# table, never a wrong one; the report says which.
#
# Lineage: Games::Sokoban::Parser 1.0 of the Sokoban project (itself the merge
# of its Patterns, Parser01 and PostParser stages, validated byte-identical to
# that chain). Dropped here: the lookup in Patterns.sqlite3 (pattlist), the
# own copy of the pattern solubility test (the Finder's is called), and three
# keys no engine reads -- gate / has_gate (the articulation points) and homes.
# Everything else is the original's text; the gate xt/eq_parser.pl holds the
# output to the project's stored blobs key for key.
use v5.42;
use feature ('refaliasing', 'declared_refs');
no warnings('experimental::refaliasing', 'once');
use Carp           ();
use Compress::Zlib ();
use List::Util ('uniq');
use Storable   ('dclone');
use Time::HiRes                    ();
use Games::Sokoban::Solver::Finder ();
our $VERSION = '0.01';
my (%Game, $W, %Cells, %Cg, %Cm, %Cmk, %Avoid, @Maze, @Baggage, $Nbox,
    %Targets, %PatPoz, %PatList,   %Seen,     %Bad,   %Vyp, @Det_cells, %Bloky,      @Goal, %Goal,
    @Buf,     @Walls,  %Corridors, %Priority, %Route, %Rm,  %Order,     %PaintCache, @Checkpoints);

sub initvars() {
    $W     = $Game{'w'};
    %Cells = %{ $Game{'cells'} };
    %Cg    = %{ $Game{'cg'} };
    %Avoid = %{ $Game{'avoid'} };

    # ONE canonical sorted cell order, used by every cell-iterating sub below, so
    # any output whose order/labels depend on iteration order is deterministic
    # once and for all (keys %Cells == keys %Cg -- verified across game sizes).
    @Det_cells = sort {$a <=> $b} keys %Cells;
    @Baggage   = @{ $Game{'baggage'} };
    $Nbox      = scalar(@Baggage) - 1;
    @Goal      = @{ $Game{'goal'} };
    %Goal      = map(($_, 1), @Goal);

    # Parser01-style remapped maze (walls()/corridor() expect this encoding).
    my $data = $Game{'code'};
    $data =~ tr/,//d;
    $data =~ tr/45678/0023/;
    @Maze = split(//a, $data, 0);

    # reset all working state
    %Cm          = ();
    %Cmk         = ();
    %Targets     = ();
    %Vyp         = ();
    %PatPoz      = ();
    %PatList     = ();
    %Seen        = ();
    %Bad         = ();
    %Bloky       = ();
    @Walls       = ();
    %Corridors   = ();
    %Priority    = ();
    %Route       = ();
    %Order       = ();
    %Rm          = ();
    %PaintCache  = ();
    @Checkpoints = ();
} ## end sub initvars

# Pattern-offset table, keyed by push direction. Depends only on $W, so compute
# ONCE per game (was rebuilt in both patterns() and bloky()).
sub vypocet() {
    my (%vypocet) = ();
    foreach my $x (reverse -1 .. 4) {
        foreach my $y (reverse -2 .. 2) {
            push @{ $vypocet{$W};    }, $x * $W + $y;
            push @{ $vypocet{'-1'};  }, $y * $W - $x;
            push @{ $vypocet{'1'};   }, -$y * $W + $x;
            push @{ $vypocet{ -$W }; }, -$x * $W - $y;
        }
    }
    return %vypocet;
}

# Re-run after EVERY %Cm/%Cmk mutation: removing edges can cascade (newly
# unreachable cells). Does NOT persist to %Game (parse() does that once).
sub prune_unreachable() {
    my (%reachable, @queue);
    for my $bx (@Baggage) {
        for my $t (@{ $Cmk{$bx} // [] }) {
            next if exists $reachable{$t};
            $reachable{$t} = 1;
            push @queue, $t;
        }
    }
    my $bh = 0;
    while ($bh < @queue) {
        my $pos = $queue[$bh++];
        for my $t (@{ $Cmk{$pos} // [] }) {
            next if exists $reachable{$t};
            $reachable{$t} = 1;
            push @queue, $t;
        }
    }
    my %ever_here = (%reachable, map {$_ => 1} @Baggage);
    for my $from (keys %Cmk) {
        if (!exists $ever_here{$from}) {
            delete $Cmk{$from};
            delete $Cm{$from};
            next;
        }
        $Cmk{$from} = [grep {exists $reachable{$_}} @{ $Cmk{$from} }];
        for my $t (keys %{ $Cm{$from} }) {
            delete $Cm{$from}{$t} unless exists $reachable{$t};
        }
        if (!@{ $Cmk{$from} }) {
            delete $Cmk{$from};
            delete $Cm{$from};
        }
    } ## end for my $from (keys %Cmk)
} ## end sub prune_unreachable

# Build the push graph Cm{box}{target}=man-stance and Cmk{box}=[targets], then prune.
sub cm() {
    %Cm      = ();
    %Cmk     = ();
    %Targets = ();
    foreach my $bx (@Det_cells) {
        next if $Avoid{$bx};
        foreach my $t (@{ $Cg{$bx} }) {
            next if $Avoid{$t};
            my $s = $bx * 2 - $t;
            next unless exists $Cells{$s};
            $Cm{$bx}{$t} = $s;
            ++$Targets{$t};
            push @{ $Cmk{$bx} }, $t;
        }
    }
    prune_unreachable();
} ## end sub cm

sub transpose (@lines) {
    my @c;
    foreach $_ (@lines) {
        my $i = 0;
        $c[$i++] .= $_ foreach (split(//a, $_, 0));
    }
    return @c;
}

sub standardize($pattern) {
    my @lines = unpack('(a5)*', $pattern);
OUT: foreach my $i (reverse 1 .. 3) {
        if ($lines[$i] eq '99999') {
            foreach my $j (0 .. $i - 1) {
                $lines[$j] = '99999';
            }
            last OUT;
        }
    }
    @lines     = transpose @lines;
    $lines[0]  = '999999' if $lines[1] eq '999999';
    $lines[-1] = '999999' if $lines[-2] eq '999999';
    @lines     = transpose @lines;
    $pattern   = join('', @lines);
    return $pattern;
} ## end sub standardize

# Extract per-push deadlock patterns. Pushes whose pattern is insoluble
# (Finder::pat_soluble false, or already known Bad) are removed from Cm/Cmk
# (then prune). Surviving pushes get PatPoz{bx}{t}=pattern / PatList{pattern}=count
# for bloky().
sub patterns() {
    %PatPoz  = ();
    %PatList = ();
    my @remove = ();
    my $code   = $Game{'code'};
    $code =~ tr/45678/00233/;
    $code =~ tr/,//d;
    my @maze  = split(//a, $code, 0);
    my %cells = ();

    for (my $i = 0; $i <= $#maze; ++$i) {
        $cells{$i} = $maze[$i];
    }
    foreach my $bx (sort {$a <=> $b} keys %Cm) {
        foreach my $t (sort {$a <=> $b} @{ $Cmk{$bx} }) {
            my $smer = $t - $bx;
            \my @v = $Vyp{$smer};
            my $pattern = '';
            foreach my $s (map($t + $_, @v)) {
                my $pis = exists $cells{$s} ? $cells{$s} : '9';
                $pattern .= $pis;
            }
            substr($pattern, 22, 1) =~ tr/03/47/;
            substr($pattern, 27, 1) =~ tr/03/58/;
            $pattern = standardize($pattern);
            if (exists $Bad{$pattern}) {
                push @remove, [$bx, $t, $pattern];
                next;
            }
            unless ($Seen{$pattern}++) {
                unless (Games::Sokoban::Solver::Finder::pat_soluble($pattern)) {
                    push @remove, [$bx, $t];
                    $Bad{$pattern} = 1;
                    next;
                }
            }
            next if $Nbox == 0;
            my $dat = $pattern =~ tr/03//;
            next if ($dat == 0);
            $PatPoz{$bx}{$t} = $pattern;
            ++$PatList{$pattern};
        } ## end foreach my $t (sort {$a <=>...})
    } ## end foreach my $bx (sort {$a <=>...})
    if (@remove) {
        foreach my $bxt (@remove) {
            my ($x, $t) = @$bxt;
            delete $Cm{$x}{$t};
            if (%{ $Cm{$x} }) {
                $Cmk{$x} = [keys %{ $Cm{$x} }];
            }
            else {
                delete $Cm{$x};
                delete $Cmk{$x};
            }
        }
        prune_unreachable();
    }
} ## end sub patterns

# The bloks of every pattern of the level, from the blok source: a procedure
# ($patlist, nbox => N, deadline => T) -> (\%bloks, \@report), %bloks a blok
# string per pattern (sets of window cells, comma-separated, sets separated by
# semicolons) and the report one row [pattern, kmax, k_done, candidates,
# seconds] per pattern. Each string is turned into the per-push BIT VECTORS the
# engines test; the report is kept for parse() to hand out.
sub bloky($source, $deadline, $report) {
    my $nbox = scalar @Baggage;
    my ($bloks, $rows) = ({}, []);
    if (defined $source and %PatList) {
        ($bloks, $rows) = $source->(\%PatList, 'nbox' => $nbox, 'deadline' => $deadline);
        Carp::croak('Parser: the blok source must return (\%bloks, \@report)')
            unless ref $bloks eq 'HASH' and ref $rows eq 'ARRAY';
    }
    foreach my $pattern (keys %PatList) {
        my $str = $bloks->{$pattern} // '';
        $PatList{$pattern} = length $str ? [map([split(/,/a, $_, 0)], split(/;/a, $str, 0))] : [];
    }
    foreach my $bx (keys %Cmk) {
        foreach my $t (@{ $Cmk{$bx} }) {
            next unless $PatPoz{$bx} && $PatPoz{$bx}{$t};
            my $pattern = $PatPoz{$bx}{$t};
            my @blok    = @{ $PatList{$pattern} };
            next unless @blok;
            @blok = grep (scalar(@$_) < $nbox, @blok);
            \my @v = $Vyp{ $t - $bx };

            # each pattern is persisted as a trimmed BIT VECTOR ('' + vec, so
            # the string ends at the pattern's highest cell), not a cell array:
            # the solvers' hot blok test is then one string (vb &. pv) eq pv per
            # pattern. NB ':5.42' enables 'bitwise': string AND is the DOTTED &. op.
            foreach \my @bl(@blok) {
                my $vec = '';
                vec($vec, $t + $_, 1) = 1 foreach @v[@bl];
                push @{ $Bloky{$bx}{$t} }, $vec;
            }
        } ## end foreach my $t (@{ $Cmk{$bx}...})
    } ## end foreach my $bx (keys %Cmk)
    $Game{'blok'} = dclone \%Bloky;
    if ($report) {
        $report->{'blok'}          = $rows;
        $report->{'patpoz'}        = dclone \%PatPoz;
        $report->{'patterns'}      = scalar keys %PatList;
        $report->{'blok_complete'} = (defined $source and !grep {$_->[2] < $_->[1]} @$rows) ? 1 : 0;
    }
} ## end sub bloky

sub walls() {

    # @Det_cells (sorted): @Walls discovery order, hence atwall record order, must
    # be deterministic, not dependent on hash iteration order.
    foreach my $x (@Det_cells) {
        my @smer = (1, -$W, 1, $W, $W, 1, $W, -1);
        foreach my ($p, $z)(@smer) {
            if ($Maze[$x - $p] == 9 and $Maze[$x + $z] == 9) {
                my $y = $x + $p;
                if ($Maze[$y + $z] == 9 and $Maze[$y] != 9) {
                    my @wall = ($x);
                    while ($Maze[$y + $z] == 9 and $Maze[$y] != 9) {
                        push @wall, $y;
                        $y += $p;
                    }
                    next unless $Maze[$y] == 9;
                    next if @wall < 3;
                    my $test = join('', @Maze[@wall]);
                    next if $test     =~ /^2+$/a;
                    next unless $test =~ /3/a;
                    push @Walls, [@wall];
                }
            } ## end if ($Maze[$x - $p] == ...)
        } ## end foreach my ($p, $z)(@smer)
    } ## end foreach my $x (@Det_cells)
    $Game{'has_wall'} = 0;
    return unless @Walls;
    my $found = 1;
    my %seen  = ();
    my (@w1, @w2, @ws, $key);
    while ($found) {
        my @spojeno = ();
        $found = 0;
        for (my $i = 0; $i <= $#Walls; ++$i) {
            @w1 = @{ $Walls[$i] };
            for (my $j = 0; $j <= $#Walls; ++$j) {
                next if $i == $j;
                @w2 = @{ $Walls[$j] };
                if ($w1[0] == $w2[0]) {
                    @ws  = (reverse(@w1), @w2);
                    @ws  = uniq @ws;
                    $key = join(',', sort {$a <=> $b} @ws);
                    next if $seen{$key}++;
                    push @spojeno, [@ws];
                    $found = 1;
                }
                elsif ($w1[-1] == $w2[0]) {
                    @ws  = (@w1, @w2);
                    @ws  = uniq @ws;
                    $key = join(',', sort {$a <=> $b} @ws);
                    next if $seen{$key}++;
                    push @spojeno, [@ws];
                    $found = 1;
                }
                elsif ($w1[0] == $w2[-1]) {
                    @ws  = (@w2, @w1);
                    @ws  = uniq @ws;
                    $key = join(',', sort {$a <=> $b} @ws);
                    next if $seen{$key}++;
                    push @spojeno, [@ws];
                    $found = 1;
                }
                elsif ($w1[-1] == $w2[-1]) {
                    @ws  = (@w1, reverse(@w2));
                    @ws  = uniq @ws;
                    $key = join(',', sort {$a <=> $b} @ws);
                    next if $seen{$key}++;
                    push @spojeno, [@ws];
                    $found = 1;
                }
            } ## end for (my $j = 0; $j <= $#Walls...)
        } ## end for (my $i = 0; $i <= $#Walls...)
        if ($found) {
            push @Walls, @spojeno;
        }
    } ## end while ($found)
    my %atwall = ();
    foreach \my @wall(@Walls) {
        @wall = sort {$a <=> $b} @wall;
        my $str = join('', @Maze[@wall]);
        my $n   = $str =~ tr/3//;
        foreach $_ (@wall) {
            push @{ $atwall{$_} }, [$n, [@wall]];
        }
    }
    $Game{'has_wall'} = 1;
    $Game{'walls'}    = dclone \%atwall;
} ## end sub walls

# Precompute push levels for a hole / one-sided goal corridor.
sub _macro_levels($cells_ref, $patt, $max_ti = undef) {
    my @cells    = @$cells_ref;
    my @pchars   = split(//a, $patt, 0);
    my $limit    = $max_ti // $#pchars;
    my @goal_idx = sort {$b <=> $a} grep {$pchars[$_] eq '3' && $_ <= $limit} 1 .. $#pchars;
    return undef unless @goal_idx;
    my @levels;
    for my $k (0 .. $#goal_idx) {
        my $ti     = $goal_idx[$k];
        my @pushes = map {[$cells[$_ - 1], $cells[$_], $Cm{ $cells[$_ - 1] }{ $cells[$_] }]} 1 .. $ti;
        push @levels,
            {
                target    => $cells[$ti],
                free_path => [@cells[1 .. $ti - 1]],
                pushes    => \@pushes,
            };
    }
    return \@levels;
} ## end sub _macro_levels

sub corridor() {
    $Game{'has_corridor'} = 0;
    foreach my $x (keys %Cm) {
    TT: foreach my $t (@{ $Cmk{$x} }) {
            my $smer = $t - $x;
            my $zed  = abs($smer) == 1 ? $W : 1;
            next if $Maze[$x + $zed] == 9 and $Maze[$x - $zed] == 9;
            if ($Maze[$t + $zed] == 9 and $Maze[$t - $zed] == 9) {
                my @corridor = $t;
                my $y        = $t + $smer;
                while ($Maze[$y] != 9 and $Maze[$y + $zed] == 9 and $Maze[$y - $zed] == 9) {
                    push @corridor, $y;
                    $y += $smer;
                }
                next TT if ($Maze[$y] == 9);
                next TT if (scalar(@corridor) < 4);
                $y = $corridor[-1];
                my $mode = (exists $Cm{ $y + $smer } and exists $Cm{ $y + $smer }{$y}) ? 'two' : 'one';
                $Corridors{$x}{$t} = [[@corridor], $mode, join('', @Maze[@corridor])];
            }
        } ## end TT: foreach my $t (@{ $Cmk{$x} ...})
    } ## end foreach my $x (keys %Cm)
    my $orig_str  = $Game{'code'} =~ tr/,//dr;
    my @orig_maze = split(//a, $orig_str, 0);
    for my $x (keys %Corridors) {
        for my $t (keys %{ $Corridors{$x} }) {
            my $cor = $Corridors{$x}{$t};
            if ($cor->[1] eq 'one' && $cor->[2] =~ /3/a) {
                my @cells  = @{ $cor->[0] };
                my @blocks = sort {$a <=> $b} grep {$orig_maze[$cells[$_]] eq '4'} 1 .. $#cells;
                my $max_ti = @blocks ? $blocks[0] - 2 : undef;
                $cor->[3] = _macro_levels($cor->[0], $cor->[2], $max_ti);
                $cor->[4] = scalar @blocks;
            }
        }
    }
    if (%Corridors) {
        $Game{'has_corridor'} = 1;
        $Game{'corridor'}     = dclone \%Corridors;
    }
} ## end sub corridor

sub enrich_holes() {
    return unless $Game{'has_hole'};
    my $holes = $Game{'hole'};
    for my $entry (keys %$holes) {
        for my $last (keys %{ $holes->{$entry} }) {
            my $hole = $holes->{$entry}{$last};
            $hole->[2] = _macro_levels($hole->[0], $hole->[1]);
        }
    }
}

# Reachability paint for priority()/reachable() (Parser01's variadic paint,
# renamed to avoid clashing with the memoized route paint below).
sub paint_reach($man, @baggage) {
    my %cg   = ($man, 1);
    my %bags = map(($_, 1), @baggage);
    my ($x, $d);
    $Buf[0] = $man;
    my $bt = 1;
    for (my $bh = 0; $bh < $bt; ++$bh) {
        $x = $Buf[$bh];
        $d = $cg{$x} + 1;
        foreach my $t (@{ $Cg{$x} }) {
            next if exists $bags{$t};
            if (not exists $cg{$t}) {
                $cg{$t} = $d;
                $Buf[$bt++] = $t;
            }
        }
    }
    return %cg;
} ## end sub paint_reach

sub reachable($g, @obstacle) {
    my %obst = map(($_, 1), @obstacle);
    my (%seen1, @heap1);
    foreach my $bx (@Baggage) {
        foreach my $t (@{ $Cmk{$bx} }) {
            next if $t == $g;
            my $p = pack('nn', $Cm{$bx}{$t}, $bx);
            next if $seen1{$p}++;
            push @heap1, $p;
        }
    }
    my ($bh, $bt) = (0, scalar @heap1);
    while ($bh < $bt) {
        my ($man, $box) = unpack('nn', $heap1[$bh++]);
        my %cg = paint_reach($man, $box);
        foreach my $tg (@{ $Cmk{$box} }) {
            next if $tg == $g;
            my $s = $Cm{$box}{$tg};
            next unless exists $cg{$s};
            my $child = pack('nn', $box, $tg);
            next if $seen1{$child}++;
            push @heap1, $child;
            ++$bt;
        }
    }
    my %seen2 = %seen1;
    my @heap2 = grep {
        my ($man, $box) = unpack('nn', $_);
        !$obst{$box} && !$obst{$man};
    } keys %seen1;
    ($bh, $bt) = (0, scalar @heap2);
    while ($bh < $bt) {
        my ($man, $box) = unpack('nn', $heap2[$bh++]);
        my %cg = paint_reach($man, $box, @obstacle);
        foreach my $tg (@{ $Cmk{$box} }) {
            next if $obst{$tg} && $tg != $g;
            my $s = $Cm{$box}{$tg};
            next unless exists $cg{$s};
            return 1 if $tg == $g;
            my $child = pack('nn', $box, $tg);
            next if $seen2{$child}++;
            push @heap2, $child;
            ++$bt;
        }
    }
    return 0;
} ## end sub reachable

# Fill-order search: assign an increasing rank (into %Priority) to each goal in
# @$todo that becomes push-reachable once the still-unfilled goals are treated as
# obstacles, iterated to a fixed point. A SEPARATE procedure so priority() can
# re-run it on the reduced set after a checkpoint removes a stuck goal (a
# checkpoint can unstick its siblings). Returns (\@still-unresolved, next-rank).
sub order($todo, $odr) {
    my @goal  = @$todo;
    my @ngoal = @goal;
    my $zmena = 1;
    while ($zmena) {
        $zmena = 0;
        @ngoal = @goal;
        foreach my $g (@goal) {
            my @obstacle = grep($_ != $g, @goal);
            if (reachable($g, @obstacle)) {
                $Priority{$g} = $odr;
                $zmena        = 1;
                @ngoal        = grep {$_ != $g} @ngoal;
            }
        }
        if ($zmena) {
            ++$odr;
            last unless @ngoal;
            @goal = @ngoal;
        }
    } ## end while ($zmena)
    return (\@ngoal, $odr);
} ## end sub order

# The OLD-parser goal-peeling order: a goal earns the current rank when some
# start box can single-box-push onto it with ALL the still-unranked goals
# standing as walls FROM THE START -- stricter than reachable()'s closure
# seeding, which admits (man,box) states only reachable before the goals are
# blocked. This produces systematically deeper tiers (and ranks games where
# reachable() gets stuck), which is what value_score's tier gate descends.
# Returns the complete ranking, or () when the peel cannot rank every goal
# (the caller keeps its own result).
sub order_peel($allgoal) {
    my @goal  = @$allgoal;
    my %order = ();
    my $found = 1;
    my $odr   = 0;
    while ($found and @goal) {
        $found = 0;
        my %f = ();
    GOAL: foreach my $g (@goal) {
            my @bags   = grep {$_ != $g} @goal;
            my %target = map  {($_, 1)} @bags;
            foreach my $bx (@Baggage) {
                next if $bx == $g;
                my $man;
                foreach my $t (@{ $Cg{$bx} // [] }) {
                    next if $target{$t};
                    $man = $t;
                    last;
                }
                next unless defined $man;
                my $pozice = pack('nn', $man, $bx);
                my %seen   = ($pozice, 1);
                my @heap   = ($pozice);
                while (@heap) {
                    $pozice = shift @heap;
                    my ($m, $box) = unpack('nn', $pozice);
                    my %cg = paint_reach($m, $box, @bags);
                    foreach my $x (@{ $Cmk{$box} // [] }) {
                        next if $target{$x};
                        my $s = $Cm{$box}{$x};
                        next unless $cg{$s};
                        if ($x == $g) {$found = 1; $f{$g} = 1; next GOAL;}
                        my $child = pack('nn', $box, $x);
                        next if $seen{$child}++;
                        push @heap, $child;
                    }
                }
            } ## end foreach my $bx (@Baggage)
        } ## end GOAL: foreach my $g (@goal)
        if ($found) {
            ++$odr;
            $order{$_} = $odr foreach keys %f;
            @goal = grep {!$f{$_}} @goal;
        }
    } ## end while ($found and @goal)
    return () unless keys %order == scalar @$allgoal;
    return %order;
} ## end sub order_peel

# Tier depth of a ranking = number of DISTINCT rank values.
sub _rank_depth($h) {
    my %v;
    ++$v{$_} for values %$h;
    return scalar keys %v;
}

# Goal-fill ordering + the optional checkpoint (P1) preference. Two ranking
# algorithms compete: order()/reachable() (closure-seeded) and order_peel() (the
# old-parser strict peel); the deeper ranking wins, tie -> peel. Outcomes:
#  1. order() ranks every real goal -> has_order=1, order=the deeper ranking;
#     sols stays the plain real terminals (all tailless).
#  1b. order() stuck but the peel is complete -> has_order=1, order=peel ranks,
#     no checkpoints.
#  2. order() gets stuck, but up to 2 checkpoints unstick it, the resulting
#     preference set (real goals with each ga swapped for its park cell P) has
#     EXACTLY nbox cells, AND pref_sols() can build at least one finishing tail
#     -> has_order=1, order=ranks (real goals + each P at the top rank), and
#     pref_sols() ADDS box-on-P terminals (each carrying its P->ga tail).
#  3. otherwise -> has_order=0, order = {each real goal => 1}, nothing else.
# $Game{goal} is ALWAYS the real goals: the forward search targets THEM (so a game
# solvable before stays solvable), the P terminals are only extra shortcut
# endpoints. sols() (the plain real terminals) MUST already have run.
sub priority() {
    %Priority          = ();
    @Checkpoints       = ();
    $Game{'has_order'} = 0;
    my %start_box = map(($_, 1), @Baggage);
    my @allgoal   = sort {$a <=> $b} keys %Goal;

    # Both ranking algorithms run and the DEEPER result wins (tie -> peel, the
    # empirically stronger one). The peel needs no checkpoints, so a complete
    # peel also short-circuits the P1 machinery below.
    my %peel = order_peel(\@allgoal);
    $Priority{$_} = 1 foreach grep {$start_box{$_}} @allgoal;    # a box already on a goal = rank 1
    my @todo = grep {!$start_box{$_}} @allgoal;
    my ($ngoal, $odr) = order(\@todo, 1);
    if (!@$ngoal) {                                              # CASE 1: full order, no checkpoints
        %Priority          = %peel if %peel and _rank_depth(\%peel) >= _rank_depth(\%Priority);
        $Game{'has_order'} = 1;
        $Game{'order'}     = dclone \%Priority;
        return;
    }
    if (%peel) {    # CASE 1b: the closure order is stuck but the peel ranks everything
        %Priority          = %peel;
        $Game{'has_order'} = 1;
        $Game{'order'}     = dclone \%Priority;
        return;
    }

    # order() is stuck: try up to 2 checkpoints, re-running order() on the residue
    # after each one removes a stuck goal. A checkpoint [ga, P] parks the box on a
    # fresh cell P from which a SINGLE push finishes it onto ga; for the tail to be
    # feasible from the solved board, P must be a fresh non-goal cell DISTINCT from
    # every other P, and the push-stance Cm{P}{ga} must not itself be a goal (a goal
    # always holds a box in the terminal, so the player could never stand there).
    my %avoid_park = (%Goal, %start_box);
    my (%used_P, @checkpoints);
    my @rest   = @$ngoal;
    my $budget = 2;
    while (@rest && $budget) {
        my ($ga, $P);
    FIND: foreach my $g (@rest) {
            foreach my $t (@{ $Cmk{$g} }) {
                next if $avoid_park{$t} || $used_P{$t};
                next unless grep {$_ == $g} @{ $Cmk{$t} };    # t -> g is a valid single push (the tail push)
                my $stance = $Cm{$t}{$g};                     # player pushes t -> g from here
                next unless defined $stance && !$Goal{$stance};
                ($ga, $P) = ($g, $t);
                last FIND;
            }
        }
        last unless defined $ga;
        $used_P{$P} = 1;
        --$budget;
        push @checkpoints, [$ga, $P];
        @rest = grep {$_ != $ga} @rest;
        ($ngoal, $odr) = order(\@rest, $odr);
        @rest = @$ngoal;
    } ## end while (@rest && $budget)

    # CASE 2 requires: everything ordered now, checkpoints exist, the preference set
    # has exactly nbox cells, and pref_sols() builds >=1 finishing tail.
    if (!@rest && @checkpoints) {
        my %pref = %Goal;
        my $high = $odr;
        for my $cp (@checkpoints) {
            my ($ga, $P) = @$cp;
            delete $pref{$ga};
            $pref{$P}      = 1;
            $Priority{$P}  = $high;                              # P staged first (top rank)
            $Priority{$ga} = 0 unless defined $Priority{$ga};    # ga stays a real goal (value_score reads its rank)
        }
        if (keys %pref == scalar @Baggage) {
            @Checkpoints = @checkpoints;
            if (pref_sols(\%pref)) {                             # appends box-on-P terminals + tails; true if >=1 built
                $Game{'has_order'} = 1;
                $Game{'order'}     = dclone \%Priority;
                return;
            }
            @Checkpoints = ();                                   # tails failed -> undo, fall to CASE 3
        }
    } ## end if (!@rest && @checkpoints)

    # CASE 3: cannot order -> flat {goal => 1}.
    %Priority          = map(($_, 1), keys %Goal);
    $Game{'order'}     = {%Priority};
    $Game{'has_order'} = 0;
} ## end sub priority

# Shortest player walk from $from to $to over %Cg, treating the cells in %$block
# as walls. Returns the move string (lowercase l/r/u/d, the get_path() convention)
# or undef if unreachable. '' when already there.
sub _walk_moves($from, $to, $block) {
    return '' if $from == $to;
    my %pis = (-1, 'l', 1, 'r', $W, 'd', -$W, 'u');
    my (%prev, %seen);
    my @q = ($from);
    $seen{$from} = 1;
    my $found = 0;
OUTER: while (@q) {
        my $x = shift @q;
        foreach my $y (@{ $Cg{$x} // [] }) {
            next if $seen{$y} || $block->{$y};
            $seen{$y} = 1;
            $prev{$y} = $x;
            if ($y == $to) {$found = 1; last OUTER}
            push @q, $y;
        }
    }
    return undef unless $found;
    my @path;
    for (my $c = $to; $c != $from; $c = $prev{$c}) {unshift @path, $c}
    my ($s, $p) = ('', $from);
    foreach my $n (@path) {$s .= $pis{ $n - $p }; $p = $n}
    return $s;
} ## end sub _walk_moves

# All orderings of @$list (recursive; @Checkpoints is at most 2 long, so this is
# tiny). Used because the checkpoints are not order-independent: finishing P1 first
# may block P2's push-stance while the reverse order succeeds.
sub _permute($list) {
    return ([]) unless @$list;
    my @out;
    for my $i (0 .. $#$list) {
        my @rest = @$list;
        my ($pick) = splice(@rest, $i, 1);
        push @out, [$pick, @$_] foreach _permute(\@rest);
    }
    return @out;
}

# Push the checkpoints, in the given order, off their park cells onto their real
# goals, starting from the preference-solved player position. Returns the move
# string (walks lowercase + the P->ga push UPPERCASE, get_path() convention) or
# undef if any step is infeasible on the idealized board.
sub _tail_order($player, $boxes_ref, $order) {
    my %pis  = (-1, 'l', 1, 'r', $W, 'd', -$W, 'u');
    my %box  = %$boxes_ref;                            # occupied cells (the substituted goal set), mutated as we push
    my $cur  = $player;
    my $tail = '';
    foreach my $cp (@$order) {
        my ($ga, $P) = @$cp;
        my $stance = $Cm{$P}{$ga};
        return undef unless defined $stance;
        my $walk = _walk_moves($cur, $stance, \%box);    # box on P (and every placed box) blocks the walk
        return undef unless defined $walk;
        my $push = $pis{ $ga - $P };
        return undef unless defined $push;
        $tail .= $walk . uc $push;
        delete $box{$P};
        $box{$ga} = 1;                                   # box moved P -> ga
        $cur = $P;                                       # player ends on P after the push
    }
    return $tail;
} ## end sub _tail_order

# The "tail": from the preference-solved player position ($player = a $Game{sols}
# key's player, with every box but the parked ones already on its goal), the moves
# that push every checkpoint box off P onto its real goal ga, finishing the REAL
# solution. Idealized (walks over the final box set); the solver re-validates.
# Tries every checkpoint ORDER and returns the first that is feasible (undef if
# none works -- then this terminal is skipped).
sub _tail_moves($player, $boxes_ref) {
    foreach my $order (_permute(\@Checkpoints)) {
        my $tail = _tail_order($player, $boxes_ref, $order);
        return $tail if defined $tail;
    }
    return undef;
}

# Terminal (solved) positions the engines test against, packed (player,@boxes)
# with $Game{vzp}. The BASE set: the plain REAL terminals (all boxes on the true
# goals), each keyed to '' (no tail). MUST run before priority(), which may ADD
# checkpoint-substituted terminals via pref_sols(). A terminal's value is a move
# string: '' = a real solution (the Solver's stop); non-empty = a box-on-P shortcut
# whose P->ga tail finishes the real solution (Firstbet appends it, the Solver
# ignores tailed entries and keeps searching to a tailless one).
sub sols () {
    my %Sols;
    my @real = sort {$a <=> $b} keys %Goal;
    foreach my $bx (keys %Cm) {
        next if $Goal{$bx};
        foreach my $t (@{ $Cmk{$bx}; }) {
            $Sols{ pack $Game{'vzp'}, $bx, @real } = '' if $Goal{$t};    # real terminal, no tail
        }
    }
    $Game{'sols'} = \%Sols;
    return;
}

# Append the checkpoint-substituted terminals to $Game{sols}: a box parked on each
# park cell P (the rest on their real goals), keyed to the P->ga finishing tail.
# %$pref is the substituted box set (real goals with each ga swapped for its P);
# @Checkpoints drives the tail. Returns the number of feasible tailed terminals
# added -- 0 means the P1 aid is unusable and priority() falls back to CASE 3.
sub pref_sols($pref) {
    my @search = sort {$a <=> $b} keys %$pref;
    my $added  = 0;
    foreach my $bx (keys %Cm) {
        next if $pref->{$bx};
        foreach my $t (@{ $Cmk{$bx}; }) {
            next unless $pref->{$t};
            my $tail = _tail_moves($bx, $pref);
            next unless defined $tail;    # skip an idealized-infeasible stance
            $Game{'sols'}{ pack $Game{'vzp'}, $bx, @search } = $tail;
            ++$added;
        }
    }
    return $added;
} ## end sub pref_sols

sub reverse_moves() {
    foreach my $x (keys %Cm) {
        $Rm{$x} = [values %{ $Cm{$x} }];
    }
}

# Memoized player-reachability flood-fill for find_route (pure function of
# (man,box) + static graph). Returns a shared read-only hashref {cell=>dist}.
sub paint($man, $box) {
    my $key = "$man,$box";
    return $PaintCache{$key} if exists $PaintCache{$key};
    my %wanted = map(($_, 1), @{ $Rm{$box} });
    my %cg     = ($man, 1);
    my @buf    = $man;
    while (@buf) {
        my $x = shift @buf;
        my $d = $cg{$x} + 1;
        foreach my $t (@{ $Cg{$x} }) {
            next if $t == $box;
            next if exists $cg{$t};
            $cg{$t} = $d;
            if (exists $wanted{$t}) {
                delete $wanted{$t};
                return $PaintCache{$key} = \%cg unless %wanted;
            }
            push @buf, $t;
        }
    }
    return $PaintCache{$key} = \%cg;
} ## end sub paint

sub find_route($bx, $g) {
    my (@heap, $n_open, %seen, %parent, $bestlen, $bestbet);
    $bestbet = undef;
    $bestlen = 'Inf';
    foreach my $t (@{ $Cmk{$bx} }) {
        my $s      = $Cm{$bx}{$t};
        my $pozice = "$s,$bx";
        push @heap, $pozice;
        $seen{$pozice}   = 0;
        $parent{$pozice} = '';
    }
    $n_open = scalar @heap;
    while ($n_open) {
        my $pozice = shift @heap;
        my $sol    = $seen{$pozice};
        --$n_open;
        my ($man, $box) = split(/,/a, $pozice, 0);
        my $cg = paint($man, $box);
        foreach my $t (@{ $Cmk{$box} }) {
            my $s = $Cm{$box}{$t};
            next unless exists $cg->{$s};
            my $sollen = $sol + $cg->{$s};
            next if $sollen > $bestlen;
            my $child = "$box,$t";
            next if (exists $seen{$child} and $seen{$child} <= $sollen);
            $parent{$child} = $pozice;
            $seen{$child}   = $sollen;

            if ($t == $g) {
                $bestlen = $sollen;
                $bestbet = $child;
                next;
            }
            push @heap, $child;
            ++$n_open;
        } ## end foreach my $t (@{ $Cmk{$box...}})
    } ## end while ($n_open)
    return ('Inf') unless $bestbet;
    my @postup = ($bestbet);
    my $p      = $bestbet;
    while ($p = $parent{$p}) {
        unshift @postup, $p;
    }
    return ($bestlen, @postup);
} ## end sub find_route

# Concrete shortest player-walk from $from to $to over the walk graph %Cg with a
# single box cell as an obstacle. Returns the list of cells ON that walk (order
# irrelevant -- it feeds a set). Empty if unreachable.
sub _walk_cells($from, $to, $box) {
    return ($from) if $from == $to;
    my %prev = ($from => -1);
    my @q    = ($from);
WALK: while (@q) {
        my $x = shift @q;
        foreach my $t (@{ $Cg{$x} // [] }) {
            next if $t == $box || exists $prev{$t};
            $prev{$t} = $x;
            last WALK if $t == $to;
            push @q, $t;
        }
    }
    return () unless exists $prev{$to};
    my (@path, $c);
    for ($c = $to; $c != -1; $c = $prev{$c}) {push @path, $c;}
    return @path;
} ## end sub _walk_cells

# The dedup set of cells that must be EMPTY (of any OTHER box) for the macro "push
# the box along @$moves (box-cell sequence starting at $bx) onto the goal" to be
# executable: every cell the box is pushed through, plus every cell the player walks
# through between consecutive pushes (get_path-style), plus the push stances.
# Idealized (the route was computed on an empty field); a solver still verifies it
# against the live box placement -- it only answers, fast, "could this macro run here
# at all?". Returned as a HASH {cell => 1} (not a sorted list): the consumer tests it
# the cheap way, iterating its (few) boxes and asking must_empty->{$box}, O(nbox)
# instead of O(route length).
sub _macro_cells($bx, $moves) {
    return {} unless @$moves;
    my @c    = ($bx, @$moves);           # box occupies c[0]=bx, then c[1..k]
    my %need = map(($_, 1), @$moves);    # the box moves INTO c[1..k]
    my $s1   = $Cm{ $c[0] }{ $c[1] };    # stance for the first push
    $need{$s1} = 1 if defined $s1;
    my $player = $c[0];                  # after push 1 the player stands on c[0]
    for (my $i = 2; $i < @c; ++$i) {     # push i moves the box c[i-1] -> c[i]
        my $stance = $Cm{ $c[$i - 1] }{ $c[$i] };
        next unless defined $stance;
        $need{$_} = 1 foreach _walk_cells($player, $stance, $c[$i - 1]);
        $player = $c[$i - 1];
    }
    return \%need;
} ## end sub _macro_cells

# Canonical Route: for EVERY push-graph key X and EVERY goal g, the ideal single-box
# route (empty field, one box on X). The transient %Route (consumed by
# podklady()/common_path()) keeps the rich record {distance,steps,moves,must_empty};
# the PERSISTED $Game{'routes'} is compacted to { X => { g => [moves_packed,
# must_empty_packed] } } -- both 'n*' cell strings (moves = box-cell sequence in
# order, must_empty = the macro-feasibility cell set). The engines unpack ONCE at
# game load back into the rich runtime shape, so the search hot path never touches
# pack/unpack. distance/steps per-record scalars are NOT persisted (they duplicate
# the raw distance/steps tables). Only reachable routes are persisted.
sub route() {
    my %routes;
    foreach my $bx (keys %Cmk) {
        foreach my $g (@Goal) {
            next if $bx == $g;
            my ($bestlen, @postup) = find_route($bx, $g);
            my @moves;
            foreach my $p (@postup) {
                push @moves, (split /,/a, $p, 0)[1];
            }
            shift @moves;
            my $rec = {
                'distance'   => $bestlen,                     # player-move length (walk+push)
                'steps'      => scalar @moves,                # box-push count
                'moves'      => [@moves],
                'must_empty' => _macro_cells($bx, \@moves),
            };
            $Route{$bx}{$g}  = $rec;
            $routes{$bx}{$g} = [pack('n*', @moves), pack('n*', sort {$a <=> $b} keys %{ $rec->{'must_empty'} })]
                if @moves;                                    # persist reachable only, compact
        } ## end foreach my $g (@Goal)
    } ## end foreach my $bx (keys %Cmk)
    $Game{'routes'} = \%routes;
} ## end sub route

# Pure-function port of Firstbet.pm::recalc_quad.
sub _quad($raw) {
    my $max_dist = 0;
    foreach my $bx (keys %$raw) {
        foreach my $v (values %{ $raw->{$bx} }) {
            next           if $v eq 'Inf';
            $max_dist = $v if $v > $max_dist;
        }
    }
    my $maxp   = ($max_dist + 1)**2;
    my $maxval = 0.0;
    $maxval += $maxp * (1 + $_) foreach values %Order;
    my %quad;
    foreach my $bx (keys %$raw) {
        foreach my $g (keys %{ $raw->{$bx} }) {
            my $v = $raw->{$bx}{$g};
            $quad{$bx}{$g} = (!defined $v or $v eq 'Inf') ? 0 : ($max_dist - $v + 1)**2;
        }
    }
    return (\%quad, $maxp, $maxval);
} ## end sub _quad

sub podklady() {
    my (%draw, %zraw, %rmark);
    foreach my $bx (keys %Route) {
        foreach my $g (keys %{ $Route{$bx} }) {
            my $r = $Route{$bx}{$g};
            if (@{ $r->{'moves'} }) {
                $draw{$bx}{$g} = $r->{'distance'};    # player-move length
                $zraw{$bx}{$g} = $r->{'steps'};       # box-push count
            }
            else {
                $draw{$bx}{$g} = 'Inf';
                $zraw{$bx}{$g} = 'Inf';
            }
        }
    }
    foreach my $bx (@Baggage) {
        foreach my $g (@Goal) {
            my $r   = $Route{$bx}{$g} or next;
            my @seq = ($bx, @{ $r->{'moves'} });
            next unless @seq > 1;
            for (my $i = 0; $i < $#seq; ++$i) {
                $rmark{ $seq[$i] }{ $seq[$i + 1] } = 1;
            }
        }
    }
    my ($dq, $dmaxp, $dmaxval) = _quad(\%draw);
    my ($zq, $zmaxp, $zmaxval) = _quad(\%zraw);

    # RAW canonical metrics: distance = player-move length, steps = box-push
    # count; the QUAD scoring tables are derived from them.
    $Game{'distance'}      = \%draw;
    $Game{'steps'}         = \%zraw;
    $Game{'route'}         = \%rmark;
    $Game{'distance_quad'} = $dq;
    $Game{'maxp'}          = $dmaxp;
    $Game{'maxval'}        = $dmaxval;
    $Game{'steps_quad'}    = $zq;
    $Game{'maxp_steps'}    = $zmaxp;
    $Game{'maxval_steps'}  = $zmaxval;
} ## end sub podklady

sub common_path() {
    my (%count, %routes, $nvalid);
    $nvalid = 0;
    foreach my $bx (@Baggage) {
        foreach my $g (@Goal) {
            next if $bx == $g;
            my $r = $Route{$bx}{$g} or next;
            next unless @{ $r->{'moves'} };
            my @seq = ($bx, @{ $r->{'moves'} });
            my @edges;
            for (my $i = 0; $i < $#seq; ++$i) {
                push @edges, [$seq[$i], $seq[$i + 1]];
            }
            $routes{$bx}{$g} = \@edges;
            ++$nvalid;
            ++$count{ $_->[0] }{ $_->[1] } foreach @edges;
        }
    } ## end foreach my $bx (@Baggage)
    my %candidate;
    foreach my $s (keys %count) {
        foreach my $t (keys %{ $count{$s} }) {

            # an edge LANDING on a goal is never part of the conveyor -- the
            # c_path endpoint must sit OFF the goals, otherwise to_goal()'s
            # deliveries start from an occupied goal and mostly fail.
            next                   if $Goal{$t};
            $candidate{$s}{$t} = 1 if $count{$s}{$t} == $nvalid;
        }
    }
    unless ($nvalid and %candidate) {
        @Game{ 'has_cp', 'c_path', 'common_path' } = (0, [], {});
        return;
    }
    my %index;
    foreach my $bx (keys %routes) {
        foreach my $g (keys %{ $routes{$bx} }) {
            my $idx = 0;
            foreach my $e (@{ $routes{$bx}{$g} }) {
                next unless $candidate{ $e->[0] }{ $e->[1] };
                my ($s, $t) = @$e;
                if    (!exists $index{$s}{$t}) {$index{$s}{$t} = $idx}
                elsif ($index{$s}{$t} != $idx) {
                    @Game{ 'has_cp', 'c_path', 'common_path' } = (0, [], {});
                    return;
                }
                ++$idx;
            }
        }
    } ## end foreach my $bx (keys %routes)
    my @c_path;
    foreach my $s (keys %index) {
        foreach my $t (keys %{ $index{$s} }) {
            $c_path[$index{$s}{$t}] = [$s, $t];
        }
    }
    foreach my $i (0 .. $#c_path) {
        unless (defined $c_path[$i]) {
            @Game{ 'has_cp', 'c_path', 'common_path' } = (0, [], {});
            return;
        }
    }
    my %CP;
    foreach my $j (0 .. $#c_path) {
        my ($s, $t) = @{ $c_path[$j] };
        $CP{$s}{$t} = $j;
    }
    $Game{'has_cp'}      = scalar @c_path;
    $Game{'c_path'}      = dclone \@c_path;
    $Game{'common_path'} = dclone \%CP;
} ## end sub common_path

# Player-reachable cells from $man over %Cg with the moving box $box and every cell
# in $blk (standing boxes) as walls. Returns {cell=>walk-distance}.
sub _reach($man, $box, $blk) {
    my %d = ($man => 0);
    my @q = ($man);
    while (@q) {
        my $x  = shift @q;
        my $nd = $d{$x} + 1;
        foreach my $t (@{ $Cg{$x} // [] }) {
            next if $t == $box || $blk->{$t} || exists $d{$t};
            $d{$t} = $nd;
            push @q, $t;
        }
    }
    return \%d;
}

# Single-box push route from state (player $man, box $box) to goal $g, with the
# cells in @$blocked occupied by standing boxes (walls). Returns the box-push
# sequence [[box_src,box_tgt],...] or () if unreachable.
sub _route_to_goal($man, $box, $g, $blocked) {
    my %blk   = map(($_, 1), @$blocked);
    my $start = "$man,$box";
    my (%seen, %parent);
    $seen{$start}   = 0;
    $parent{$start} = '';
    my @heap = ($start);
    my ($bestlen, $best) = ('Inf', undef);
    while (@heap) {
        my $pozice = shift @heap;
        my ($m, $bx) = split(/,/a, $pozice, 0);
        my $sol   = $seen{$pozice};
        my $reach = _reach($m, $bx, \%blk);
        foreach my $t (@{ $Cmk{$bx} // [] }) {
            next if $blk{$t};
            my $s = $Cm{$bx}{$t};

            # defined, not truthy: the player STANDS on the stance (distance 0)
            # for the first delivery push right after the last conveyor push --
            # a falsy 0 dropped exactly that push and gutted to_goal coverage
            next unless defined $reach->{$s};
            my $sollen = $sol + $reach->{$s};
            next if $bestlen ne 'Inf' && $sollen >= $bestlen;
            my $child = "$bx,$t";
            next if exists $seen{$child} && $seen{$child} <= $sollen;
            $seen{$child}   = $sollen;
            $parent{$child} = $pozice;
            if ($t == $g) {$bestlen = $sollen; $best = $child; next;}
            push @heap, $child;
        } ## end foreach my $t (@{ $Cmk{$bx}...})
    } ## end while (@heap)
    return () unless defined $best;
    my @chain = ($best);
    my $p     = $best;
    while ($p = $parent{$p}) {unshift @chain, $p;}
    shift @chain;    # drop the start state (carries no push)
    my @seq;
    foreach my $st (@chain) {
        my ($src, $tgt) = split(/,/a, $st, 0);
        push @seq, [$src, $tgt];
    }
    return @seq;
} ## end sub _route_to_goal

# When the game has a common path, precompute the delivery macros from the conveyor
# ENDPOINT (c_path[-1]) to each goal -- routed in goal-fill order (highest %Order
# first), each blocking the already-delivered goals. Stored as
# $Game{'to_goal'} = { goal => [[box_src,box_tgt],...] }. All-or-nothing: the map
# is stored only when EVERY goal is deliverable from the endpoint -- a partial map
# would let the conveyor macro strand boxes on a game it cannot finish.
sub to_goal() {
    $Game{'to_goal'} = {};
    my $cpath = $Game{'c_path'};
    return unless $cpath && @$cpath;
    my ($man, $box) = @{ $cpath->[-1] };
    my @ng = sort {($Order{$b} // 0) <=> ($Order{$a} // 0)} @Goal;
    my (@blocked, %tg);
    foreach my $g (@ng) {
        my @seq = _route_to_goal($man, $box, $g, \@blocked);
        next unless @seq;
        $tg{$g} = \@seq;
        push @blocked, $g;
    }
    $Game{'to_goal'} = dclone \%tg if %tg and keys %tg == scalar @Goal;
} ## end sub to_goal

sub packing() {

    # Position serialization width. Cell indices run 0..(count-1); if the whole
    # cell count fits in a single byte, positions are packed 1-byte ('C') instead
    # of 2-byte ('n').
    #   vzp = pack template:   pack(vzp, $man, @baggage)
    #   vzu = unpack template: unpack(vzu, $pos) -> ($man, @baggage)   (leading
    #         field = man, then baggage; solvers also derive $Zbp from vzu =~ /C/)
    my $count = length($Game{'code'} =~ tr/,//dr);
    @Game{ 'vzp', 'vzu' } = $count < 256 ? ('C*', 'CC*') : ('n*', 'nn*');
}

# THE ONE PASS. $code is the record Code::prepare returned (copied, not
# touched); the options:
#   blok_budget => S     seconds for the bloks of the level's patterns: undef
#                        (the default) = no limit, the complete table; 0 = no
#                        bloks at all; S > 0 = a deadline S seconds from now
#   blok_source => CODE  the procedure that gives the bloks of the patterns
#                        (Finder::blok_table by default)
#   report      => \%r   filled with: blok (the source's rows), patpoz (box
#                        cell -> target -> pattern), patterns (how many),
#                        blok_complete (1 when every pattern was done to its
#                        largest size), seconds (per stage)
# Returns %Game, the engines' input; blob(\%game) is what they take.
sub parse($code, %opt) {
    Carp::croak('Parser::parse: a hash reference from Code::prepare is needed') unless ref $code eq 'HASH';
    my $budget = $opt{'blok_budget'};
    my $source = exists $opt{'blok_source'} ? $opt{'blok_source'} : \&Games::Sokoban::Solver::Finder::blok_table;
    undef $source if defined $budget and $budget == 0;
    my $deadline = (defined $budget and $budget > 0) ? Time::HiRes::time() + $budget : undef;
    my $report   = $opt{'report'};
    my $t0       = Time::HiRes::time();
    %Game = %{ dclone($code) };
    initvars();
    delete $Game{'md5'};
    %Vyp = vypocet();    # ONCE, shared by patterns() and bloky()

    # --- push graph + patterns ---
    cm();                          # build Cm/Cmk + prune
    patterns();                    # PatPoz/PatList + @remove + prune
    $Game{'cm'}  = dclone \%Cm;    # persist the pruned graph ONCE
    $Game{'cmk'} = dclone \%Cmk;
    my $t1 = Time::HiRes::time();

    # --- structure ---
    bloky($source, $deadline, $report);
    my $t2 = Time::HiRes::time();
    walls();
    corridor();
    enrich_holes();
    packing();                     # sets vzp/vzu; MUST precede sols() (sols packs via vzp)
    sols();                        # the plain real terminals -- MUST precede priority()
    priority();                    # order + optional P1 preference; may ADD box-on-P terminals to sols
    ($Game{'code'} =~ tr/,//dr) =~ /[568]/;
    $Game{'player'} = $-[0];
    $Game{'h'}      = 1 + ($Game{'code'} =~ tr/,//);
    $Game{'ncell'}  = $Game{'code'} =~ tr/034587//;
    $Game{'nbox'}   = scalar @{ $Game{'baggage'} };

    # --- route stats + quadratization ---
    # priority()/reachable() autovivify absent goal/park cells into %Cm/%Cmk as a
    # side effect (e.g. @{ $Cmk{$g} } for a goal not in the graph); restore the
    # clean graph so route() is not polluted with spurious source cells.
    %Cm    = %{ $Game{'cm'} };
    %Cmk   = %{ $Game{'cmk'} };
    %Order = %{ $Game{'order'} };
    reverse_moves();
    route();

    # A goal that no box can ever be pushed onto -- from no cell of the push
    # graph, which is every cell a box can stand on -- makes the level one
    # nobody can solve, and the engines were never written for that: they
    # answer UNSOLVABLE after a search, or die on a table with no entry. The
    # Sokoban project's collection has no such level (the Code stage reduced
    # every level and its games were all meant to be solved); a level typed by
    # a user may be one, so it is refused here with the cell named.
    my %home = map {($_, 1)} @Baggage;
    for my $g (@Goal) {
        next if $home{$g};
        next if grep {exists $Game{'routes'}{$_}{$g}} keys %{ $Game{'routes'} };
        Carp::croak(
            "REFUSED: no box can ever be pushed onto the goal at cell $g (row " . int($g / $W) . ", column " . ($g % $W) . ')');
    }
    podklady();
    common_path();
    to_goal();

    # Parse-time scaffolding no engine reads stays out of the result.
    delete @Game{qw(avoid cells firststep)};
    if ($report) {
        my $t3 = Time::HiRes::time();
        $report->{'seconds'} = { 'graph' => $t1 - $t0, 'blok' => $t2 - $t1, 'rest' => $t3 - $t2 };
    }
    return %Game;
} ## end sub parse

# The engines take the analysis as one compressed string.
sub blob ($game) {
    return Compress::Zlib::compress(Storable::nfreeze($game));
}
1;
__END__

=head1 NAME

Games::Sokoban::Solver::Parser - the level analysis the engines search on

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Code   ();
    use Games::Sokoban::Solver::Parser ();

    my %code = Games::Sokoban::Solver::Code::prepare($code1);
    my %game = Games::Sokoban::Solver::Parser::parse(\%code,
        'blok_budget' => 30, 'report' => \my %report);
    my $blob = Games::Sokoban::Solver::Parser::blob(\%game);   # what Firstbet takes

    say "$report{'patterns'} patterns, "
        . ($report{'blok_complete'} ? 'every blok found' : 'the budget cut some');

=head1 DESCRIPTION

One pass from the record L<Games::Sokoban::Solver::Code> returns to the
complete analysis the search engines take: the push graph pruned to what a box
can ever reach, the deadlock patterns of every push (a push dead by itself is
removed; the sets of other boxes that make it dead -- its I<bloks> -- are
computed by L<Games::Sokoban::Solver::Finder> and stored as bit vectors), the
wall, corridor and hole deadlock tables, the goal-fill order, the terminal
positions, the single-box routes to every goal with the raw and quadratized
distance tables, the common path of a conveyor level and its delivery macros,
and the template a position is packed with.

The bloks are the one part that costs real time (a pattern takes from a
millisecond to minutes), so they are computed under a budget by a I<blok
source>: a procedure given the level's patterns, the number of boxes and an
absolute deadline, returning a blok string per pattern and a report. The
default source is the Finder's C<blok_table>, which works the patterns one
after another in this process; a caller with a pool of workers can hand over
one that deals the patterns out. A pattern the deadline cut has fewer bloks
than the complete table, never a wrong one; C<blok_complete> in the report says
whether any was cut.

=head1 FUNCTIONS

=over 4

=item parse CODE, OPTIONS

CODE is a reference to the hash C<Code::prepare> returned; it is copied, not
changed. OPTIONS: C<blok_budget> (seconds; C<undef>, the default, means the
complete table, C<0> no bloks at all), C<blok_source> (the procedure described
above), C<report> (a hash reference, filled with C<blok> -- the source's rows
C<[pattern, kmax, k_done, candidates, seconds]> --, C<patpoz>, C<patterns>,
C<blok_complete> and C<seconds> per stage). Returns the analysis as a hash.

=item blob GAME

The analysis as one compressed string (C<Compress::Zlib::compress> of
C<Storable::nfreeze>), the form the engines take.

=back

=head1 THE BLOK BUDGET

Measured on 2026-10-16 against the Sokoban project's stored tables (the
complete bloks of 1.92 million patterns): 50 random games of each size tier of
the project's collection, the bloks of every game computed by the serial
C<blok_table> under four budgets, and the share of the stored blok vectors the
budget recovered. C<xt/eq_parser.pl --calibrate> is the measurement.

    tier  budget  games  share of vectors  patterns complete  games complete
      1     10 s    50        96.2 %            93.9 %              46
      1     30 s    50        98.5 %            98.0 %              49
      1     60 s    50        98.5 %            98.0 %              49
      1    120 s    50        98.6 %            98.1 %              49
      2     10 s    51        60.5 %            73.2 %              20
      2     30 s    51        69.4 %            80.3 %              27
      2     60 s    51        77.5 %            85.8 %              31
      2    120 s    51        84.0 %            90.5 %              37
      3     10 s    50        53.2 %            69.9 %              16
      3     30 s    50        62.4 %            76.4 %              23
      3     60 s    50        67.7 %            80.8 %              26
      3    120 s    50        71.2 %            82.9 %              30
      4     10 s    50        48.0 %            68.6 %              10
      4     30 s    50        57.0 %            76.0 %              13
      4     60 s    50        63.6 %            80.3 %              20
      4    120 s    50        70.1 %            83.5 %              23

The tiers are the project's size classes of a level (1 the smallest, about
20 floor cells and up to 16 boxes; 4 the largest, about 70 cells and up to 30
boxes). A small level has its whole table within 30 seconds; a large one
recovers a little over half of its vectors in 30 seconds and the rest comes
slowly -- doubling the budget adds five to eight points, and the patterns
left are the ones that took the project minutes each.

The default budget of the program is 30 seconds, for two reasons. The
program's default time for one mode of the race is 60 seconds, and the bloks
are paid once before the race starts, so a budget longer than a mode's would
hold the race back for a table the engines can do without (every engine has
a deadlock battery of its own; a missing blok costs search, never
correctness). And the program deals the patterns out to its pool of workers,
so 30 seconds of budget with four workers is the work of the 120-second row
above. Whoever wants the complete table of a large level sets the budget to
a few minutes, or to none at all with C<-1>.

=head1 THE KEYS OF THE ANALYSIS

C<code> (the board, rows joined by commas), C<w h ncell nbox player baggage
goal>, C<vzp vzu> (pack templates), C<cm cmk cg> (push graph and walk graph),
C<blok>, C<has_wall walls>, C<has_corridor corridor>, C<has_hole hole>,
C<sols>, C<has_order order>, C<routes route distance steps distance_quad
steps_quad maxp maxval maxp_steps maxval_steps>, C<has_cp c_path common_path
to_goal>. Their shapes are those of the Sokoban project's blobs, less three
keys no engine read (C<gate>, C<has_gate>, C<homes>).

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
