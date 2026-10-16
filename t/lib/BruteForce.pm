package BruteForce;

# The oracle of the tests: the shortest solution of a tiny level, found by the
# plainest search there is -- breadth first over every position (the player's
# cell and the set of box cells), one step of the player at a time -- so that
# it shares no idea, let alone code, with the solvers under test.
#
# It can afford that only on the hand-made micro levels of t/data (a few boxes,
# a few dozen cells); on anything larger it would run out of memory, which is
# why the real solvers exist.
use v5.42;

# A level as the distribution stores it: rows of digits joined by commas.
sub solve ($code) {
    my @rows  = split(/,/, $code, -1);
    my $w     = length $rows[0];
    my $cells = join('', @rows);
    my (@free, @goal, %box, $man);
    for my $cell (0 .. length($cells) - 1) {
        my $d = substr($cells, $cell, 1);
        $free[$cell] = 1     if $d ne '9' and $d ne '1';
        $goal[$cell] = 1     if $d eq '3' or $d eq '7' or $d eq '8';
        $box{$cell}  = 1     if $d eq '4' or $d eq '7';
        $man         = $cell if $d eq '5' or $d eq '6' or $d eq '8';
    }
    die "BruteForce: no player\n" unless defined $man;
    my $key    = sub ($man, $box) {join(',', $man, sort {$a <=> $b} keys %$box)};
    my %seen   = ($key->($man, \%box) => '');
    my @queue  = ([$man, {%box}, '']);
    my %letter = (-1 => 'l', 1 => 'r', $w => 'd', -$w => 'u');
    return '' unless grep {!$box{$_}} grep {$goal[$_]} 0 .. $#goal;    # solved before the first step
    while (@queue) {
        my ($at, $boxes, $path) = @{ shift @queue };
        my $column = $at % $w;
        for my $delta (-1, 1, $w, -$w) {
            next if $delta == -1 and $column == 0 or $delta == 1 and $column == $w - 1;
            my $to = $at + $delta;
            next if $to < 0 or !$free[$to];
            my %next = %$boxes;
            my $step = $letter{$delta};
            if ($next{$to}) {
                my $beyond = $to + $delta;
                next if $beyond < 0 or !$free[$beyond] or $next{$beyond};
                next if $delta == -1 and $to % $w == 0 or $delta == 1 and $to % $w == $w - 1;
                delete $next{$to};
                $next{$beyond} = 1;
                $step = uc $step;
                return $path . $step unless grep {!$next{$_}} grep {$goal[$_]} 0 .. $#goal;
            }
            my $k = $key->($to, \%next);
            next if exists $seen{$k};
            $seen{$k} = 1;
            push @queue, [$to, \%next, $path . $step];
        } ## end for my $delta (-1, 1, $w...)
    } ## end while (@queue)
    return undef;    # no solution
} ## end sub solve

# A solution LONGER than the shortest one in pushes, within $max_len letters
# (undef when there is none): a seed for a test of the optimal solver that
# must be bettered. The same search, over (position, depth) so that a longer
# way to a position is not thrown away, taking the first solution found with
# more pushes than $shortest has.
sub longer ($code, $shortest, $max_len) {
    my $want  = ($shortest =~ tr/A-Z//) + 1;
    my @rows  = split(/,/, $code, -1);
    my $w     = length $rows[0];
    my $cells = join('', @rows);
    my (@free, @goal, %box, $man);
    for my $cell (0 .. length($cells) - 1) {
        my $d = substr($cells, $cell, 1);
        $free[$cell] = 1     if $d ne '9' and $d ne '1';
        $goal[$cell] = 1     if $d eq '3' or $d eq '7' or $d eq '8';
        $box{$cell}  = 1     if $d eq '4' or $d eq '7';
        $man         = $cell if $d eq '5' or $d eq '6' or $d eq '8';
    }
    my $key    = sub ($man, $box, $depth) {join(',', $man, $depth, sort {$a <=> $b} keys %$box)};
    my %seen   = ($key->($man, \%box, 0) => 1);
    my @queue  = ([$man, {%box}, '']);
    my %letter = (-1 => 'l', 1 => 'r', $w => 'd', -$w => 'u');
    while (@queue) {
        my ($at, $boxes, $path) = @{ shift @queue };
        next if length $path >= $max_len;
        my $column = $at % $w;
        for my $delta (-1, 1, $w, -$w) {
            next if $delta == -1 and $column == 0 or $delta == 1 and $column == $w - 1;
            my $to = $at + $delta;
            next if $to < 0 or !$free[$to];
            my %next = %$boxes;
            my $step = $letter{$delta};
            if ($next{$to}) {
                my $beyond = $to + $delta;
                next if $beyond < 0 or !$free[$beyond] or $next{$beyond};
                next if $delta == -1 and $to % $w == 0 or $delta == 1 and $to % $w == $w - 1;
                delete $next{$to};
                $next{$beyond} = 1;
                $step = uc $step;
                if (!grep {!$next{$_}} grep {$goal[$_]} 0 .. $#goal) {
                    my $found = $path . $step;
                    return $found if ($found =~ tr/A-Z//) >= $want;
                    next;
                }
            }
            my $k = $key->($to, \%next, length($path) + 1);
            next if exists $seen{$k};
            $seen{$k} = 1;
            push @queue, [$to, \%next, $path . $step];
        } ## end for my $delta (-1, 1, $w...)
    } ## end while (@queue)
    return undef;
} ## end sub longer
1;
