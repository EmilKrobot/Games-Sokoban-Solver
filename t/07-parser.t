# Parser: the analysis of a level -- its keys, the push graph against the walk
# graph, the terminals, the blok source and its report, the blob, and that two
# builds of one level are the same.
use v5.42;
use Test::More;
use Compress::Zlib ();
use Storable       ();
use Games::Sokoban::Solver::Level  ();
use Games::Sokoban::Solver::Code   ();
use Games::Sokoban::Solver::Parser ();

my $parse = \&Games::Sokoban::Solver::Parser::parse;

sub code_of ($text) {
    my ($level) = Games::Sokoban::Solver::Level::read($text);
    my ($code0, $code1) = Games::Sokoban::Solver::Level::normalize($level->{'rows'});
    return { Games::Sokoban::Solver::Code::prepare($code1) };
}

# A room with two boxes and a wall tooth, so that the push graph has corners
# to prune and the patterns have bloks to find.
my $room = <<'XSB';
########
#  .   #
# $##$ #
#  @  .#
########
XSB

my @required = qw(code w h ncell nbox player baggage goal vzp vzu cm cmk cg blok
    has_wall has_corridor has_hole sols has_order order routes route distance steps
    distance_quad steps_quad maxp maxval maxp_steps maxval_steps has_cp c_path common_path to_goal);

{
    my $code = code_of($room);
    my %report;
    my %game = $parse->($code, 'report' => \%report);
    my @missing = grep { !exists $game{$_} } @required;
    is_deeply(\@missing, [], 'every key the engines read is there');
    my @gone = grep { exists $game{$_} } qw(gate has_gate homes avoid cells firststep md5);
    is_deeply(\@gone, [], 'the keys nothing reads are not');
    is($game{'nbox'}, 2, 'two boxes');
    is(scalar @{ $game{'goal'} }, 2, 'two goals');
    is($game{'vzp'}, 'C*', 'a small level packs positions in bytes');

    # the push graph: every push is between neighbours of the walk graph, from a
    # stance that is a cell, and cmk lists exactly the targets of cm
    my $bad = 0;
    for my $bx (keys %{ $game{'cm'} }) {
        my %targets = map { $_ => 1 } @{ $game{'cmk'}{$bx} };
        $bad++ unless join(',', sort keys %targets) eq join(',', sort keys %{ $game{'cm'}{$bx} });
        for my $t (keys %{ $game{'cm'}{$bx} }) {
            my $stance = $game{'cm'}{$bx}{$t};
            $bad++ unless grep { $_ == $t } @{ $game{'cg'}{$bx} };
            $bad++ unless $stance == 2 * $bx - $t and exists $game{'cg'}{$stance};
        }
    }
    is($bad, 0, 'the push graph is consistent with the walk graph');
    ok(scalar keys %{ $game{'sols'} } > 0, 'terminal positions exist');
    my ($one) = keys %{ $game{'sols'} };
    is_deeply([(unpack $game{'vzu'}, $one)[1 .. 2]], [sort { $a <=> $b } @{ $game{'goal'} }], 'a terminal has every box on a goal');

    # the bloks and the report
    ok($report{'patterns'} > 0, "patterns found ($report{'patterns'})");
    is($report{'blok_complete'}, 1, 'no budget: every pattern complete');
    is(scalar @{ $report{'blok'} }, $report{'patterns'}, 'one report row per pattern');
    ok(!grep({ $_->[2] < $_->[1] } @{ $report{'blok'} }), 'k_done reaches kmax everywhere');
    is_deeply([sort keys %{ $report{'seconds'} }], ['blok', 'graph', 'rest'], 'the seconds of three stages');
    my $vectors = 0;
    my $strings = 0;
    for my $bx (keys %{ $game{'blok'} }) {
        for my $t (keys %{ $game{'blok'}{$bx} }) {
            ok(exists $game{'cm'}{$bx}{$t}, "blok $bx->$t is a push of the graph") if $vectors == 0;
            for my $v (@{ $game{'blok'}{$bx}{$t} }) { ++$vectors; ++$strings if !ref $v and length $v }
        }
    }
    is($strings, $vectors, "every blok is a non-empty bit string ($vectors)");
    ok($vectors > 0, 'this room has bloks');

    # the blob round trip, and a second build equal to the first
    my $blob = Games::Sokoban::Solver::Parser::blob(\%game);
    my $back = Storable::thaw(Compress::Zlib::uncompress($blob));
    is_deeply($back, \%game, 'blob() comes back as the analysis');
    my %again = $parse->($code);
    is_deeply(\%again, \%game, 'two builds of one level are the same');
    is_deeply($code, code_of($room), 'the Code record was not changed by parse');
}

# The blok source is the caller's: its strings become the vectors, its rows the
# report; an empty answer gives no bloks and an incomplete table.
{
    my $code = code_of($room);
    my @asked;
    my $source = sub ($patlist, %opt) {
        push @asked, [scalar keys %$patlist, $opt{'nbox'}, $opt{'deadline'}];
        return ({}, [map { [$_, 1, 0, 0, 0] } sort keys %$patlist]);
    };
    my %report;
    my %game = $parse->($code, 'blok_source' => $source, 'blok_budget' => 5, 'report' => \%report);
    is(scalar @asked, 1, 'the source was asked once');
    is($asked[0][1], 2, 'with the number of boxes');
    ok(defined $asked[0][2] && $asked[0][2] > 0, 'and an absolute deadline');
    is_deeply($game{'blok'}, {}, 'no strings, no bloks');
    is($report{'blok_complete'}, 0, 'a cut row makes the table incomplete');

    @asked = ();
    %game  = $parse->($code, 'blok_source' => $source, 'blok_budget' => 0, 'report' => \%report);
    is(scalar @asked, 0, 'budget 0: the source is not asked');
    is_deeply($game{'blok'}, {}, 'and there are no bloks');
    is($report{'blok_complete'}, 0, 'and the table is not complete');
    ok($report{'patterns'} > 0, 'patterns are counted all the same');
    ok(scalar keys %{ $report{'patpoz'} } > 0, 'and patpoz names the pattern of every push');

    # a source handing a string back is believed: one set of one free cell of the
    # window per pattern (a cell outside the level is a wall in the window and
    # could never be in a blok)
    my $any = sub ($patlist, %opt) {
        return ({ map { $_ => index($_, '0') } keys %$patlist }, [map { [$_, 1, 1, 1, 0] } keys %$patlist]);
    };
    %game = $parse->($code, 'blok_source' => $any, 'report' => \%report);
    ok(scalar keys %{ $game{'blok'} } > 0, 'the strings of the source are the bloks');
    is($report{'blok_complete'}, 1, 'and rows done to kmax make it complete');

    my $ok = eval { $parse->($code, 'blok_source' => sub { return 'no' }); 1 };
    like($@, qr/must return/, 'a source returning nonsense is refused');
    $ok = eval { $parse->('99999,95439,99999'); 1 };
    like($@, qr/hash reference/, 'parse wants the Code record, not a board');
}

# The fixture levels all parse, and every push of each lies in its walk graph.
{
    open my $fh, '<', 't/data/micro.xsb' or die $!;
    my $text = do { local $/; <$fh> };
    close $fh;
    for my $level (Games::Sokoban::Solver::Level::read($text)) {
        my ($code0, $code1) = Games::Sokoban::Solver::Level::normalize($level->{'rows'});
        my %game = $parse->({ Games::Sokoban::Solver::Code::prepare($code1) });
        is($game{'nbox'}, scalar @{ $game{'goal'} }, "$level->{'title'}: as many boxes as goals");
        ok(scalar keys %{ $game{'sols'} } > 0, "$level->{'title'}: has a terminal");
    }
}

done_testing;
