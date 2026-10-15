# Fest::Analysis: the record of a level for the Fest engine -- its stamp and
# keys, the pattern library found, the packed form, and two builds alike.
use v5.42;
use Test::More;
use Compress::Zlib ();
use Storable       ();
use Games::Sokoban::Solver::Level  ();
use Games::Sokoban::Solver::Code   ();
use Games::Sokoban::Solver::Parser ();
use Games::Sokoban::Solver::Fest::Analysis ();

my $room = <<'XSB';
########
#  .   #
# $##$ #
#  @  .#
########
XSB

sub game_of ($text) {
    my ($level) = Games::Sokoban::Solver::Level::read($text);
    my ($code0, $code1) = Games::Sokoban::Solver::Level::normalize($level->{'rows'});
    return { Games::Sokoban::Solver::Parser::parse({ Games::Sokoban::Solver::Code::prepare($code1) }) };
}

my $game   = game_of($room);
my $record = Games::Sokoban::Solver::Fest::Analysis::prepare($game);
is(ref $record, 'HASH', 'prepare returns the record');
is($record->{'stamp'}, 'fest record 2', 'stamped as the engine expects');
is($record->{'stamp'}, $Games::Sokoban::Solver::Fest::Analysis::ANALYSIS_STAMP, '... which is the module stamp');
my @keys = qw(blok cg cm floor goal start sok0 width cp d goal_hole impossible n n8 pattern pattern_at
    room room_area side tunnel_pull tunnel_push walk wall mpdb pull_mpdb envelope snail
    blocks goals_away goals_near girl_context room_links0);
my @missing = grep { !exists $record->{$_} } @keys;
is_deeply(\@missing, [], 'every key of the record is there');
is(scalar keys %$record, scalar(@keys) + 1, 'and nothing else');
is_deeply($record->{'cm'},   $game->{'cm'},   'the push graph is the Parser\'s');
is_deeply($record->{'blok'}, $game->{'blok'}, 'the blok table too');
is_deeply([sort { $a <=> $b } keys %{ $record->{'goal'} }], [sort { $a <=> $b } @{ $game->{'goal'} }], 'the goals as a set');
is($record->{'sok0'}, $game->{'player'}, 'the player');
is($record->{'width'}, $game->{'w'}, 'the width');
ok(scalar keys %{ $record->{'wall'} } > 0, 'walls round the floor');
ok(ref $record->{'pattern_at'} eq 'HASH', 'the deadlock pattern library was laid over the level');
ok(ref $record->{'snail'} eq 'HASH' && exists $record->{'snail'}{'kind'}, 'the chain verdict has a kind');

# the packed form the engine takes
my $blob = Games::Sokoban::Solver::Fest::Analysis::analysis_record($record);
my $back = Storable::thaw(Compress::Zlib::uncompress($blob));
is_deeply($back, $record, 'analysis_record packs the record and nothing else');

# two builds alike, and the hash handed in not changed
my $again = Games::Sokoban::Solver::Fest::Analysis::prepare($game);
is_deeply($again, $record, 'two builds of one level are the same');
is_deeply($game, game_of($room), 'prepare does not change the Parser\'s hash');

# a level after another level: the record of the first again, not a mixture
{
    open my $fh, '<', 't/data/micro.xsb' or die $!;
    my $text = do { local $/; <$fh> };
    close $fh;
    my @levels = Games::Sokoban::Solver::Level::read($text);
    for my $level (@levels) {
        my ($c0, $c1) = Games::Sokoban::Solver::Level::normalize($level->{'rows'});
        my $g = { Games::Sokoban::Solver::Parser::parse({ Games::Sokoban::Solver::Code::prepare($c1) }) };
        my $r = eval { Games::Sokoban::Solver::Fest::Analysis::prepare($g) };
        ok($r && $r->{'stamp'}, "$level->{'title'}: prepared" . ($r ? '' : " ($@)"));
    }
    is_deeply(Games::Sokoban::Solver::Fest::Analysis::prepare($game), $record, 'the room again after the fixtures: the same record');
}

done_testing;
