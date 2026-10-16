# Festival::Analysis: a level analysed, the two fuses reported and not fatal,
# the blok table copied in, the frozen form and what thaw refuses.
use v5.42;
use Test::More;
use Games::Sokoban::Solver::Level              ();
use Games::Sokoban::Solver::Code               ();
use Games::Sokoban::Solver::Parser             ();
use Games::Sokoban::Solver::Festival::Analysis ();
my $FA   = 'Games::Sokoban::Solver::Festival::Analysis';
my $room = <<'XSB';
########
#  .   #
# $##$ #
#  @  .#
########
XSB
my ($level) = Games::Sokoban::Solver::Level::read($room);
my ($code0, $code1) = Games::Sokoban::Solver::Level::normalize($level->{'rows'});
my %code = Games::Sokoban::Solver::Code::prepare($code1);
my %game = Games::Sokoban::Solver::Parser::parse(\%code);

# ---- the analysis of a small level ----------------------------------------
my $fest = Games::Sokoban::Solver::Festival::Analysis::parse($code{'code'}, 60);
is(ref $fest,        'HASH',                                               'parse returns a hash');
is($fest->{'stamp'}, $Games::Sokoban::Solver::Festival::Analysis::STAMP,   'stamped');
is($fest->{'ver'},   $Games::Sokoban::Solver::Festival::Analysis::VERSION, 'with the module version');
like($fest->{'key'}, qr/\A\d+:/, 'the key starts with the row width');
is($fest->{'hotspots_incomplete'},  0, 'a minute is enough for the hotspots of a tiny level');
is($fest->{'envelopes_incomplete'}, 0, 'and for its envelopes');
ok(!exists $fest->{'blok'}, 'no blok key until with_blok');
my @some = grep {exists $fest->{$_}} qw(index_to_p width height patterns mpdb_list pull_mpdb_list envelope);
ok(@some >= 4, "the maps are there (@some)");

# ---- the fuses: a budget already spent fires both at once ----------------------
# The envelope analysis runs only on a level whose floor a box on a goal splits
# in two (two corrals in reverse mode): the room has one corral, so its flag
# stays 0 whatever the budget; the corridor below has two.
{
    my $spent = Games::Sokoban::Solver::Festival::Analysis::parse($code{'code'}, -1);
    is($spent->{'hotspots_incomplete'},  1,                'no budget: the hotspot table was thrown away, and the hash says so');
    is($spent->{'envelopes_incomplete'}, 0,                'the room has one corral: no envelope analysis to cut');
    is($spent->{'stamp'},                $fest->{'stamp'}, 'the hash is still a complete analysis of the level');
    ok(Games::Sokoban::Solver::Festival::Analysis::freeze($spent), 'and freeze accepts it');
    my ($corridor) = Games::Sokoban::Solver::Level::read("########\n#\@ \$. ##\n########\n");
    my ($k0, $k1) = Games::Sokoban::Solver::Level::normalize($corridor->{'rows'});
    my %k   = Games::Sokoban::Solver::Code::prepare($k1);
    my $two = Games::Sokoban::Solver::Festival::Analysis::parse($k{'code'}, -1);
    is($two->{'envelopes_incomplete'}, 1, 'two corrals and no budget: the envelope analysis stopped, and the hash says so');
    is($two->{'hotspots_incomplete'},  1, '... the hotspots too');
    is(Games::Sokoban::Solver::Festival::Analysis::parse($k{'code'}, 60)->{'envelopes_incomplete'},
        0, 'with a minute it finishes');

    # the next level analysed in the same process starts with the fuses reset
    my $again = Games::Sokoban::Solver::Festival::Analysis::parse($code{'code'}, 60);
    is($again->{'hotspots_incomplete'} + $again->{'envelopes_incomplete'}, 0, 'the fuses are reset for the next level');
}

# ---- with_blok ---------------------------------------------------------------------
{
    my $with = Games::Sokoban::Solver::Festival::Analysis::with_blok($fest, $game{'blok'});
    is($with, $fest, 'with_blok returns the hash it was given');
    is_deeply($fest->{'blok'}, $game{'blok'}, 'the Parser blok table, copied');
    my ($bx) = keys %{ $game{'blok'} };
    my ($t)  = keys %{ $game{'blok'}{$bx} };
    push @{ $game{'blok'}{$bx}{$t} }, 'spoiled';
    isnt(scalar @{ $fest->{'blok'}{$bx}{$t} }, scalar @{ $game{'blok'}{$bx}{$t} }, 'a copy, not an alias');
    pop @{ $game{'blok'}{$bx}{$t} };
    ok(!eval {Games::Sokoban::Solver::Festival::Analysis::with_blok($fest, []); 1}, 'a blok table must be a hash');
}

# ---- freeze and thaw ---------------------------------------------------------------
{
    my $blob = Games::Sokoban::Solver::Festival::Analysis::freeze($fest);
    ok(length $blob > 100, 'frozen');
    my $back = Games::Sokoban::Solver::Festival::Analysis::thaw($blob);
    is_deeply($back, $fest, 'thaw gives the hash back, blok included');
    ok(!eval {Games::Sokoban::Solver::Festival::Analysis::thaw(''); 1}, 'thaw refuses an empty string');
    like($@, qr/empty/, '... and says so');
    ok(!eval {Games::Sokoban::Solver::Festival::Analysis::thaw('not a blob at all'); 1}, 'thaw refuses garbage');
    like($@, qr/corrupt/, '... and says so');
    my %other = (%$fest, 'stamp' => 'fest-analysis-0');
    my $wrong = Games::Sokoban::Solver::Festival::Analysis::freeze(\%other);
    ok(!eval {Games::Sokoban::Solver::Festival::Analysis::thaw($wrong); 1}, 'thaw refuses another stamp');
    like($@, qr/stamped 'fest-analysis-0'/, '... naming it');
    ok(!eval {Games::Sokoban::Solver::Festival::Analysis::freeze({ 'stamp' => 'x' }); 1}, 'freeze wants a key');
}

# ---- every fixture level analyses -------------------------------------------------
{
    open my $fh, '<', 't/data/micro.xsb' or die $!;
    my $text = do {local $/; <$fh>};
    close $fh;
    for my $level (Games::Sokoban::Solver::Level::read($text)) {
        my ($c0, $c1) = Games::Sokoban::Solver::Level::normalize($level->{'rows'});
        my %c = Games::Sokoban::Solver::Code::prepare($c1);
        my $f = eval {Games::Sokoban::Solver::Festival::Analysis::parse($c{'code'}, 60)};
        ok($f && $f->{'key'}, "$level->{'title'}: analysed" . ($f ? '' : " ($@)"));
    }
}
done_testing;
