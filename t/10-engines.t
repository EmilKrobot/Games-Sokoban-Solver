# The four engines, all 27 modes, on the micro levels with a short limit: a
# set of allowed verdicts per mode, no death and no UNSOLVABLE on a solvable
# level, every SOLVED path replayed by two readings; a conveyor level so that
# CONVEYOR solves at least once.
use v5.42;
use Test::More;
use Games::Sokoban::Solver::Level  ();
use Games::Sokoban::Solver::Code   ();
use Games::Sokoban::Solver::Parser ();
use Games::Sokoban::Solver::Path   ();
use Games::Sokoban::Solver::Replay ();
use Games::Sokoban::Solver::Festival::Analysis ();
use Games::Sokoban::Solver::Fest::Analysis     ();
use Games::Sokoban::Solver::Firstbet  ();
use Games::Sokoban::Solver::FirstBack ();
use Games::Sokoban::Solver::Festival  ();
use Games::Sokoban::Solver::Fest      ();

my $LIMIT = 5;
for my $pkg ('Games::Sokoban::Solver::Firstbet', 'Games::Sokoban::Solver::FirstBack', 'Games::Sokoban::Solver::Festival') {
    no strict 'refs';
    ${"${pkg}::QUIET"} = 2;
}
$Games::Sokoban::Solver::Festival::BLOK_REPLACES = 1;
$Games::Sokoban::Solver::Fest::BLOK              = 1;

my @firstbet  = qw(PUSH_SCORE MOVE_SCORE PUSH_ASSIGN MOVE_SUM ROUTE FLOW ORDER BACKWARD CONVEYOR FEATURE);
my @festival  = Games::Sokoban::Solver::Festival::modes();
my @fest      = Games::Sokoban::Solver::Fest::modes();
is(scalar @festival, 8, 'Festival has eight modes');
is(scalar @fest,     8, 'Fest has eight modes');
is(scalar(@firstbet) + @festival + @fest + 1, 27, '27 modes in all');

# What a mode may answer on a small solvable level in five seconds. ORDER walks
# a restricted tree (GIVEUP when it is exhausted), CONVEYOR is inapplicable
# without a conveyor (NOCP), the pull-first modes of Festival and Fest may
# FAIL on a level their pull search cannot read; every other verdict is a
# defect.
my %allowed = (
    (map { $_ => { 'SOLVED' => 1 } } grep { $_ ne 'ORDER' and $_ ne 'CONVEYOR' } @firstbet),
    'ORDER'     => { 'SOLVED' => 1, 'GIVEUP' => 1 },
    'CONVEYOR'  => { 'SOLVED' => 1, 'NOCP' => 1 },
    'FIRSTBACK' => { 'SOLVED' => 1 },
    (map { $_ => { 'SOLVED' => 1, 'FAILED' => 1, 'TIMEOUT' => 1 } } @festival, @fest),
);

my @levels = do {
    open my $fh, '<', 't/data/micro.xsb' or die $!;
    my $text = do { local $/; <$fh> };
    close $fh;
    Games::Sokoban::Solver::Level::read($text);
};

# A conveyor: both boxes must go down the one corridor, to the two goals at
# its end.
my $conveyor = <<'XSB';
A conveyor
#########
#@      #
# $ $   #
####### #
####### #
#######.#
#######.#
#########
XSB
push @levels, Games::Sokoban::Solver::Level::read($conveyor);

my (%solved_by, %answers);
for my $level (@levels) {
    my ($code0, $code1) = Games::Sokoban::Solver::Level::normalize($level->{'rows'});
    my %code = Games::Sokoban::Solver::Code::prepare($code1);
    next if !@{ $code{'baggage'} };
    my %game = Games::Sokoban::Solver::Parser::parse(\%code);
    my $game_blob = Games::Sokoban::Solver::Parser::blob(\%game);
    my $fest      = Games::Sokoban::Solver::Festival::Analysis::parse($code{'code'}, 60);
    Games::Sokoban::Solver::Festival::Analysis::with_blok($fest, $game{'blok'});
    my $fest_blob     = Games::Sokoban::Solver::Festival::Analysis::freeze($fest);
    my $analysis_blob = Games::Sokoban::Solver::Fest::Analysis::analysis_record(Games::Sokoban::Solver::Fest::Analysis::prepare(\%game));
    note("$level->{'title'}: has_cp $game{'has_cp'}");
    $solved_by{'conveyor level has a conveyor'} = $game{'has_cp'} if $level->{'title'} eq 'A conveyor';

    my @runs = (
        (map { ['Games::Sokoban::Solver::Firstbet',  $game_blob,     $_] } @firstbet),
        ['Games::Sokoban::Solver::FirstBack', $game_blob, 'FIRSTBACK'],
        (map { ['Games::Sokoban::Solver::Festival', $fest_blob,     $_] } @festival),
        (map { ['Games::Sokoban::Solver::Fest',     $analysis_blob, $_] } @fest),
    );
    for my $run (@runs) {
        my ($pkg, $blob, $mode) = @$run;
        my @r = do {
            local *STDERR;
            open STDERR, '>', \my $junk;
            no strict 'refs';
            eval { &{"${pkg}::solve"}(1, $blob, $LIMIT, $mode) };
        };
        my $tag = "$level->{'title'}: $mode";
        unless (@r) { fail("$tag died: " . (split /\n/, "$@")[0]); next }
        my ($reason, $path) = @r;
        ok($allowed{$mode}{$reason}, "$tag: $reason is an allowed verdict");
        ++$answers{$mode}{$reason};
        next unless $reason eq 'SOLVED';
        ++$solved_by{$mode};
        is(Games::Sokoban::Solver::Replay::check($code{'code'}, $path), undef, "$tag: the path plays");
        my $again = eval { Games::Sokoban::Solver::Path::rebuilt(Games::Sokoban::Solver::Path::level($code{'code'}), 'path' => $path) };
        is($again, $path, "$tag: the path is already written from its pushes");
    }
}

ok($solved_by{'conveyor level has a conveyor'}, 'the conveyor level has a conveyor (has_cp)');
ok($solved_by{'CONVEYOR'}, 'CONVEYOR solved at least one level');
for my $mode (@firstbet, 'FIRSTBACK', @festival, @fest) {
    ok($solved_by{$mode}, "$mode solved at least one level" . ($solved_by{$mode} ? '' : " (answers: " . join(' ', map { "$_ $answers{$mode}{$_}" } sort keys %{ $answers{$mode} }) . ')'));
}

done_testing;
