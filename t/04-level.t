# Level: the reading of a file, the digits of a level, the ring, every refusal.
use v5.42;
use Test::More;
use Games::Sokoban::Solver::Level ();

my $read      = \&Games::Sokoban::Solver::Level::read;
my $normalize = \&Games::Sokoban::Solver::Level::normalize;
my $as_text   = \&Games::Sokoban::Solver::Level::as_text;

# ---- read ------------------------------------------------------------------
{
    open my $fh, '<', 't/data/micro.xsb' or die "t/data/micro.xsb: $!";
    my $text = do { local $/; <$fh> };
    close $fh;
    my @levels = $read->($text);
    is(scalar @levels, 4, 'four levels in the fixture file');
    is_deeply([map { $_->{'index'} } @levels], [1, 2, 3, 4], 'indexed from 1');
    is_deeply([map { $_->{'title'} } @levels],
        ['One box, a corner to walk round', 'Two boxes side by side', 'One push', 'Three boxes in a room'],
        'the title before a level, a Title: line after one, and plain titles');
    is_deeply($levels[2]{'rows'}, ['#####', '#@$.#', '#####'], 'the rows of a level as written');
}
{
    my @levels = $read->("Title: first\r\n#-@\$.#\r\n\r\n\r\n#_@\$.#\r\n");
    is(scalar @levels, 2, 'CRLF lines, blank lines between levels');
    is($levels[0]{'title'}, 'first', 'a Title: line before a level names it');
    is($levels[1]{'title'}, 'Level 2', 'a level without a title is Level N');
    is($levels[0]{'rows'}[0], '# @$.#', '- is floor');
    is($levels[1]{'rows'}[0], '# @$.#', '_ is floor');
}
is_deeply([$read->("just words\nno level here\n")], [], 'a text without a level yields nothing');

# ---- normalize: a plain level ---------------------------------------------
{
    my ($code0, $code1, $info) = $normalize->(['#####', '#@$.#', '#####']);
    is($code0, '99999,95439,99999', 'code0 of a closed level');
    is($code1, $code0, 'code1 the same: nothing unreachable');
    is_deeply($info, {'w' => 5, 'h' => 3, 'nbox' => 1, 'ncell' => 3, 'ngoal' => 1, 'ring' => 0,
            'notes' => ['only 3 cells the player can reach: smaller than anything measured']},
        'the counts, and a note about a tiny level');
}

# ---- normalize: padding and the unreachable ---------------------------------
{
    my @rows = (
        '#######',
        '#@ $ .#',
        '#### ##',       # a pocket below the room ...
        '   # ##',       # ... reachable through the gap at column 4
        '   ####',
        '',              # a blank row is kept: unreachable floor, as zdroj had it
    );
    my ($code0, $code1, $info) = $normalize->(\@rows);
    is($info->{'w'}, 7, 'the width is the widest row');
    is($info->{'h'}, 6, 'every row counts, a blank one too');
    is($code0, '9999999,9504039,9999099,1119099,1119999,1111111', 'code0: unreachable floor becomes 1 (filler), the pocket is reachable');
    is($code1, '9999999,9504039,9999099,9999099,9999999,9999999', 'code1: unreachable floor becomes 9 (wall)');
    is($info->{'ncell'}, 7, 'ncell counts the reachable cells');
}

# ---- normalize: the ring -------------------------------------------------------
{
    my ($code0, $code1, $info) = $normalize->(['@$.']);
    is($info->{'ring'}, 1, 'an open level gets a ring');
    is($code1, '99999,95439,99999', 'the ring of walls round the whole rectangle');
    like($info->{'notes'}[0], qr/ring of walls/, 'the first note says so');
    is($info->{'w'}, 5, 'the width includes the ring');
}
{
    my ($code0, $code1, $info) = $normalize->(['#####', '#@$. ', '#####']);
    is($info->{'ring'}, 1, 'a level open on one side gets the ring too');
    is($code1, '9999999,9999999,9954309,9999999,9999999', 'the open side is closed by the ring, the row padded');
}
{
    my ($code0, $code1, $info) = $normalize->(['  #####  ', '  #@$.#  ', '  #####  ']);
    is($info->{'ring'}, 0, 'spaces outside the walls are not an open level');
    is($code0, '119999911,119543911,119999911', 'they are unreachable floor: filler in code0 ...');
    is($code1, '999999999,999543999,999999999', '... and walls in code1');
}

# ---- normalize: refusals ---------------------------------------------------------
sub refused ($rows, $like, $name) {
    my $ok = eval { $normalize->($rows); 1 };
    ok(!$ok, "$name: refused");
    like($@, $like, "$name: the sentence");
}
refused(['@$.', 'no wall'],        qr/not part of a level/,     'a character that is not part of a level');
refused(['   ', ' @ '],            qr/no box at all/,           'no box (and no wall: the ring made one)');
refused(['#####', '#  $.#', '#####'], qr/0 players/,            'no player');
refused(['#####', '#@@$.#', '#####'], qr/2 players/,            'two players');
refused(['#####', '#@$..#', '#####'], qr/1 boxes, 2 goals/,     'boxes and goals differ');
refused(['#####', '#@*  #', '#####'], qr/every box is already/, 'nothing to solve');

# ---- as_text -----------------------------------------------------------------------
is($as_text->('99999,95439,99999'), "#####\n#\@\$.#\n#####\n", 'digits back to text');
is($as_text->('11199,99869,99999'), "   ##\n##+\@#\n#####\n", 'fillers and avoid cells as floor, the player on a goal as +');

done_testing;
