# Console: the lines and the percentage; Memory: the probe, with and without
# the optional Windows modules.
#
# The Win32 modules are made unavailable BEFORE the two modules load, by a hook
# at the head of @INC that refuses them: that is the path a machine without
# them takes (every Linux box, a Windows perl without Win32::API), and it must
# give plain lines and a memory net that is off, never a death.
use v5.42;
use Test::More;
use Config;

BEGIN {
    unshift @INC, sub ($self, $file) {
        die "the test makes $file unavailable\n" if $file =~ m{\AWin32/};
        return;
    };
}

use Games::Sokoban::Solver::Console ('backline', 'backlinen', 'console_width', 'fit_line', 'podil');
use Games::Sokoban::Solver::Memory ('used_gb', 'total_gb', 'scope');

# ---- Console -------------------------------------------------------------
is(console_width(), 0, 'no Win32::Console: the width is not known (0)');

is(fit_line('short', 10), 'short',          'a line that fits is left alone');
is(fit_line('abcdef', 3), "abc\e[0m",       'a line that does not fit is cut and ends with a colour reset');
is(fit_line("\e[31mred\e[0m plain", 3), "\e[31mred\e[0m\e[0m", 'colour sequences take no room and are kept whole');
is(fit_line("\e[1mab\e[0m", 5), "\e[1mab\e[0m", 'a coloured line that fits is left alone');

{
    my $out = '';
    {
        local *STDERR;
        open STDERR, '>', \$out or die $!;
        backline('transient');
        backlinen('durable');
        close STDERR;
    }
    like($out, qr/\A\r\s*\rtransient/, 'a transient line starts with a carriage return (width unknown: padded)');
    like($out, qr/durable\n\z/,         'a durable line ends with a newline');
    unlike($out, qr/\e\[K/,             'no erase sequence when the width is not known');
}

is(podil(50, 200),     '  25.0%', 'one decimal above one per cent');
is(podil(1, 200),      '  0.50%', 'two decimals below one per cent');
is(podil(1, 20000),    ' 0.005%', 'three decimals below a hundredth');
is(podil(1, 3, 2),     ' 33.33%', 'the decimals can be given');
is(podil(0, 5),        '     0%', 'no number');
is(podil(3, 0),        '    N/A', 'no base');
is(length podil(7, 7), 7,         'seven characters wide');

# ---- Memory, with the probe refused --------------------------------------
{
    my $warned = '';
    local $SIG{__WARN__} = sub { $warned .= $_[0] };
    is(scope(),    'none', 'no probe: scope none');
    is(used_gb(),  0,      'no probe: used_gb is 0, not undef');
    is(total_gb(), 0,      'no probe: total_gb is 0');
    like($warned, qr/memory net is off/, 'said once on STDERR');
    $warned = '';
    used_gb();
    is($warned, '', 'said only once');
}

# ---- Memory, in a fresh perl with the modules it has -----------------------
{
    my $out = `"$^X" -Ilib -MGames::Sokoban::Solver::Memory -e "print join(' ', Games::Sokoban::Solver::Memory::scope(), Games::Sokoban::Solver::Memory::used_gb(), Games::Sokoban::Solver::Memory::total_gb())" 2>&1`;
    like($out, qr/\A(?:system|none) \d+(?:\.\d+)? \d+(?:\.\d+)?\s*\z/m, "a fresh perl answers numbers ($out)");
    my ($scope, $used, $total) = split ' ', (grep { /\A(?:system|none) / } split /\n/, $out)[0] // '';
    if (($scope // '') eq 'system') {
        cmp_ok($total, '>', 0,      'system scope: the machine has memory');
        cmp_ok($used,  '>', 0,      'system scope: some of it is in use');
        cmp_ok($used,  '<=', $total, 'system scope: used is not more than total');
    }
    else {
        pass('this machine has no probe; the fresh perl said so');
        pass('(no total to compare)');
        pass('(no used to compare)');
    }
}

done_testing;
