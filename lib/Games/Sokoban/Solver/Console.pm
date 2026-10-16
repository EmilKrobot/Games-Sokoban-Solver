package Games::Sokoban::Solver::Console;

# The console lines of the engines, in one place: a TRANSIENT progress line that
# the next line overwrites, a DURABLE line that stays, the width of the window
# the lines are shown in, and the percentage column of the progress lines.
#
# The two kinds of line are the engines' console discipline: transient progress
# uses backline (it may flicker and is taken back), a per-game or summary line
# uses backlinen (it clears the transient line first and stays), so that the
# scrollback at the end reads as if the transient lines had never been there.
#
# Lineage: Handy.pm of the Sokoban project (console_width, fit_line, backline,
# backlinen, podil), the only six of its seventy names the engines use.
use v5.42;
use Exporter 'import';
our @EXPORT_OK = ('backline', 'backlinen', 'console_width', 'fit_line', 'podil');
our $VERSION   = '0.01';

# On Windows the colour sequences of Term::ANSIColor reach an older console only
# through Win32::Console::ANSI (the modern terminal reads them natively).
# Optional: loaded once, here, inside an eval, never by an engine.
if ($^O eq 'MSWin32') {eval {require Win32::Console::ANSI; Win32::Console::ANSI->import; 1}}
my $lenback = 0;    # the longest transient line printed so far, for a console whose width is not known

# The width of the window STDERR is shown in, or 0 when STDERR is not a console
# (a file, a pipe) or the width cannot be asked. Asked at every call, because
# the window can be resized while a run is under way. The two low-level calls
# are used on purpose: a Win32::Console OBJECT closes its handle when it is
# destroyed, and a thread's clone of it would close STDERR for the whole
# process when the thread ends.
sub console_width () {
    return 0 unless $^O eq 'MSWin32';
    state $ok = eval {require Win32::Console; 1} // 0;
    return 0 unless $ok;
    my @info = Win32::Console::_GetConsoleScreenBufferInfo(Win32::Console::_GetStdHandle(Win32::Console::STD_ERROR_HANDLE()));
    return 0 unless @info >= 9;
    return $info[7] - $info[5] + 1;    # right - left of the visible window
}

# $string cut to at most $width visible characters. Colour sequences take no
# room on the screen and are kept whole; a cut line ends with a colour reset.
sub fit_line ($string, $width) {
    my ($out, $room) = ('', $width);
    foreach my $part (split /(\e\[[0-9;]*[A-Za-z])/, $string) {
        if ($part =~ /^\e\[/) {$out .= $part; next}
        if (length($part) <= $room) {$out .= $part; $room -= length($part); next}
        return $out . substr($part, 0, $room) . "\e[0m";
    }
    return $out;
}

# A TRANSIENT line: the next backline/backlinen overwrites it. It must never
# reach the right edge of the window -- a wrapped line cannot be taken back
# with "\r", which returns to the start of its LAST row only -- so on a console
# it is cut to the window's width less one.
sub backline ($string) {
    my $width = console_width();
    if ($width > 1) {
        $string = fit_line($string, $width - 1) if $string !~ /\n/;
        print {*STDERR} "\r\e[K" . $string;
        return;
    }
    my $ls = $string =~ tr/a-zA-Z0-9\ \n\t,.:%!?;_\-\=\+\\\|\*//;
    $lenback = $ls if $ls > $lenback;
    print {*STDERR} "\r" . (' ' x $lenback) . "\r" . $string;
    return;
}

# A DURABLE line: it clears the transient line before it and stays.
sub backlinen ($string) {
    if (console_width() > 1) {
        print {*STDERR} "\r\e[K" . $string . "\n";
        return;
    }
    backline($string);
    print {*STDERR} "\n";
    return;
}

# $number as a percentage of $base, right-aligned in seven characters, with one
# decimal above one per cent, two above a hundredth, three below; $deci fixes
# the decimals. 'N/A' with no base, '0%' with no number.
sub podil ($number, $base, $deci = undef) {
    return '    N/A' unless $base;
    return '     0%' unless $number;
    my $pd = 100 * ($number / $base);
    unless (defined $deci) {
        $deci = 1;
        $deci = 2 unless $pd > 1.0;
        $deci = 3 unless $pd > 0.01;
    }
    return sprintf("%6.0${deci}f%%", $pd);
}
1;
__END__

=head1 NAME

Games::Sokoban::Solver::Console - the progress lines of the engines

=head1 SYNOPSIS

    use Games::Sokoban::Solver::Console ('backline', 'backlinen', 'podil');

    backline("searching ... $positions positions");   # overwritten by the next line
    backlinen("SOLVED in $seconds s");                 # stays in the scrollback
    my $share = podil($open, $max);                    # '  12.5%'

=head1 DESCRIPTION

The engines of this distribution report on STDERR in two kinds of line. A
B<transient> line shows progress and is taken back by the next line; a
B<durable> line carries a fact (a solve ended, a record improved) and stays.
Printed in that discipline, the scrollback at the end of a run reads as if the
transient lines had never been there.

A transient line must never reach the right edge of the window, because a line
that wrapped cannot be taken back with a carriage return; so on a console whose
width can be asked it is cut to the width less one, colour sequences kept whole.
Where the width is not known (STDERR is a file or a pipe, or the system has no
way to ask) the line is overwritten by padding it with spaces to the longest
transient line printed so far.

=head1 FUNCTIONS

Nothing is exported by default; ask for the names.

=over 4

=item backline STRING

Print STRING on STDERR as a transient line.

=item backlinen STRING

Clear the transient line and print STRING on STDERR as a durable line, with a
newline.

=item console_width

The width of the window STDERR is shown in, or 0 when it is not known. Asked on
Windows through L<Win32::Console> when that module is installed; 0 elsewhere.

=item fit_line STRING, WIDTH

STRING cut to at most WIDTH visible characters; colour sequences take no room
and a cut line ends with a colour reset.

=item podil NUMBER, BASE, [DECIMALS]

NUMBER as a percentage of BASE, right-aligned in seven characters: C<'  25.0%'>.
The decimals are chosen by the size of the percentage unless given.
C<'    N/A'> when BASE is zero, C<'     0%'> when NUMBER is.

=back

=head1 AUTHOR

Jiri Broz, E<lt>jiri.krobot.broz@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2026 by Jiri Broz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.42.2 or,
at your option, any later version of Perl 5 you may have available.

=cut
