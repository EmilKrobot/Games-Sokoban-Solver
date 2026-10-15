# CLAUDE.md -- Games-Sokoban-Solver

This tree is the CPAN distribution of the solver pipeline of the Sokoban
project (`C:\Workspace\Sokoban`). It is worked on from a session of THAT
project with this directory added, so the project's `CLAUDE.md` and its
`pravidla` skill apply here in full: load the `pravidla` skill first, edit
files with the editor and never by a script, comments in English ASCII,
`use v5.42`, POD per perlmodstyle, gates that can fire.

The plan this tree is built by:
`C:\Users\jirik\.claude\plans\p-iprav-me-si-pl-n-fin-ln-validated-hippo.md`
(module map, interfaces, the hard parts, the steps with their gates). The
memory `project_distribution` says where the work stands.

## The two rules of this tree

- **PERL5LIB is empty for every test and gate here.** The Sokoban project's
  `lib/` sits on PERL5LIB and holds `Games/Sokoban/Solver.pm` (the project's
  optimal solver, not this distribution's facade) and the originals of every
  module copied here. With PERL5LIB set, a module this tree forgot would be
  found there silently. So: `$env:PERL5LIB=''; prove -l t` and
  `perl -Ilib ...`; `xt/lib/Gate.pm` dies when PERL5LIB is set. The one
  exception is the two gates REUSED from `C:\Workspace\Sokoban\ai`
  (`eq_fest_promote.pl --module Solver::Festival`, `eq_path_rebuilt.pl
  --module Solver::X`): they run from the Sokoban tree with PERL5LIB as it is
  plus `-IC:/Workspace/Games-Sokoban-Solver/lib`.
- **The Sokoban tree is never written from here.** Files are COPIED out of it
  and edited in this tree; its databases (`D:\Sokoban_data\db\Sokoban.sqlite3`,
  `Patterns.sqlite3`) are opened read-only by the gates in `xt/` and never by
  the distribution itself.

## Layout

- `lib/Games/Sokoban/Solver.pm` -- the facade; `lib/Games/Sokoban/Solver/*` --
  the modules; `lib/Games/Sokoban/Solver/Data/*.stor` -- the data tables.
- `bin/soko-solver.pl` -- the program.
- `t/` -- tests that ship: no database, hand-made micro levels, under two
  minutes. `xt/` -- author gates against the Sokoban database (not in the
  MANIFEST); `xt/lib/Gate.pm` is their common kit. `maint/` -- maintenance.
- Perl is `C:/Strawberry/perl/bin/perl.exe`, make is `C:\Strawberry\c\bin\gmake.exe`.
- Line endings are LF in the working tree too (`.gitattributes`): the tarball
  goes to Linux.
