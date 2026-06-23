# Vendored dependencies

These modules were previously pulled as hex packages (`aleppo`, `ast_walk`).
Upstream is unmaintained and does not build cleanly on modern OTP, so the
sources are vendored here and compiled as part of efene. rebar3 compiles every
`.erl`/`.yrl` under `src/` (including this directory) and runs yecc on the
grammar.

## aleppo (Apache-2.0)

- Origin: https://github.com/ErlyORM/aleppo — hex release `0.9.0`.
- `aleppo.erl` is unmodified. The legacy `erl_scan:token_info/2` call (removed
  in OTP 24) lives under `-ifdef(pre18)`; we simply do not define `pre18`, so
  the modern `erl_scan:symbol/1` branch is compiled. (Upstream's own
  rebar.config wrongly defined `pre18` because its `"^R|17"` regex matched the
  ERTS version string.)
- `aleppo_parser.yrl` is the grammar; the stale pre-generated `aleppo_parser.erl`
  is intentionally NOT vendored, so yecc regenerates it with the current OTP's
  parser prelude (no deprecated `erlang:get_stacktrace/0`).

## ast_walk (BSD-2-Clause, see ast_walk.LICENSE)

- Origin: https://github.com/marianoguerra/ast_walk — hex release `0.3.1`.
- One patch: the `file` attribute clause bound `_Line` twice in a single
  pattern (a warning since OTP 24); the inner one was renamed to `_Line1`.
