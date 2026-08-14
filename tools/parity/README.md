# nla-16 parity harness (`tools/parity/`)

Site-for-site comparison of `by (nonlinear_arith)` closures between Z3
(tactus binary, default backend) and Lean (`--lean-backend` +
LeanNonlinearArith). Plan + decisions: `board/nla-16-plan.md`.
Slice-0 close-out: `board/nla-16-slice-0-mechanics.md`.

## Components

- `sites.py <crate-src-dir>` — scanner. Blanks comments/strings/chars,
  lexes `{`/`}`/`fn`, attributes each `nonlinear_arith` occurrence to
  its enclosing fn item. Emits CSV:
  `file,line,col,fn,fn_start,fn_end`. (Comment blanking is LOAD-BEARING:
  the pre-implementation grep census counted comment mentions — qext's
  one "site" was prose; true corpus 15 crates/~2,595 sites.)
- `harness.py <crate> <crate-src> --z3-log L --lean-log L [--csv OUT] [--summary]` —
  parses both run logs, merges onto the site table. Verdicts:
  `agree-closed`, `violation` (z3 closed / lean open — THE gate),
  `both-open-bisect`, `lean-better`. Lean-fn attribution is
  NAME+FILE (bare-name matching gives same-name false positives —
  axiom_le_mul_nonneg_monotone exists in two files; the `at <src>:l:c:`
  inner diagnostic line is the disambiguator).
- `posthoc.py <crate-src> <tactus-lean-lib-dir> --out-csv O` — THE
  layer-attribution mechanism. Re-elaborates per-fn pkg modules with
  `NLA16_STATS=1` (sequential; cache-keyed on content+prelude), parses
  `[nla16-stats]` warnings to per-obligation rows mapped to rust spans
  via the `@rust:` comments in the pkg text. Required because verus
  DROPS warning diagnostics on green runs (sorry-filtered path) — the
  stats can NOT travel through the verus log on success; post-hoc is
  the channel.
- `run_crate.sh <crate> <z3|lean>` — serialized runs (lockfile; host
  ≤4-thread rule).
- `run_pins.sh` + `pins/` — byte-exact stats-channel pins
  (armed / default-off / wrong-value gate). Subprocess pins because
  v4.25 has no `IO.setEnv` (in-file `#guard_msgs` can't vary env).

## Run conventions (each crate, two runs, SERIAL)

z3 baseline (decision 1: same tactus binary, NO `--lean-backend`;
`--lean-all-proofs` is gone since e5f7aea):
```
verus --num-threads 4 --crate-type=lib <crate>/src/lib.rs
```
or raw cargo workspace crates:
```
rustup run 1.94.0 env VERUS_ROOT=$PWD/../tactus \
  cargo verus verify --manifest-path Cargo.toml -p <crate> -- \
  --num-threads 4 --lean-backend      # drop --lean-backend for z3
```
Cargo args BEFORE `-p`; verus args after `--` (cargo-verus rejects the
reverse order). NO `-V cache` on canonical runs (pkg cross-run cache
skips re-elaboration — closed verdicts stand, but stats can't be
reharvested from cached runs).

Post-hoc:
```
export LEAN_PATH=<prelude-hash-dir>:<lib-dir>:$(cd tactus/lean-project && lake env printenv LEAN_PATH)
NLA16_STATS=1 lean <lib-dir>/pkg/<module>.lean
```
The prelude dir: `~/.cache/tactus/prelude-<hash>` with a compatible
`TactusDefs.olean` ROOT (module-prefix resolution needs it);
`posthoc.py` auto-probes by mtime-descending with an import test.
Leaved artifacts: mirror runs write to `$WORKSPACE/target/tactus-lean/lib/pkg/`;
raw cargo-verus runs write to the CRATE's own `target/tactus-lean/<stem>/pkg/`.

## Log formats (Slice-0 recon + pilot, pinned)

- z3 failures at nonlinear sites: `error: assert_nonlinear_by: ...` +
  `--> path:line:col` — per-site.
- lean failures: `error: Lean tactic failed for <fn>:` per OBLIGATION
  (multiple per fn), with inner `at <src>:l:c:` inner-diagnostic lines
  and trailing `-->` arrows.
- summary: `verification results:: N verified, M errors` (fn-level).
- stats channel: `warning: [nla16-stats] layer=1|layer=2-prelude|layer=2 conflicts=K`
  (post-hoc: at pkg-module positions mapped to rust spans).

## Known-attribution edges

- Path-dep crates verify their whole dep chain under cargo-verus;
  report each crate from its OWN run only.
- Pre-existing z3-open regions exist (qext `axiom_non_square` ×9 —
  memory-confirmed baseline, not signal): such sites can't be
  violations by construction.
- pkg module elaboration stops at its first error → post-hoc stats for
  a FAILING module are partial (closes before the error only).
- Multi-site fns: z3 per-site, lean per-fn (decision 3 — bisect only
  on divergence). Arm-bisection recipe validated in the pilot: copy
  the pkg module, `s/nonlinear_arith/fail/` (a meta tactic that
  always fails), elaborate — isolates the arm as whnf/budget sink.
