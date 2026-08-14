# nla-16 parity harness (`tools/parity/`)

Site-for-site comparison of `by (nonlinear_arith)` closures between Z3
(tactus binary, default backend) and Lean (`--lean-backend` +
LeanNonlinearArith). Plan + decisions: `board/nla-16-plan.md`.

## Components

- `sites.py <crate-src-dir>` — scanner. Blanks comments/strings/chars,
  lexes `{`/`}`/`fn`, attributes each `nonlinear_arith` occurrence to
  its enclosing fn item. Emits CSV:
  `file,line,col,fn,fn_start,fn_end`.
- `harness.py <crate> <crate-src> --z3-log L --lean-log L [--csv OUT] [--summary]` —
  parses both run logs, merges onto the site table. Verdicts:
  `agree-closed`, `violation` (z3 closed / lean open — THE gate),
  `both-open-bisect`, `lean-better`.
- `run_pins.sh` — byte-exact pins for the `[nla16-stats]` channel
  (armed, default-off, wrong-value gate). In-repo substitute for
  in-file `#guard_msgs` pins, which can't set env vars on v4.25
  (no `IO.setEnv`).

## Run conventions (each crate, two runs, SERIAL — host ≤4-thread rule)

- z3 baseline (decision 1: same tactus binary, no `--lean-backend`):
  ```
  verus --num-threads 4 --crate-type=lib <crate>/src/lib.rs
  ```
  or, for raw cargo workspace crates:
  ```
  rustup run 1.94.0 env VERUS_ROOT=$PWD/.../tactus \
    cargo verus verify --manifest-path Cargo.toml -p <crate> -- \
    --num-threads 4
  ```
  Cargo-relevant args BEFORE `-p`, verus args after `--`
  (cargo-verus rejects `--manifest-path` after Verus-irrelevant args).
- lean (stats channel armed):
  ```
  export LEAN_PATH="$(cd tactus/lean-project && lake env printenv LEAN_PATH)"
  NLA16_STATS=1 verus --num-threads 4 --lean-backend \
    --crate-type=lib <crate>/src/lib.rs
  ```
- NO `-V cache` on canonical runs (per-fn caching skips lean
  elaboration → stats lines would go missing). Timing rule: `uptime`
  before trusting wall-clock anything; heartbeats only for verdicts.

## Log formats (Slice-0 recon, pinned by pilot)

- z3 failures at nonlinear sites: `error: assert_nonlinear_by: ...` with
  `--> path:line:col` span — per-site granularity directly.
- lean failures: `error: Lean tactic failed for <fn-name>:` — per-FN
  granularity; other lean errors carry spans attributed to enclosing
  fns (`lean_other_error` note).
- stats channel: `warning: [nla16-stats] layer=1|layer=2-prelude|layer=2 conflicts=K`
  at the fn's span; forwarded by verus because warning severity is the
  only class it reports on CheckResult::Success (verifier.rs:2489).
- summary: `verification results:: N verified, M errors` (fn-level).

## Known-attribution edges

- Path-dep crates verify their whole dep chain under cargo-verus
  (2dcs verifies algebra/linalg/geometry/rational/bigint/qext on the
  way); Slice-2 reports each crate from its OWN run only.
- Pre-existing z3-open regions exist (qext `axiom_non_square` ×9 —
  memory-confirmed pre-existing). Such sites can't be violations by
  construction; they're blank on the z3 side.
- Multi-site fns: z3 per-site, lean per-fn (decision 3 — bisect only
  on divergence).
