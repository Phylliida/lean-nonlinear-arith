## nla-16 Slice 0 `WIP` (2026-08-14 eve) — harness mechanics + pilot cohort

### What landed

- **`tools/parity/`** (repo-local; commits `3d8f1d8`, `549ae30`):
  - `sites.py` — nonlinear-site scanner. Blanks comments/strings/chars
    (offset-preserving), rough Rust lexer (nested block comments, raw
    strings, char-vs-lifetime), attributes each site to its enclosing
    `fn`. Comments blanking matters: the pre-implementation grep
    census counted MENTIONS — qext's one "site" was a prose comment
    about Z3's `by(nonlinear_arith)` limitation (true count 0).
    **Corpus re-censused: 15 crates, ~2,595 sites** (was: 16/~2,613).
    Plan doc corrected.
  - `harness.py` — log parser + merger → per-site CSV
    (`crate,file,line,fn,z3,lean,verdict,layers,notes`) with verdicts
    `agree-closed / VIOLATION / both-open-bisect / lean-better`; the
    `layers` column carries the stats channel; `z3_other_error` /
    `lean_other_error` notes mark non-nonlinear failures.
  - `run_crate.sh` — per-crate pair runner (raw cargo-verus + mirror
    direct-verus paths; a lockfile SERIALIZES runs — the ≤4-thread
    host rule: `NLA16_STATS=1` armed for lean runs, no `-V cache`).
  - `run_pins.sh` + `pins/` — subprocess pins (see stats channel).
  - `README.md` — conventions + log formats + attribution edges.
- **Stats channel** (`reportStats`, Tactic/NonlinearArith.lean —
  builds on `nonlinearArithCore`'s close points): env-gated
  (`NLA16_STATS=1` exactly — POSIX has no set-via-unset), WARNING
  severity (the only class verus's per-fn checker forwards on green
  runs — `verifier.rs:2489` CheckResult::Success warnings;
  `logInfo` is dropped), sandbox-safe (L1's rolled-back message log
  can't leak a line — a surviving line means an actual CLOSE, so
  `layer=1/2` names the closing layer, and ABSENCE means the ladder's
  fallback closed). Payloads pinned byte-exact both directions via
  subprocess pins (in-file `#guard_msgs` can't set env vars — no
  `IO.setEnv` on v4.25; subprocess also exercises the worker-spawn env
  inheritance shape the harness depends on). Build green 7615.

### Mechanics validated (pilot runs)

| Crate | z3 | lean | Sites | Verdicts |
|---|---|---|---|---|
| tactus-algebra | 188/0 | 122/36 | 44 | 37 agree-closed, **7 VIOLATIONS** |
| verus-2dcs (raw path) | mechanical OK | — | 1 | dep-chain verify works; 9 PRE-EXISTING qext `axiom_non_square` z3 errors (memory-confirmed baseline, not signal) |

- Raw-crate cargo-verus path works: `cargo verus verify … -p <crate>
  -- --num-threads 4` (cargo args BEFORE `-p` — cargo-verus rejects
  `--manifest-path` after Verus-irrelevant args; flag ordering trap).
  Deps verify too → Slice-2 reports each crate from its OWN run only.
- D1 baseline-source check: tactus binary without `--lean-backend`
  runs stock z3 (spinoff config). `--lean-all-proofs` is GONE since
  e5f7aea (verifier.rs comment); `--lean-backend` in the cargo-verus
  passthrough is the routing flag. The pilot's lean-native diagnostics
  confirm elaboration against Mathlib (not z3).

### PF-1 — pilot finding: 7/44 nonlinear-site violations, TIMEOUT class

All violations (6 fns, 7 sites — `axiom_mul_nonneg_monotone` carries
two): 800000-heartbeat `(deterministic) timeout at whnf` at the
requires-clause call site. General G10-resource-ceiling class; G8
blocker classification (pending armed-run attribution: was the failing
arm nonlinear_arith or a fallback? the stats lines answer it).

Second-order cause candidates to probe in Slice 2/3 (DO NOT preempt):
(a) nonlinear_arith as FIRST arm spending whnf on goals the old ladder
closed cheaper (the newly-armed run attributes this); (b)
intervalMagnitude's verbatim-quirk formula (perf watch first suspect);
(c) mkDecideProof whnf on big tables.

### NLA15-era baseline comparison (arm-ordering flag)

tactus-algebra's own git history recorded 127/31 (its last lean-gate
commit); the Slice-0 unarmed run reads 122/36. Either arm-ordering
cost (nonlinear_arith first = PF-1 corollary) or drift; the armed run
discriminates.

### Mechanics findings worth the books

- Comment-mention census inflation (site scanner MUST blank comments).
- qext carries 0 nonlinear sites — pre-implementation census artifact.
- Warning-severity is the only verus-forwarded channel on green runs.
- No `IO.setEnv` on v4.25.0 → subprocess pins.
- cargo-verus arg ORDER: cargo args before `-p`.
- `verification results::` counts fns; nonlinear failures are
  per-SITE on z3 (`assert_nonlinear_by` spans), per-FN on lean.

### Next (Slice 0 residual)

- Armed stats rerun on tactus-algebra (in flight): layer attribution
  for all 37 agree-closed (which arm closed what — the ladder-arm
  census pilot slice) and arm attribution for PF-1.
- o139 probe through the armed channel (bootstrap-fixture
  nla15_probe.rs).
- Slice-2 decisions that pilot data now sharpens: `-V cache` default
  for dep chains (cargo-verus re-verifies deps — un-cached full-chain
  time is heavy); dep-time vs target-time split.
