## nla-16 Slice 0 `done` (2026-08-14 eve) — harness mechanics + pilot cohort

### What landed

- **`tools/parity/`** (commits `3d8f1d8`, `549ae30`, `25a526d` + this):
  `sites.py` (comment/string-blank scanner), `harness.py` (log merger,
  name+file lean attribution), `posthoc.py` (per-obligation stats
  harvest), `run_crate.sh` (serialized runner), `run_pins.sh`, README.
- **Stats channel** (`reportStats`, Tactic/NonlinearArith.lean):
  env-gated `NLA16_STATS=1` (value gate — POSIX has no set-via-unset),
  warning severity, sandbox-rollback-safe. Build green 7615,
  run_pins.sh green. Consumed POST-HOC (below), not through verus.
- **Corpus re-censused:** 15 crates, ~2,595 sites (comment-mention
  inflation removed; qext = 0 sites, dropped). Plan doc corrected
  (both census block and decision-2 pilot cohort).

### Pilot results

| Crate | z3 | lean | Sites | Verdicts |
|---|---|---|---|---|
| tactus-algebra | 188/0 | 122/36 | 44 | 38 agree-closed, **6 VIOLATIONS** |
| o139 probe | — | 1/0 (pkg-cache hit; post-hoc confirms) | 1 | agree-closed, **`layer=2 conflicts=6` exactly z3-4.12.5's count** |
| verus-2dcs (raw path recon) | mechanical OK | — | 1 | dep-chain verify works; 9 PRE-EXISTING qext errors (memory-confirmed baseline) |

### PF-1 — six violations, one class, arm ATTRIBUTED

All six violations (5 fns): `(deterministic) timeout at whnf`,
800000 heartbeats. **Arm-bisect attribution (post-hoc): nonlinear_arith
is the budget sink.** Copying the failing pkg module and rewriting
`nonlinear_arith` → `fail` (always-failing meta tactic) turns the whole
module green in 18s — the fallback R-closure closes cheaply when it
runs. The pilot shape: `PartialOrder.le` over unfolded `Rational`
records fed into L1's `ring_nf at *`/whnf. This is simultaneously the
ladder-arm-ordering cost (nla-15 put nonlinear_arith first; the crate's
own gate history reads 127/31 vs our 122/36) and the G10
resource-ceiling's first concrete corpus shape. Root-cause finalists
for Slice 3 (not yet opened): L1 `ring_nf at *` whnf on
Rational-def-folded comparisons; L2 reify prelude whnf; a budget/accounting
interaction (`withLayerHeartbeats` fresh scope vs the theorem-level
800k: several full budgets can be burned per call site). The bisect
recipe is in the README (copy + `s/nonlinear_arith/fail/` + elaborate).

### Mechanism decisions locked by pilot findings

- **Stats do not travel through verus.** CheckResult::Success warnings
  are sorry-filtered (generate.rs `format_lean_check_result`,
  "deliberately narrowed to sorry") — generic warnings are dropped on
  green runs. The census channel is POST-HOC per-fn pkg elaboration:
  pkg modules persist (`target/tactus-lean/<stem>/pkg/*.lean`),
  elaborate standalone in ~ms–minutes each, stats positions carry rust
  spans (`@rust:` comments). Per-OBLIGATION granularity (a fn's pkg
  holds one theorem per obligation) — better than per-fn.
- **Prelude root resolution:** pkg imports need a compatible
  `~/.cache/tactus/prelude-<hash>/TactusDefs.olean` at LEAN_PATH head
  (module root `TactusDefs`); posthoc.py auto-probes the cache by
  mtime with an import test. Missing prelude → the cryptic
  "unknown module prefix 'TactusDefs'" — worth the books.
- **Dup-name fn attribution:** bare `failed for <name>:` matching
  false-positives same-name fns in other files (axiom_le_mul_neg…
  ×2). Harness attributes by name+file via the inner `at <src>:l:c:`
  diagnostic line. (7 phony violations → 6 real.)
- **cargo-verus arg order:** cargo args before `-p`, verus args after
  `--`; the reverse is rejected.
- **`--lean-all-proofs` is gone** (verifier.rs comment at the cache
  tag: removed e5f7aea; proof fns always route under
  `--lean-backend`).
- **pkg cross-run cache caveat:** a cached crate re-run verifies in
  seconds WITHOUT re-elaborating (the o139 probe's 0.76s 1/0). Stats
  harvest then requires either pkg-text-change or post-hoc — the
  harness never derives layer data from cached runs.
- **No `IO.setEnv` on v4.25** → subprocess pins; the value gate
  (`== some "1"`) documents itself (no set-via-unset on POSIX).

### Slice-2 decisions the pilot sharpens (for Danielle at Slice-1/2 kickoff)

- Full-chain cargo-verus runs are dep-chain-slow uncached; options:
  dep-order caching (verify deps first under same invocation) or
  `-V cache` for dep layers only with the canonical-per-crate
  constraint (target crate uncached).
- Arm census from post-hoc will give the fallback-retirement data
  (the R-arms closed 100% of pilot sites that nonlinear_arith
  missed — but the "no fallback" question is corpus-wide).

### Traps worth the books (cumulative with HANDOFF)

- Census by raw grep counts comment MENTIONS — always blank comments.
- verus drops success-path warnings (sorry-filter); post-hoc is the
  only stats channel for green fns.
- "unknown module prefix 'TactusDefs'" = missing prelude hash dir, not
  a missing crate artifact.
- Bare-name failure attribution across duplicate fn names is wrong.
- `cargo verus` arg ORDER (cargo args first).
- The pkg cross-run cache silently skips elaboration — a 0.76s "1
  verified/0 errors" is cache-shaped, not a fresh gate.
