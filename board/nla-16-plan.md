## nla-16 plan `boarded` (2026-08-14 eve, pre-implementation planning sweep — the parity harness, = M6)

Scope (HANDOFF + DESIGN-endgame §2.10 + board nla-16): run the full
workspace nonlinear corpus through the `nonlinear_arith` tactic (via
tactus `--lean-backend`), site-for-site vs Z3, census-style report.
**Acceptance gate: no site that Z3 closes and we don't.** Also the
owned measurements (G8/G9/G10, R-iii probes, mk_ineq_atom gap,
glue-subsumption watch, div/mod × nlsat contact scan, perf watch,
ladder-arm census) — this is the one declared-empirical residue; the
harness confirms coverage, it does not define it (M5 carries the
paper guarantee). Estimate: 1–2 sessions infrastructure+run + a
findings/fallout budget, per DESIGN-endgame §2.10.

### Owned items → where each lands in the slice plan

| Item (source) | Slice |
|---|---|
| G8 unmapped glue tail — census of how far the discharge layer's glue (linarith + one nlinarith round + sq_nonneg hints) reaches; every Z3-closed/ours-open site gets its blocker classified (L1-open / L2-search-final / discharge-fail / glue-tail) | 2 + 3 |
| G9 RUP stall — watch item (theoretical, argued impossible for z3 chains); harness records any stall events (expect zero; non-zero = finding, not a fix) | 2 |
| G10 resource ceiling — kernel decide / heartbeats pacing on huge refutations; census TABLE of per-site layers + L2 ranger (Q6: heartbeats, never wall-clock gates; `uptime` before trusting timings) | 2 |
| R-iii pd-driver z3-binary differential probes — pd1/pd2/pd3/pd4/pd6 + int1 through the `/tmp/z3-4.12.5` shell (`make -j shell` worktree, live) with nlsat statistics, vs our WalkTests/RefuteTests snapshots (conflict counts / emitted payloads); search-side only, fidelity-driven | 1 |
| mk_ineq_atom normalization gap (nla-19a-design-review-13: sign-normalize every factor, sz ≥ 1 invariant — our `mkIneqAtom` omits the loop) — measure corpus contact: does any harvested query's atom construction reach a shape the missing normalization would alter? Snapshots re-derive under the port when it lands (expected churn, not breakage) | 2 |
| glue-subsumption watch — how often glue-subsumption closes step-free vs z3's step structure (per-site counts off `nlaL2Runs`/`nlaL2Conflicts` shape); measurement only | 2 |
| div/mod × nlsat-tier composition gap (Slice-4 review R-ii) — CONTACT SCAN: how many corpus sites carry div/mod hyps AND need L2; today these fail LOUDLY at the reify boundary (never wrong-close); harvested cases become the acceptance drivers if the fix (reify div/mod subterms as fresh vars + Euclidean defining facts over ℝ casts) is pulled forward | 2 + 3 |
| perf watch — mkDecideProof whnf on big tables; intervalMagnitude verbatim-quirk formula first suspect if pacing drifts | 2 (deferred results table) |
| ladder-arm census (nla-15 note) — which ladder arm closes what: `nonlinear_arith` primary vs the nlinarith fallback arms; census decides whether the fallback can retire | 2 |
| fixture rot — the 10 pre-existing fixture errors (incl. known-red fill_zeros) stay a separate column, never count as harness failures; fill_zeros triage reported | 2 |

### Recon (2026-08-14 eve — done before planning)

- **Corpus census (this session, `grep -rE "by ?\( *nonlinear_arith"`):**
  16 crates carry sites, ~2,613 total. Verus-rational 433,
  fixed-point 648, mandelbrot 519, cutedsl 373, physics2d 144,
  bigint 133, computability-theory 86, group-theory 70, vulkan 40,
  interval-arithmetic 38, gui 25, ray-marching 18, canvas 9,
  algebra 12, quadratic-extension 1, 2d-constraint-satisfaction 1.
  (Line-count proxy; the harness's per-function extraction replaces
  it with exact numbers.)
- **Per-function granularity exists end-to-end.** Verus reports
  verified/error counts per crate and errors carry file:line spans;
  mapping site→function = syntactic containment (the span of the
  enclosing `proof fn`/`spec fn`). No verus-side change needed for
  the FUNCTION-level census; site-level inside one function needs
  `--verify-function`-style bisection ONLY if multi-site functions
  produce ambiguous attributions (decision 3).
- **The z3 baseline rides the same binary.** tactus is a verus
  fork; without `--lean-backend` it runs the stock z3 path on the
  same frontend bytes — per-goal divergence isolates to the backend
  exactly (decision 1).
- **check.sh convention exists per tactified crate** (`-V cache`,
  tee'd full log, LEAN_PATH dance) — the harness mirrors it, does
  NOT reuse it as-is (it hides per-function data in counts; we need
  the full logs machine-parsed).
- **Instrumentation already in tree:** `nlaL2Runs`/`nlaL2Conflicts`
  refs, `nonlinear_arith_stats` variant, SAT-exit skip-count
  disclosure, run_cmd counter-sandwich pin mechanism (nla-14). The
  harness harvests these from emitted output where the per-site layer
  report needs them; a per-site stats mode (stats line per closed
  site, one line, grep-able) is the one new tactic-side surface
  (untrusted output only — never gates).
- **z3-4.12.5 worktree live** at `/tmp/z3-4.12.5` (`make -j shell`
  build present) for the R-iii differential probes.
- **Fixture is ROT, not corpus.** tactus/bootstrap-fixture's 24/10
  is pre-existing; the harness never derives acceptance from it.

### Decision points — proposed, Danielle resolves

1. **Baseline source — tactus binary with z3 backend** (same fork,
   no `--lean-backend`). Same frontend → cleaner per-goal isolation
   than stock verus (which could disagree with tactus's emitter on
   things unrelated to the backend). Alternate: stock verus for
   double bookkeeping. Proposed z3 runs: default spinoff config
   exactly as `by(nonlinear_arith)` sites already ask for (smt.
   arith.solver=6, MBQI off, nlsat enabled — established facts from
   the 2026-07-24 reading).
2. **Corpus order — rotational, worst-first cold start.** Rank by
   sites: fixed-point (648) → mandelbrot (519) → rational (433) →
   cutedsl (373) → physics2d/bigint tail. Small cohort first as
   Slice-0 calibration: quadratic-extension (1) + the existing
   tactus-algebra mirror (tactified copy of algebra) + the nla-15
   o139 probe. The big four only after Slice 0's mechanics pin.
3. **Multi-site functions, ambiguous attribution — bisect on
   demand.** Default census granularity is per-FUNCTION; a function
   carrying ≥2 nonlinear sites that diverges gets a per-site
   bisection pass (`--verify-function`-style isolation or synthetic
   split). Only pursued where the diff report shows ambiguity —
   Danielle rule: only where it changes the answer.
4. **z3 borderline-flakiness — one canonical run + targeted
   restart-free repeat of DIVERGENT sites only** (verus's z3 is
   seed-stable; restart-level variance lives in resource limits,
   and the acceptance gate only cares about closures). If a site
   closes under neither of two identical z3 runs identically-timed,
   classify `z3-borderline` — excluded from the gate both sides.
5. **Wall-clock off the table.** Q6: heartbeats + kernel per-site
   tables only; `uptime` before any timing claim (standing
   directive 7 verbatim).

### Slice plan

- **Slice 0 — mechanics + pilot (½ session).** Harness script
  (`tools/parity/`): per-crate z3+tactus runs with full-log
  capture (mirroring check.sh's LEAN_PATH dance; `-V cache` OFF for
  canonical runs), parser extracting per-function results +
  function→site mapping, site table CSV (`crate, fn, site_line,
  z3, lean, layer, notes`). Pilot cohort per decision 2. Output: the
  mechanics file + pilot table + the confirmed per-site stats
  surface (grep-able stats line). Decision 1/2/3/4/5 resolved by
  Danielle BEFORE this slice's run half.
- **Slice 1 — R-iii differential probes (½ session).** pd1–pd6 +
  int1 through the z3-4.12.5 shell; snapshot vs binary compare;
  board-doc close-out. Independent of the harness; parallel-safe.
- **Slice 2 — the full run + report (1 session + fallout).** All 16
  crates through both backends; site table + diff classification
  (z3-closed/ours-open sites get a one-line blocker class, per G8);
  G10 pacing table; ladder-arm census; div/mod contact scan;
  mk_ineq_atom contact scan; G9/G10 watch notes; fixture rot
  reported separately. Acceptance gate evaluated.
- **Slice 3 — findings triage (bounded).** Every
  z3-closed/ours-open site is either (a) a NEW boarded item with a
  reproduction, (b) pulled into an existing owned item (e.g. div/mod
  R-ii composition), or (c) classed `z3-borderline` (decision 4).
  No silent categories. Design review (Danielle-requested pattern,
  same-session) → **M6 closes here.**
