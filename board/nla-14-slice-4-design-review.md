## nla-14 Slice 4 design review (2026-08-14, Danielle-requested)

Divergence/regret/not-the-right-way audit of the Slice-4 code:
`nonlinearArithCore`, the `nonlinear_arith`/`nonlinear_arith_stats`
elabs, the `nlaL2Runs`/`nlaL2Conflicts` instrumentation, the run_cmd
pin layer, and decisions D1–D3. Frame: decisions we'll regret,
divergences from z3, shortcuts.

### Findings

**R-i (REAL, fixed same-day): the instrumentation semantics didn't
match the pins' intent.** The Slice-4 hook sat AFTER the solver run,
two consequences:

- (a) The True short-circuit path (`prelude` returns `none`) exited
  before the bump — and `nonlinearArithCore`'s stats branch then
  printed `closed by L2 (nlsat search → trace → kernel-checked walk,
  N conflicts)` with N STALE from a previous run: a message claiming a
  search that never happened, with fabricated-looking data.
- (b) The counter meant "reached the solver run", not "L2 entered" —
  prelude failures (the div/mod and unsupported-shape exits) were
  invisible to it. Invisible-to-the-counter is exactly the failure the
  L1-never-touches-L2 pin exists to catch; the pin's intent was
  entry-semantics all along.

Fix: the bump + conflicts-zeroing moved to orchestrate's ENTRY (real
count set post-run), and orchestrate now returns
`OrchestrateExit` (`.prelude` / `.refuted`; SAT/undef still throw) so
the stats line names what actually happened — the True goal reports
`closed by L2's prelude (True goal — no solver work)`. `nla_solve`
discards the value. Pins: the True goal is now counter-pinned
(L2 entered exactly once, zero conflicts) and the prelude stats line
is #guard_msgs-pinned byte-exact; the sq refuted-line pin (4
conflicts) is unchanged. Only-ever-two callers (nla_solve,
nonlinearArithCore); no Slice-2/3 pin touched.

**R-ii (REAL, boarded to nla-16): the div/mod × nlsat-tier composition
gap — a coverage gap-in-kind created BY the layering.** L1 owns
div/mod semantics but cannot produce nlsat-tier nonlinear lemmas; L2
hard-fails at reify on any div/mod (the pinned L1-owned invariant,
§2.7). So a VC needing BOTH — e.g. an `x % y` hypothesis plus an
o139-class degree-3 cross-product goal — is unclosable by
`nonlinear_arith`, while z3's solver-6 closes such goals in one
search: `nla_divisions` is part of `nla_core` and feeds the same
arithmetic context nlsat consults. Reachable from Verus in principle;
today the failure is LOUD (the div/mod reify error), never a wrong
close. Not in the checker-completeness G-inventory (that file is
checker-side; this is frontend-layering, a new class). Fix direction
when nla-16 shows corpus contact: reify div/mod subterms as fresh
vars + emit the Euclidean defining facts (`y·q + r = x`, sign-gated
mod range) as extra root hyps over the ℝ casts — sound (the
identities hold in ℤ and casts preserve them) and z3-shaped (div/mod
atoms + axioms in the shared context). Until then the hard-fail is
the correct surface.

### Verified clean (audit notes)

- `tryCatchRuntimeEx` catches BOTH failure classes: regular tactic
  errors (ℝ-goal omega `throwError` → L2; probe: sq L2=1) and
  heartbeat runtime exs (tryGrobner's proven idiom,
  Saturate.lean:1901).
- Rollback fidelity: `restoreState` wipes L1's failure messages (the
  SAT pin is byte-identical to the nla_solve surface) and its
  context/env churn never reaches L2's prelude (the full pin matrix
  green). The Slice-5 env-keeping lesson does not apply: no proofs
  are extracted from a FAILED L1.
- No wrong-close channel: L1 closes only via sound tactics +
  kernel-checked noted lemmas; L2 only via the kernel-checked walk;
  exceptions never produce proofs.
- Budget shape: worst case 2× user maxHeartbeats is the sanctioned
  Z3-per-module shape (BUDGET-SHAPE lesson; DESIGN-endgame §2.7).
  o139's L1 phase fails fast (ℤ-native leaf on an ℝ goal), so the
  800k on the test is effectively L2's.
- undef cannot be re-pinned through the layering without threading
  `maxConflicts` — D3 (the knob is z3-non-default, UINT_MAX =
  nlsat_params default) keeps it at the solver seam. Consistent.
- The linter warnings at NonlinearArith.lean:488/1052 are pre-existing
  Slice-2 lint in untouched regions (verified against `4e42c84`).
- `g0.isAssigned` is genuinely defensive: saturateCore's normal
  returns all close the goal they worked on (early return only at
  `getGoals.isEmpty`; the leaf omega is unwrapped) — the check can
  only fire after future refactors, where it falls to L2, the safe
  side.
- The stats elab's counter reset mirrors `nla_saturate_stats`;
  documented; pins set-then-run.

### Considered, not boarded

- L1 runs on ℝ goals it cannot close (collector/discharge/leaf are
  ℤ-native): bounded waste, fails fast in practice. Short-circuiting
  L1 on ℝ-typed goals would be a heuristic special case with no
  measurable win — nla-16 owns the perf watch.
- L1 internal-error swallowing: a meta-bug `throwError` inside
  saturateCore falls silently to L2. Never unsound (both layers'
  closes are independently checked); visibility via the stats layer
  line + the layer pins. Rethrowing "internal:"-prefixed errors would
  mean parsing exception messages — worse.
- Layer pins are intentionally fragile to L1 improvements
  (nla-07b/21/22 will flip drivers L2→L1; the pins fail loud and get
  re-pinned). Intended.
- The D2 numeral pin exercises forwarding, not restriction;
  `nonlinear_arith 0` on a div/mod goal needing 2 saturation rounds
  turns a closable goal into the L2 hard-fail — a debug-knob
  corollary, documented in the elab docstring.

### Verdict

Slice 4 stands: R-i fixed same-day, R-ii boarded to nla-16. Meta-yield
of the round: the instrumentation added in the SAME commit as the pins
was the least-audited code in the slice — the pin mechanism itself
needed the adversarial read (its semantics were "reached the solver"
while the pin's intent was "entered L2"; only the True-goal edge made
the gap visible). nla-14 is DONE → nla-15 (tactus wiring).
