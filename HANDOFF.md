# HANDOFF — 2026-08-14 — nla-14 DONE (all four slices + Slice-4 design
# review landed same-day): `nonlinear_arith` ships — sandboxed L1
# (`saturateCore`) fast path, clean rollback to the original goal, L2 =
# Slice-3 orchestrate, per-layer fresh heartbeat budgets. Review: R-i
# instrumentation entry-semantics fixed same-day (OrchestrateExit), R-ii
# div/mod × nlsat-tier composition gap boarded to nla-16.
# Next = nla-15 (tactus wiring, ½ session — THE PAYOFF).

Read first: `board/nla-14-plan.md` (the nla-14 spec, decisions 1–5),
then `board/nla-14-slice-4-tactic-acceptance.md` (plan + close-out —
D1 dev elabs stay / D2 round numeral mirrors nla_saturate / D3 no
maxConflicts threading, all resolved by the standing principles;
probe-verified per-driver layer table; the run_cmd counter-sandwich
pin mechanism), then `board/nla-14-slice-4-design-review.md` (R-i/R-ii
+ the verified-clean audit notes). Build green, WORKING TREE CLEAN at
the review commit.

**Source-of-truth rule: all ports cite `git show z3-4.12.5:<path>`
(repo `verus-cad/z3`), never the working tree.** Standing directive
(Danielle): cover ALL cases no matter how rare. z3-4.12.5 build for
differential probes: worktree `/tmp/z3-4.12.5` (`make -j shell`).

## State of the arc

Slice 4 landed same-day: `Tactic/NonlinearArith.lean` gains
`nonlinearArithCore` (saveState → tryCatchRuntimeEx
(withLayerHeartbeats saturateCore) → `g0.isAssigned` check → on failure
full restoreState + withLayerHeartbeats orchestrate), the
`nonlinear_arith (n)?` / `nonlinear_arith_stats (n)?` elabs, and the
`nlaL2Runs`/`nlaL2Conflicts` instrumentation refs. The same-day design
review added `OrchestrateExit` (orchestrate returns `.prelude` /
`.refuted`; entry-semantics hook) — R-i. No new trusted surface; the
only pre-existing-pin-touching change is `nla_solve` discarding the
return value.

**Probe finding that reshaped the acceptance set:** int1, int2, and
the R-iii driver all close in L1 (mined `x*x = 2` down-propagates to
|x| ≤ 1, corner rules refute — no B&B). The B&B-through-layering
acceptance is carried by the NEW drivers `x*(x+1) = 3` (L1 bounds x
only one-sidedly) and its two-variable reorder variant (perm = #[1,0],
intBranch at the internal index). Per-driver layers (probe-verified,
scratch_layerprobe.lean): L1 — sqZ-nonneg, tangent, int1, int2, R-iii;
L2 — sq (4 conflicts), disj (2), proxy (4), nat (1), reorder (1),
x*(x+1)=3 (1, ×2 drivers), o139 (6 = exactly z3-4.12.5's count).

Pins (Tests.NonlinearArith): L1-never-touches-L2, round-numeral
exercise, byte-exact stats layer line, full acceptance sweep, o139
through the layering (800k on the test, fresh per layer), True
short-circuit, SAT model display / div/mod hard-fail byte-identical to
the nla_solve surfaces, unsupported-hyp (∃) loud rejection.

## Next

1. **nla-15** (tactus wiring, ½ session): `require` line in
   tactus/lean-project (pins already identical: lean+mathlib v4.25.0),
   emit `nonlinear_arith` for `by(nonlinear_arith)` sites, crate-local
   check.sh gate. THIS is the payoff: all Verus nonlinear sites get
   the Lean backend.
2. **nla-16** (parity harness, 1–2 + findings): owns G8/G9/G10 + the
   R-iii pd-driver/int1 z3-binary differential probes via
   `/tmp/z3-4.12.5` + the mk_ineq_atom normalization gap +
   glue-subsumption watch + **the R-ii div/mod × nlsat-tier
   composition gap (board file updated)** = M6. Also the perf watch
   (mkDecideProof whnf on big tables; intervalMagnitude's
   verbatim-quirk formula is the first suspect if pacing drifts).
Q7 open: re-offer 11a (resultants) as interleave.

## Session mechanics + traps (cumulative; older entries in prior
## HANDOFFs — the Slice-1/2/3 lists all still apply)

New this slice (details in the Slice-4 board close-out):
- **run_cmd counter sandwiches** pin tactic-internal state: IO.Ref
  instrumentation set inside the tactic, reset/read by `run_cmd`
  around the example — deterministic (command elaboration is
  sequential). `#guard_msgs` can't pin L1's stats line (wall-clock ms).
- **Probe before pinning layers** — two planned-L2 drivers were
  L1-closable; asserting the planned layer would have silently deleted
  the B&B acceptance coverage.
- L1 failure is exception-shaped: saturateCore's tier-2 omega is
  deliberately UNWRAPPED (Saturate.lean:2031); normal return ⇒ closed.
  Sandbox idiom = tryGrobner's saveState/tryCatchRuntimeEx/
  restoreState (catches tactic errors AND heartbeat runtime exs).
- A registration-order hyp is genuinely unused by the refutation — the
  unused-variable lint fires CORRECTLY; suppress with a comment saying
  the hyp orders var registration.
- `nonlinear_arith_stats` resets all counters at entry (mirrors
  nla_saturate_stats) — counter pins set-then-run, never read across a
  stats call.
- `Tactic.saturateCore` resolves unqualified from the Frontend
  namespace via enclosing-namespace lookup (LeanNonlinearArith.Tactic)
  — no open needed, no clash with `Lean.Elab.Tactic`.
- (review R-i) instrumentation hooks belong at ENTRY semantics: a
  post-hoc counter reads "reached the solver", the pin's intent was
  "entered L2" — and short-circuit exits report STALE data unless the
  refs are zeroed at entry. The pin mechanism itself needs the
  adversarial read.

Commits: `41e32a2` (plan), `f6d3064` (core+pins), `9c769d0`
(close-out), the review commit.
Memory `verus-cad/memory/project_tactus_nonlinear_port.md` appended
(catch-up: the file had NO nla-14 content — the Slice-3 HANDOFF's
"appended" claim never landed; the stale description line fixed too).
