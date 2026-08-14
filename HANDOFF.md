# HANDOFF — 2026-08-14 (late) — nla-14 DONE + nla-15 DONE (+ its
# design review): `nonlinear_arith` is wired into tactus — first arm of
# the nonlinear ladder, `import LeanNonlinearArith` in the scope
# preamble, path-dep require in lean-project. Gate: o139-over-int probe
# 1 verified/0 errors (nlinarith structurally can't close it); fixture
# at its pre-existing baseline. Review R-i fixed same-day
# (message-classified skip; pre-scan deleted).
# **nla-16 Slice 0 DONE (2026-08-14 eve)** — tools/parity suite +
# NLA16_STATS stats channel (post-hoc per-obligation harvest);
# pilot: 6/44 violations, ALL 800k-whnf timeouts, arm-ATTRIBUTED by
# bisect (nonlinear_arith is the sink); o139 post-hoc shows
# `layer=2 conflicts=6` = z3-4.12.5 exactly. Census re-cut:
# 15 crates/~2,595 sites (comment-mention inflation; qext=0).
# Next = nla-16 Slice 1 (R-iii pd-driver differential probes via
# /tmp/z3-4.12.5) and/or Slice 2 (full-corpus run) — Slice-1 is
# parallel-safe; Slice-2 decisions sharpened at the Slice-0 close-out.

Read first: `board/nla-16-slice-0-mechanics.md` (Slice 0: mechanisms,
PF-1, traps), then `board/nla-16-plan.md` (plan, decisions 1–5
resolved, census corrected). Older: `board/nla-14-plan.md` (the nla-14 spec, decisions 1–5),
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

**nla-15 (same day, evening): the tactic is LIVE in tactus.**
`tactic_select.nonlin_ladder` gains `nonlinear_arith` as the first arm;
the scope preamble gains `import LeanNonlinearArith`; lean-project
gains the path-dep require (lake env covers every crate). Two forced
frontend changes, both pinned: (1) INERT-HYP SKIPPING in phase1 — the
`_tactus_bc_*` ∀-axiom haves sit in every emitted proof context, so
hyps outside the arithmetic fragment are now skipped+counted (z3's
spinoff-inert class; goal + div/mod stay strict; the SAT message
discloses the skip count); (2) mdata robustness — kernel-caught by the
fixture's degenerate-True theorem (a preceding `have` mdata-wraps the
goal; prelude + mkNnfIff now consumeMData). Gate: o139-over-int probe
(bootstrap-fixture/nla15_probe.rs) 1 verified/0 errors — nlinarith
structurally cannot close it; fixture lib.rs at its pre-existing
24/10 baseline (rot, not regression; direct-elaboration confirmed).

## Next

1. **nla-16** (parity harness, 1–2 + findings) = M6: full workspace
   nonlinear corpus through the tactic, site-for-site vs Z3
   (`/tmp/z3-4.12.5`); acceptance: no site Z3 closes that we don't.
   Owns G8/G9/G10 + the R-iii pd-driver/int1 differential probes + the
   mk_ineq_atom normalization gap + glue-subsumption watch + the R-ii
   div/mod × nlsat-tier composition gap + the perf watch (mkDecideProof
   whnf on big tables; intervalMagnitude's verbatim-quirk formula first
   suspect if pacing drifts) + NOW: which ladder arm closes what (the
   nlinarith fallback arms vs the nonlinear_arith primary — the
   census decides whether the fallback can be retired) and the
   fixture rot (10 pre-existing errors incl. known-red fill_zeros —
   not ours, but the harness will keep tripping on them).
Q7 open: re-offer 11a (resultants) as interleave.

## Session mechanics + traps (cumulative; older entries in prior
## HANDOFFs — the Slice-1/2/3 lists all still apply)

- **HOST BUILD CONSTRAINT (Danielle, 2026-08-14 eve): build with ≤4
  threads or the machine crashes.** `lake build -j4` (or fewer),
  `make -j4`, cargo likewise. Applies to the nla-16 harness runs too
  (Slice-2 full-corpus verus runs spawn lean per fn — cap the crate
  concurrency, never parallel-crate).

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
- (nla-15) **mdata is everywhere in tactic-composed contexts**: a
  preceding `have` wraps the goal in `noImplicitLambda` mdata —
  `isConstOf`-based goal-shape checks MUST consumeMData, and so must
  any bridge code pattern-matching hyp types (mkNnfIff's True/False
  arms were skipped; only the kernel's final check caught the refl —
  comparisons survived because mdata is defeq-transparent, so pins
  without a preceding `have` NEVER see it).
- (nla-15) tactus gate mechanics: check.sh convention exports
  `LEAN_PATH="$(cd tactus/lean-project && lake env printenv
  LEAN_PATH)"` (stmt-olean/per-fn builds bypass lake otherwise —
  "unknown module prefix 'Mathlib'" is a missing env, not a
  regression); `--lean-all-proofs` is REMOVED (probe headers stale);
  lean-project's `lake build` fails on missing TactusCheck.lean
  (pre-existing, env-only package — verus uses `lake env lean`).
- (nla-15 review R-i) the skip/strict boundary is a CLASSIFICATION
  problem — the right classifier is the reifier's OWN error channel;
  a parallel syntactic pre-scan is a second source of truth and
  second sources of truth drift (same shape as Slice-3's R-i).
  Rethrow only `L1-owned invariant` + `internal:`; skip the rest.

Follow-up noted (not urgent): lean-project's require is a relative
PATH dep (`../../lean-nonlinear-arith`) — switch to a pinned git
require once lean-nonlinear-arith is pushed.

Commits: `41e32a2` (plan), `f6d3064` (core+pins), `9c769d0`
(close-out), `4cab930` (Slice-4 review), `c7e752c` (nla-15 inert-skip),
`199a57a` (nla-15 mdata fix), the nla-15 close-out commit; tactus side:
the wiring commit.
Memory `verus-cad/memory/project_tactus_nonlinear_port.md` appended
(catch-up: the file had NO nla-14 content — the Slice-3 HANDOFF's
"appended" claim never landed; the stale description line fixed too).
