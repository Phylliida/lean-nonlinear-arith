# HANDOFF — 2026-08-14 — nla-14 Slice 3 DONE (quote+orchestrate:
# `nla_solve` runs reify → solve → patch → bridge → walk end-to-end,
# NO hand-written snapshots; next = Slice 4: the `nonlinear_arith`
# elab + L1/L2 layering + acceptance)

Read first: `board/nla-14-plan.md` (the nla-14 spec, decisions 1–5),
then `board/nla-14-slice-3-quote-orchestrate.md` (plan + close-out with
the new catches). Build green (7615 jobs), WORKING TREE CLEAN at
`a5ed72c`.

**Source-of-truth rule: all ports cite `git show z3-4.12.5:<path>`
(repo `verus-cad/z3`), never the working tree.** Standing directive
(Danielle): cover ALL cases no matter how rare. z3-4.12.5 build for
differential probes: worktree `/tmp/z3-4.12.5` (`make -j shell`).

## State of the arc

Slice 3 landed same-day (afternoon session): the solver runs in
TacticM via the new `Solver.checkCapturing` seam (`check`'s body +
the internal→external perm captured between snapshot and
`restoreOrder`; `check` delegates — one code path). The five quoters
live in the new `Nlsat/Quote.lean` (full TraceStep grammar).
`orchestrate` (dev tactic `nla_solve`) does: prelude (byContradiction
+ phase1 reify/Tseitin, `ReifyState` now SURVIVES) → solver
registration (mkVar FIRST — see catches) → run → proxy-def patch
(bvar-keyed, reorder-stable) → Cs rebuilt to the REFERENCED
bundle-less inputs (precheck's contract; cid−1 = frontend clause
index) → bridges against the patched INTERNAL-order table (ρ* via the
captured perm) → `walkRefutation`. SAT → per-var model display
(decision 4; ℝ-model caveat for integer vars); undef → bounded-exit
error. Pins: sq/disj/proxy/int1/int2/o139 user-syntax drivers, D-1
(learned clauses carry the proxy — guard), foreign-`.arith`-with-proxy
sound rejection (exact message), SAT model (exact message), div/mod
surface, reorder perm guard, undef budget guard.

**Kernel caught a real Slice-2 bug**: `.le/.ge` bridge arms at
negative polarity double-negated (`¬¬litHolds`); fixed via `not_le`.
No prior pin had a ≤/≥ goal. Also: `mkAlign` sandbox now `try`-wraps
push_cast/ring (simp can close linear alignments outright).

## Next: nla-14 Slice 4 — tactic + acceptance

The `nonlinear_arith` elab, layering (§2.7 verbatim: sandboxed
`withLayerHeartbeats saturateCore` L1 fast path, on failure roll back
to the ORIGINAL goal then `withLayerHeartbeats` L2 = orchestrate),
L1-never-touches-L2 pin (a saturate-closable goal), acceptance +
negative probes, stats variant mirroring `nla_saturate_stats`, design
review (Danielle), HANDOFF + memory. After that: nla-15 (tactus
wiring, ½), nla-16 (parity harness; owns G8/G9/G10 + R-iii probes +
mk_ineq_atom gap + glue-subsumption watch) = M6. Q7 open: re-offer 11a
(resultants) as interleave.

## Session mechanics + traps (cumulative; older entries in prior
## HANDOFFs — the Slice-1/2 lists all still apply)

New this slice (details in the Slice-3 board close-out):
- `Solver.run'` DROPS the final state — use `(prog.run Solver.empty)`.
- `Solver.init` creates bvar 0 AND input clause cid 0 → frontend
  clauses are cid+1; true-clause citation is the (unpinned, loud)
  cid-0 case.
- Registration order: `mkVar` before atoms/clauses, or watches
  silently no-op and every goal reports SAT with an empty model.
- `st.roots`/`defClauses`/`TraceStep` lack Inhabited/BEq — `[i]?` +
  loud error, `match` not `==`.
- `return f a` doesn't absorb a multi-line application — parens.
- `#guard` on solver runs works (compiled eval); doc comments above
  `#guard`/`set_option…in` fail parsing ("expected 'lemma'").
- Rat has `ToString` (`1/2`); `repr` gives `(1 : Rat)/2`.
- z3's budget check fires only after a BACKJUMPING resolve — stage-0
  refutations (sq, lt-cycle) never see `maxConflicts`.

Commits: `15fa48d` (plan), `24ecfb6` (core), `a5ed72c` (pins).
Memory `verus-cad/memory/project_tactus_nonlinear_port.md` appended.
