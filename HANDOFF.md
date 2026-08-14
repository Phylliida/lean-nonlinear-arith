# HANDOFF — 2026-08-14 — nla-14 Slice 1 + Slice 2 DONE
# (Tseitin proxy checker support + the reify+Tseitin+bridge frontend;
# `nla_frontend` transforms user goals to the walk's refutation goal;
# next = Slice 3: quote+orchestrate, solver-run-in-tactic)

Read first: `board/nla-14-plan.md` (the nla-14 spec — decisions 1–5
RESOLVED by Danielle's standing principles: match every z3 case, the
right way, now not later, SAME MECHANISM as z3 for performance
parity), then `board/nla-14-slice-1-booldef-proxy-checker.md` (Slice-1
close-out with the new traps). Build green (7612 jobs), WORKING TREE
CLEAN at `72c3b6a`.

**Source-of-truth rule: all ports cite `git show z3-4.12.5:<path>`
(repo `verus-cad/z3`), never the working tree.** Standing directive
(Danielle): cover ALL cases no matter how rare. z3-4.12.5 build for
differential probes: worktree `/tmp/z3-4.12.5` (`make -j shell`).

## State of the arc

M3 + 12e landed earlier today (see the previous HANDOFF's git log);
this evening session planned nla-14 and landed Slice 1. Key plan
facts: the solver is PURE (`SolverM = StateM Solver`,
`Solver.run'` — callable from TacticM); L1 needs no changes
(`saturateCore` + `withLayerHeartbeats` are the §2.7 shape); bool vars
were ALREADY ported search-side (`mkBoolVar` Solver.lean:183,
`isArithAtom` :245, decision path :486 — mirrors z3's `mk_bool_var`);
the walk's goal shape is `∀ ρ, (integrality hyps) → (∀ C ∈ Cs,
clauseHolds ρ atoms C) → False` with integrality hyps BEFORE the
clause hyp (12e decision 1).

**Slice 1 landed the checker side of Tseitin** (+ same-day design
review, R-i fix): `Atom.bool (d :
BoolDef)` with HIERARCHICAL definitions (leaves may reference other
proxies — z3's Tseitin nests; fuel-bounded table recursion, cycles
poison to False),
`interp`/`litHolds` arms (`boolDefHolds`), and the decide-grade
`BoolDef.taut`/`conseq` + `taut_sound`/`conseq_sound` reflection
(the upRefutes idiom). `Walk.precheck`/`clauseDecodable` UNCHANGED by
design. 12 churn arms in Solver/Refute, all junk/defensive. Pins in
AssembleTests incl. nested-proxy evaluation, cyclic-def poisoning, and
the end-to-end {¬b1, b0} definitional clause via `taut_sound`.
Review-verified against 4.12.5 source: bool-var negative-first decide
(:1536 = Solver.lean:845), proxies never in arith justifications
(:1764-1813), `max_var(bool) = null_var` (:376).

**Slice 2 (2026-08-14):** the frontend is real — `nla_frontend` in
`Tactic/NonlinearArith.lean` runs reify(ℤ/ℕ/ℝ, opaque-subterm vars,
div/mod hard-fail) → NNF+Tseitin (normalized hierarchical proxy defs)
→ term-mode bridges (the ONLY sandbox is per-literal evalP alignment)
→ the walk-shaped refutation goal, with integrality hyps before the
clause hyp. Pins walk the produced goals BY HAND (kernel checks the
full bridge chain): sq/ℝ, two-literal disjunctive, Int integrality,
the PROXY path (and-under-or over a shared lt-atom), Not-Not.
Mid-slice catch: `taut` truth tables over Literal leaves needed
polarity normalization (`BoolDef.normNeg` + per-leaf-consistent
soundness + `clauseHolds_iff_evalNorm`).

## Next: nla-14 Slice 3 — quote+orchestrate

Slice 2 LANDED (2026-08-14): `Tactic/NonlinearArith.lean` — the
`nla_frontend` tactic transforms `Γ ⊢ G` to the walk's refutation goal
(reify → Tseitin → term-mode bridges; full detail + the normNeg catch
+ the new traps in board/nla-14-slice-2-reify-tseitin-bridge.md).
Slice 3 components (plan doc): the solver run in TacticM
(`Solver.run'` is pure), the five snapshot quoters (atom/clause/step/
bundle/snapshot — `atomToExpr`/`atomsToExpr` exist in the frontend
file, MOVE or share), the proxy-def patch into the extracted snapshot
POST-reorder (bvar-keyed defs are `heuristicReorder`-stable), the
post-run rebuild of Cs to the REFERENCED inputs only (precheck's
contract — bridges are per-clause, so select), SAT-exit model display
(decision 4 — skip proxy vars), and the pins: drivers with NO
hand-written snapshot, the D-1 disjunctive driver with a proxy in a
LEARNED clause, the foreign-`.arith`-with-proxy sound-rejection probe,
and the Slice-2-deferred div/mod error-surface pin (`#guard_msgs`).

## Roadmap (unchanged)

Slices 3 (quote+orchestrate + SAT-model display per decision 4) →
Slice 4 (the `nonlinear_arith` elab, layering, acceptance + probes,
design review) = nla-14 (3–4 sessions total) → nla-15 (tactus wiring,
½) → nla-16 (parity harness; owns G8/G9/G10 + R-iii pd/int1 z3-binary
probes + mk_ineq_atom gap + glue-subsumption watch) = M6. Tier B
(G7/S1) deferred unless the harness shows need. Q7 open: re-offer 11a
(resultants) as interleave.

## Session mechanics + traps (cumulative)

New this session (details in the Slice-1 and Slice-2 board entries):
- **`→` binds tighter than `↔`** — `H → A ↔ B` parses as
  `(H → A) ↔ B`; parenthesize trailing Iffs.
- `mkAppM` takes EXPLICIT args only; implicit-operand lemmas need
  `mkAppOptM` with pinned positions — INCLUDING type implicits
  (`some (mkConst ``Real)` for `R`, else "failed to synthesize
  IntCast ?R" at tactic RUNTIME).
- `Membership.mem` value args are (container, elem) —
  `mem #[Cs, C]`; `List.Mem` on `[]` is not defeq-False under mkAppM's
  isDefEq — eliminate via `List.not_mem_nil` (mkAppM' it), cons via
  the `List.mem_cons` Iff (Walk.memChain idiom).
- `Or.elim`/`False.elim`: pin ALL implicit binders via mkAppOptM
  (else "result contains metavariables").
- Sandbox tactics act on the CURRENT goal unless you setGoals to the
  sandbox mvar FIRST (the Walk buildFSet idiom: getGoals/setGoals/
  restore).
- `let (a,b) ← match …` not `:= ←`; `return` in a nested match arm
  exits the OUTER fn; multi-statement if-branches in do need explicit
  `do`; structure field groups need parens; doc comment above
  `mutual` fails ("expected 'lemma'").
- **`open Classical` inside the namespace** for `decide (τ l)` in
  STATEMENTS (the `classical` tactic can't help signatures).
- **WF-compiled defs (`termination_by` with a mixed measure) have NO
  kernel defeq** — consumers rewrite via the auto equation lemmas
  (simp only [f] at hyp AND goal — variable-headed applications stay
  folded, constructor-headed ones unfold — then congr); plain `simp`
  (not `simp only`) reduces `#[...][i]?` lookups; don't simp under a
  lambda whose bound var blocks iota (rcases/split FIRST).
- The MPoly evaluator is **`Check.evalP`** (Semantics.lean:77), NOT
  Kernel's (that's the PairQ certificate evaluator — the
  unknown-constant error disguises itself as "Function expected ...
  has type ?m.1").
- simp needs `Check.Atom.Holds` in the set BEFORE `holds_single_lt`
  fires (the Iff head is `Atom.Holds`).
- simp proofs unfolding the atom table: `cases a` BEFORE `cases n`
  (a fresh match arm on a variable atom sticks).
- Prior section (from the 12e HANDOFF, still accurate): doc comment
  above `#guard` fails parsing; `scratch_dump.lean` needs
  `lake env lean --run`; verify `git status` at session start;
  `break` works in do-notation `while`; `let mut` can't be assigned
  inside `withContext` closures (thread a state record);
  '_tmp✝' kernel fv errors = upstream elaboration error-recovery —
  grep for the REAL error; `withoutModifyingState` + `hasMVar` checks
  on produced terms (the Slice-1 hole class); inductive parameters
  implicit in constructors (`mkAppOptM … #[some ρ]`); do-block `try`
  arms end in VALUES; `{ S with … }` structure updates on ONE line;
  named `Array TraceStep` defs with ascriptions for `evalExpr`;
  block-buffered `--run` output; `lake build <module>` BEFORE
  `lake env lean scratch.lean`; swallowed try/catch instrumentation;
  `Eq.mp` forward / `Eq.mpr` BACKWARD; `(0:ℝ)` annotation;
  `Or.getAppFnArgs` = `#[A, B]`; generic `lt_or_ge` not
  `Int.lt_or_ge`; `mkConstWithFreshMVarLevels`-style raw consts as
  mkAppM args fail — pin via mkAppOptM (Left.neg_pos_iff idiom).

Commits: `44e9f04` (nla-14 plan), `72c3b6a` (Slice 1), `3534f14`
(Slice-1 review + R-i), `6d86751` (Slice-2 trusted glue checkpoint),
plus the Slice-2 landing. Memory
`verus-cad/memory/project_tactus_nonlinear_port.md` appended.
