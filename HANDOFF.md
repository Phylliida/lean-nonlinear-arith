# HANDOFF — 2026-08-13 (eve 2) — nla-14 PLANNED + Slice 1 DONE
# (Tseitin proxy checker support: `Atom.bool` + `BoolDef` + the
# taut/conseq reflection, additive, axioms clean; next = Slice 2:
# reify+Tseitin+bridge)

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

**Slice 1 landed the checker side of Tseitin:** `Atom.bool (d :
BoolDef)` with flattened arith-literal-leaf definitions,
`interp`/`litHolds` arms (`boolDefHolds`), and the decide-grade
`BoolDef.taut`/`conseq` + `taut_sound`/`conseq_sound` reflection
(the upRefutes idiom). `Walk.precheck`/`clauseDecodable` UNCHANGED by
design. 12 churn arms in Solver/Refute, all junk/defensive. Pins in
AssembleTests incl. the end-to-end {¬b1, b0} definitional clause via
`taut_sound`.

## Next: nla-14 Slice 2 — reify+Tseitin+bridge

Per the plan's slice list. The components: Expr→MPoly/Atom parser
(ℤ/ℕ/ℝ comparisons; `+ - * ^nat`, casts), var table (ℤ→`mkVar true`
+ integrality hyp emission; ℕ→ℤ + `0 ≤ ↑n` clause per decision 2; ℝ
direct), Tseitin clausification with `mkBoolVar` slots + flattened
defs, per-clause bridges (`conseq_sound` for root clauses,
`taut_sound` for definitional), `byContradiction` assembly. First
recon question (recorded in the Slice-1 close-out): the proxy-def
patch applies to the extracted snapshot POST-reorder — defs reference
bvars (stable across `heuristicReorder`), but the atom table the walk
sees is the snapshot's internal-order one; bridges are built against
the same patched table by construction.

## Roadmap (unchanged)

Slices 3 (quote+orchestrate + SAT-model display per decision 4) →
Slice 4 (the `nonlinear_arith` elab, layering, acceptance + probes,
design review) = nla-14 (3–4 sessions total) → nla-15 (tactus wiring,
½) → nla-16 (parity harness; owns G8/G9/G10 + R-iii pd/int1 z3-binary
probes + mk_ineq_atom gap + glue-subsumption watch) = M6. Tier B
(G7/S1) deferred unless the harness shows need. Q7 open: re-offer 11a
(resultants) as interleave.

## Session mechanics + traps (cumulative)

New this session (details in the Slice-1 board entry):
- **`open Classical` inside the namespace** for `decide (τ l)` in
  STATEMENTS (the `classical` tactic can't help signatures).
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

Commits this session: `44e9f04` (nla-14 plan), `72c3b6a` (Slice 1).
Memory `verus-cad/memory/project_tactus_nonlinear_port.md` appended
(nla-14 plan + Slice 1).
