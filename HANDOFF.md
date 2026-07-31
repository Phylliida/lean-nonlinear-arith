# HANDOFF — 2026-07-31 (post nla-29 close + design review)

Read first: `DESIGN-endgame.md` (the master plan — §0 finish line, §2
critical path, §6 decisions + divergence register, §8 standing
directives), then `BOARD.md` (execution units; the nla-29 entry has the
full design-review log). Memory file
`verus-cad/memory/project_tactus_nonlinear_port.md` has the session
history. Build: Nix `lake` on PATH (not elan); `lake build` green at
commit `b7379cc`.

## Where we are

Critical path `28 → 27 → 12b-ii → 29` is DONE. L1 saturation, the
computational kernel (QPoly/Mpbq/BivPoly/RAlg/Factor/Roots/CellStore/
AnumArith), and the nlsat evaluator lane (Types, IntervalSet, AnumEval,
Evaluator + q≡0 fallbacks, EvaluatorTable) are all landed and pinned.
Everything is sorry-free; trusted layer unchanged this arc (all new
code is untrusted search-side).

**Next: nla-12c — the solver loop** (2–4 sessions, the big port).
Spec: DESIGN-endgame §2.3. Port `nlsat_solver.cpp` (4.12.5 classic
search, no levelwise, `randomize=false`): stage/level structure keyed
on max_var, boolean + arithmetic decisions, propagation via
infeasible-interval sets with justification literals,
`select_witness = pickInComplement`, conflict resolution calling
explain (12d), backjumping, learned clauses. **SAT mode first** —
models are verified by evaluation (the evaluator is its own checker
for sat answers). Clause-learning minimization and restart policy are
SEMANTIC per Q3: port verbatim; any heuristic simplification needs a
written parity argument in the commit. Solver state owns the cell
store (one store for the solver's lifetime; trail pops remove
bindings, refinements persist — see CellStore.lean header). Trace
emission hooks land here but payloads stay unpinned until 12d/19a
(standing rule 3).

After 12c: 12d+19a (same arc — Explain + Check.lean v0, Q1
grammar-first S3 coverage proof derived from nlsat_explain.cpp
source), 19b (M3), 12e, 14, 15, 16. Parallel lanes: S1 (11a ∥ 11c,
Q7 open — 11a doubles as resultantElim's semantic proof), L1
hardening (21/22/07b/06), nla-30 (deferred multivariate-resultant
generality), **nla-31 (termination proofs — `refineNzBound` is
elementary, do it first; the engine loops + isolating2Refinable compose
with nla-10/Sturm)**.

## Key architecture (don't re-derive)

- **CellStore** (`Kernel/CellStore.lean`): `CellStore = Array RAlg`,
  `CellM = StateM CellStore`, in-place updates; all ops that refine
  (`compareC`, `addC`, …) write back. Build mixed-set scenarios in ONE
  CellM computation (ids dangle outside their store). `fresh` must be
  the `let n := (← get).size; modify (·.push c); return n` form (RC
  quadratic trap).
- **Anum arithmetic** (`Kernel/AnumArith.lean`): z3's field ops 1:1.
  became-basic is DATA (`MkBinaryResult`/`MkUnaryResult` carrying the
  rational) — callers re-dispatch through `addRatL`/`subRatR`/etc.
  (z3's `mk_basic` with a basic operand); restore ordering is in the
  type's docstring (design-review fix). z3's throws are `Option`
  (`inv`/`div` of zero, `power` 0^0) — `none` is the faithful image of
  the exception; never Lean's silent `1/0 = 0` / `0^0 = 1`.
- **evalAnum** (`Nlsat/Evaluator.lean`): `t_eval_core` verbatim;
  `Option RAlg` (unassigned var or z3 throw = `none`, never the
  panic-default cell-0 read). Stored-cell refinements persist (z3's
  public const& ops const_cast and mutate); temps need no threading
  (overwritten per op call in both worlds — recheck if 12c ever reuses
  temporaries across op calls).
- **isolateRootsAt**: `isolateRootsAtCore` + `isolateRootsNested` /
  `isolateRootsAt` (one-level aux-z recursion is structural by
  construction). q≡0 witness analysis on the board (one factor of the
  defining poly must divide every x-coefficient).
- **BivPoly.resultantElimY**: approved multiplication-matrix route
  (Danielle 2026-07-31: capability-identical to z3's general resultant
  on every reachable input — pb is always a univariate defining poly;
  generality deferred to nla-30). `detBiv` is Bareiss fraction-free;
  `detBivLaplace` is the pinned differential reference.

## Standing directives (Danielle)

1. Do things the right way first; prove over empiricism; follow z3 as
   closely as possible — every divergence is bad unless signed off
   (register in DESIGN-endgame §6).
2. **"Nearly unreachable" still needs fixing** — over large codebases
   it comes up. Docstrings are never a fallback: behavior must be
   identical in practice. Cover all cases, not just expected ones
   (that's why detBiv is Bareiss, not Laplace).
3. Source-fidelity over equivalent-engine + empirical check: port the
   mechanism (the F3 restore-ordering bug was found by re-reading z3
   against the port — that review method works).
4. Parity directive: schedulers only select from the closure; every
   change states its parity argument.
5. No assume/admit/external_body in the trusted layer.
6. Budgets: `withLayerHeartbeats`, never fraction-of-remaining.
7. Implement in this window's style — no coder agents for code
   (Danielle's call); commit freely, small commits.

## Lean traps hit this arc (all recorded in memory)

- Same-named `let rec` in different branches of one def collide —
  name distinctly (walkLo/walkHi/walk4).
- `.ok (a, b)` on a multi-field constructor via anonymous dot-notation
  parses as a `Prod` — write `.ok a b`.
- `partial` needs `Inhabited` on the return type (`deriving
  Inhabited`); a dropped `let rec` tail call surfaces as
  `unexpected token '|'` at the NEXT match arm.
- mathlib ships a root-level `Dyadic` that captures unqualified name
  resolution — kernel type is `Mpbq`.
- `termination_by` + proof-carrying subtype from the finder
  (`maxSmallerThan`) + `decreasing_by all_goals (simp_wf; assumption)`
  works for measure-decreasing walkers inside `do`.
