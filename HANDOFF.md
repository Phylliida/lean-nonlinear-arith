# HANDOFF — 2026-08-09 (post reviews 6–11: R-series CLOSED, G1–G3 done; next = F5 housekeeping → census slice)

Read first: `DESIGN-endgame.md` (master plan — §0 finish line, §2
critical path, §6 decisions + divergence register, §8 standing
directives), then `BOARD.md` — the nla-19a entry has design reviews
3–11, the G1–G10 gap inventory, the F1–F5 decisions, and all landing
blocks. Memory file `verus-cad/memory/project_tactus_nonlinear_port.md`
has the session history. Build: Nix `lake` on PATH (not elan);
`lake build` green (7610 jobs).

**Source-of-truth rule (unchanged): all ports cite
`git show z3-4.12.5:<path>` (repo: `verus-cad/z3`), never the working
tree.**

**Standing directive (Danielle, 2026-08-09): cover ALL cases no matter
how rare — never defer a known gap with "until it shows up in
practice".**

## Where we are

The **12d.6b ⇄ 19a arc is functionally complete at v0**, and the
discharge layer is now complete for ALL ineq-atom shapes:

- **F3** (`Walk.lean`, `nlsat_refute`): the DAG walk over the
  `s.refutation` snapshot — bridged input clauses, per-learned-cid RUP
  (`by decide` + `upRefutes_sound`), F2 arith discharges in sandboxed
  sub-goals, final bundle ⇒ `False`. Goal contract (R-vi):
  `∀ ρ, (∀ C ∈ Cs, clauseHolds ρ atoms C) → False` with Cs = the
  referenced input clauses in cid order (mismatch rejects).
- **F4 acceptance**: regeneration stability (dump printer ↔ WalkTests
  defs byte-identical), fs1/fs2 factorSplit drivers walked end-to-end.
- **G1** (`Refute.zeroProductClose`): zero-product eq-implication
  lemmas at any factor degree — native `MPoly.factorM` (untrusted) +
  kernel-verified identity (evalP simp + `ring`) + `mul_ne_zero`/
  `pow_ne_zero` chain. fs3/fs4 positive pins; fs3FinalBad soundness
  probe.
- **G2/G3** (`Refute.extractFacts` multi-factor/even-parity paths):
  trusted `holds_multi_*` family in Check.lean; per-factor diseqs feed
  the zero-product index; sign facts via `oddProd`.
- **R-series closed**: R-d sign-flipped factor matching (`MPoly.neg`
  kernel-reduces; `evalP_neg` + `neg_ne_zero`); R-b multi-eq-positive
  via the `List.prod`-of-evals restatement + `listEvalProd_ne_zero`
  (NO factorization needed — factors given); R-a FULL: flat `negChain`
  expansion + Or-splitting in `closeWithSplits` (`findOr` + `g.cases`,
  before the diseq trichotomy). NB: the per-factor RECURSIVE expansion
  of a negative sign atom is mathematically WRONG (odd-product sign
  couples odd factors) — the flat form is the right one.
- **Review 11 audit**: split fuel is clause-sized (no arbitrary bound);
  degenerate shapes pinned (empty-factor eq/lt, all-even lt).

**The ONLY remaining `extractFacts` skip class: root atoms** — owned
by the census slice (G4), which is scheduled with a recipe, not
deferred.

## Next: F5 housekeeping (R8 + R1'), then the census slice (G4)

F5: split `Check.lean` into Semantics/Discharge; unify discharge
hypotheses on full `MPoly.Canon`; normalize `↑0`-form hypotheses to
`(0 : ℝ)`.

Census slice (G4): grammar-coverage census — per grammar shape, is the
arith-clause contradiction literal-local (closes from literal failures
+ glue) or not? Non-local cases get step-fact collection via the
Coverage theorems (recipe on the BOARD: `coverage_linearRoot`/
`coverage_thomQuadratic` assembly, R-iii root-order injection, R-ii
by-value reconstruction). `rootGeneric` definite-disc is the known
member. The √2-grade goal (x0≥0 ∧ x0²≥2 ∧ x0≤1, load-bearing
cellBound) lands here. Review-6 F-w parked here: mkNeg/sp
payload-corruption probes + optional decidable `grammarOK` lint.

## R-e (recorded, with fix sketch)

Zero-product reasoning inside an Or-split BRANCH is not covered: the
fact indexes (eqFacts/diseqFacts/prodEqFacts) are built pre-mangle, and
post-split branch contexts only get the glue (the indexed fvars' types
are mangled by then — `zeroProductClose`'s `evalP`-form assumptions
break). Requires a negative multi-factor sign atom AND a separate
factorization-depth-≥3 conflict in the SAME arith lemma. Fix sketch:
unfold `negChain` at EXTRACTION time (build the nested-Or type directly
instead of via the def), run Or-splits BEFORE zero-product closes, and
re-index branch contexts (extractFacts per branch literal is already
shape-driven — the machinery reuses). No z3-faithful trace observed to
need it; when implementing, the BOARD entry has the full analysis.

## Session mechanics (F3/F4 workflow)

- **Adding a dump case**: copy a `goN` in `scratch_dump.lean`'s
  `DumpDriver` (init, mkVar per var, mkIneqLiteral per atom, mkClause
  per input unit clause, `Solver.check (Solver.resolve Explain.explain)`),
  add `printSnap "<name>"` in main, `lake env lean --run scratch_dump.lean`.
  Output is paste-ready `private def`s (anonymous `⟨steps, lemma⟩`
  form — `lemma` is reserved). Goal input list for `nlsat_refute` =
  referenced input clauses in cid order.
- **Probe debugging**: `#guard_msgs (drop error)` swallows messages —
  copy the file to a scratch, strip the guard lines, `lake env lean`
  it, delete after. **Corrupted-trace probes must keep the goal's
  input list = the corrupted trace's REFERENCED inputs** (a dropped
  clause antecedent changes the referenced set and the contract gate
  fires first).
- Full build: `lake build` (green = 7610 jobs).

## Traps / lessons (reviews 6–11)

- **`Meta.evalExpr` of a bare FUNCTION const mis-evaluates on this
  toolchain** (v4.25.0 Nix): full APPLICATION exprs evaluate correctly.
  All native checks live in compiled `Walk.precheck`-style functions
  consumed via a single application evalExpr. Root cause open.
- **`mkApp` applies args to leading IMPLICIT binders** — `mkAppM` for
  implicit-prefix heads; `mkAppM f #[]` ERRORS ("result contains
  metavariables") when all binders are implicit — use `mkAppOptM` and
  pin them (e.g. `Int.cast_ne_zero {α} [inst] [inst2] {n}`); pin `Real`
  explicitly in `Int.cast`/`OfNat.ofNat` (else the ring arg stays an
  mvar and `ring` can't run).
- **`Classical.byContradiction : (¬p → False) → p`** in 4.25 core.
- **`List.mem_cons` binder order is `{α} {b} {l} {a}`** (element LAST);
  `List.forall_mem_cons` is `{α} {p} {a} {l}`; `List.forall_mem_nil` is
  `{α} (p)`. `List.prod_ne_zero` takes `0 ∉ l` (not the ∀ form).
- **`lemma` is a RESERVED WORD in 4.25** — `TraceBundle` literals use
  the anonymous `⟨steps, lemma⟩` form.
- **`push_neg` on `¬(a ≠ 0)` already yields `a = 0`** (no
  `not_not.mp`).
- **Tactic quotations' simp sets elaborate at RUNTIME** — deleting a
  def does NOT break the build of files whose `simp only [...]` names
  it; check by hand.
- **Well-founded-compiled `MPoly.mul` etc. do NOT reduce under kernel
  whnf/rfl/decide** (kernel-reduction trap): atom tables in literal-list
  form; defeq-matching natively-computed products against
  `MPoly.mul`-containing types fails — restate types in `List.prod`
  form instead (the R-b solution).
- **`match` on pair patterns `(f, _) :: rest` can get stuck under
  whnf on variables** — use `g :: rest` + `g.1` projections instead
  (the `negChain` shape).
- Core polarity: `arithClause core proj = proj ++ ¬core` — hand-written
  test cores invert into the clause (bit me twice; the checker
  correctly refused the invalid clauses).
- `command grep` on this box (bare `grep` is aliased weirdly); check
  `uptime` before timings; `setGoals` not `replaceMainGoal` (empty-goal
  trap); `#guard_msgs (drop error)` takes the command's DOCSTRING as
  the expected message (plain `/- -/` on rejection probes);
  withContext for all meta ops touching context fvars; mutating outer
  `let mut` vars inside `.withContext do` lambdas doesn't work —
  thread values out and mutate outside.

## Roadmap after the census slice

19b (pseudoDivision/factorSplit identities → M3; `ordering_139`
standing target), 12e (integer branch-and-bound — solver-side too),
14 (the `nonlinear_arith` tactic, `withLayerHeartbeats`), 15 (tactus
wiring, ~½ session), 16 (parity harness; owns G8/G9/G10 measurement:
glue-heuristic tail, RUP-stall watch, resource ceiling). Tier B (G7,
rootGeneric deg ≥ 3) via the S1 lane (11a resultants ∥ 11c root
continuity — the long pole).
