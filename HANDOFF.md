# HANDOFF — 2026-08-10 (reviews 6–14 done; R-series + R2' COMPLETE, no un-owned gaps; next = F5 housekeeping → census slice)

Read first: `DESIGN-endgame.md` (master plan — §0 finish line, §2
critical path, §6 decisions + divergence register, §8 standing
directives), then `BOARD.md` — the nla-19a entry has design reviews
3–14, the G1–G10 gap inventory, the F1–F5 decisions, and all landing
blocks. Memory file `verus-cad/memory/project_tactus_nonlinear_port.md`
has the session history. Build: Nix `lake` on PATH (not elan);
`lake build` green (7610 jobs).

**Source-of-truth rule (unchanged): all ports cite
`git show z3-4.12.5:<path>` (repo: `verus-cad/z3`), never the working
tree.**

**Standing directive (Danielle, 2026-08-09): cover ALL cases no matter
how rare — never defer a known gap with "until it shows up in
practice".** Its harness-level twin now lives in
`~/.hermes/config.yaml`'s `agent.system_prompt` (2026-08-10): "Depth
is unlimited; scope is exact … widen it once, say so … Finished-late
ages better than partial-on-time …".

## Where we are

The **12d.6b ⇄ 19a arc is functionally complete at v0**, and the
discharge layer is complete for ALL ineq-atom shapes, unconditionally:

- **F3** (`Walk.lean`, `nlsat_refute`): the DAG walk — bridged input
  clauses, per-learned-cid RUP (`by decide` + `upRefutes_sound`), F2
  arith discharges in sandboxed sub-goals, final bundle ⇒ `False`.
  Goal contract (R-vi): `∀ ρ, (∀ C ∈ Cs, clauseHolds ρ atoms C) →
  False`, Cs = referenced input clauses in cid order (mismatch
  rejects).
- **F4 acceptance**: dump printer ↔ WalkTests defs byte-identical;
  fs1/fs2 drivers walked end-to-end.
- **G1** `Refute.zeroProductClose` (native `factorM` + kernel-verified
  identity + ne-chain); **G2/G3** `extractFacts` multi-factor /
  even-parity paths (`holds_multi_*` in Check.lean).
- **R-series COMPLETE**: R-d sign-flip factor matching (`evalP_neg` +
  `neg_ne_zero`); R-b multi-eq-positive via `List.prod`-of-evals +
  `listEvalProd_ne_zero`; R-a FULL via flat `negChain` expansion +
  Or-splitting glue (NB: the per-factor RECURSIVE expansion is
  mathematically WRONG — odd-product sign couples odd factors);
  **R-e** (review 12): `chainLoop` splits negChain facts PRE-mangle
  via `g.cases`, extending the eq index per branch — zero-product
  closes work inside Or-split branches. Review-13 z3-divergence
  audit CLEAN (z3 atoms always sz≥1 and lm-sign-normalized; our
  empty-factor/sign-flip handling is deliberate superset).
- **R2' FIXED (review 14)**: duplicate literals stalled UP propagation
  (`clauseStatus [l,l]-un → .other`); dedup at the walk's decide sites
  (`rupNode`, final bundle, `precheck` mirror) — trusted bridges
  `clauseSatI_dedup`/`not_litSatI_forall_dedup` (one-liners via
  `List.mem_dedup`). Stall needs EVERY clause duplicated (pinned
  pre/post).
- Review 11: split fuel is clause-sized (no arbitrary bound);
  degenerate shapes pinned (empty-factor eq/lt, all-even lt,
  two-chain clauses, single-factor even-marked negative lt).

**No un-owned known gaps remain** (review 14 ownership audit). The
ONLY remaining `extractFacts` skip class is root atoms — owned by
the census slice (G4).

## Next: F5 housekeeping (R8 + R1'), then the census slice (G4)

F5: split `Check.lean` into Semantics/Discharge; unify discharge
hypotheses on full `MPoly.Canon`; normalize `↑0`-form hypotheses to
`(0 : ℝ)` annotations (R1', approved; see BOARD review 3).

Census slice (G4): grammar-coverage census — per grammar shape, is the
arith-clause contradiction literal-local (closes from literal failures
+ glue) or not? Non-local cases get step-fact collection via the
Coverage theorems (recipe on the BOARD: `coverage_linearRoot`/
`coverage_thomQuadratic` assembly, R-iii root-order injection, R-ii
by-value reconstruction). `rootGeneric` definite-disc is the known
member. The √2-grade goal (x0≥0 ∧ x0²≥2 ∧ x0≤1, load-bearing
cellBound) lands here. Review-6 F-w parked here: mkNeg/sp
payload-corruption probes + optional decidable `grammarOK` lint.

## Session mechanics (F3/F4 workflow)

- **Adding a dump case**: copy a `goN` in `scratch_dump.lean`'s
  `DumpDriver` (init, mkVar per var, mkIneqLiteral per atom, mkClause
  per input unit clause, `Solver.check (Solver.resolve
  Explain.explain)`), add `printSnap "<name>"` in main,
  `lake env lean --run scratch_dump.lean`. Output is paste-ready
  `private def`s (anonymous `⟨steps, lemma⟩` form — `lemma` is
  reserved). Goal input list for `nlsat_refute` = referenced input
  clauses in cid order.
- **Probe debugging**: `#guard_msgs (drop error)` swallows messages —
  copy to a scratch, strip the guards, `lake env lean` it, delete
  after. **Corrupted-trace probes must keep the goal's input list =
  the corrupted trace's REFERENCED inputs.**
- **Scratch probes**: `scratch_*.lean` is gitignored EXCEPT
  `scratch_dump.lean`/`scratch_probe.lean` (tracked intentionally).
  Name throwaways accordingly (added 2026-08-10 after scratch_sig
  got committed twice).
- Full build: `lake build` (green = 7610 jobs); module-scoped:
  `lake build LeanNonlinearArith.Nlsat.X`.

## Traps / lessons (reviews 3–14)

- **`Meta.evalExpr` of a bare FUNCTION const mis-evaluates** (v4.25.0
  Nix): full APPLICATION exprs evaluate correctly. All native checks
  in compiled `Walk.precheck`-style functions consumed via a single
  application evalExpr. Root cause open.
- **`mkApp` applies args to leading IMPLICIT binders** — `mkAppM` for
  implicit-prefix heads; `mkAppM f #[]` ERRORS ("result contains
  metavariables") when all binders implicit — `mkAppOptM` and pin
  (e.g. `Int.cast_ne_zero`); pin `Real` explicitly in `Int.cast`/
  `OfNat.ofNat`.
- **`Classical.byContradiction : (¬p → False) → p`** in 4.25 core.
- **`List.mem_cons` binder order `{α} {b} {l} {a}`** (element LAST);
  `List.forall_mem_cons` `{α} {p} {a} {l}`; `List.forall_mem_nil`
  `{α} (p)`. `List.prod_ne_zero` takes `0 ∉ l` (not the ∀ form).
- **`lemma` is a RESERVED WORD in 4.25** — `TraceBundle` literals:
  anonymous `⟨steps, lemma⟩` form.
- **`push_neg` on `¬(a ≠ 0)` already yields `a = 0`**.
- **Tactic quotations' simp sets elaborate at RUNTIME** — deleting a
  def does NOT break the build of files whose `simp only [...]` names
  it; check by hand.
- **Well-founded-compiled `MPoly.mul` etc. do NOT reduce under kernel
  whnf/rfl/decide** (kernel-reduction trap): atom tables in
  literal-list form; restate types in `List.prod` form (the R-b
  solution). **`match` on pair patterns `(f, _) :: rest` can get stuck
  under whnf on variables** — use `g :: rest` + `g.1`.
- **`List.dedup` kernel-reduces on concrete literals** (`rfl`-probed)
  and `List.mem_dedup` is the iff bridge; core `List.eraseDups` is the
  alternative if mathlib's pwFilter form ever misbehaves.
- **evalTactic mangles (simp/ring_nf) ASSIGN the goal mvar** — after
  mangling pass `← getMainGoal` (the fresh mvar), not the pre-mangle
  one ("metavariable already assigned" symptom). `CasesSubgoal`
  inherits `fields` from `InductionSubgoal` (no `fieldHyps` in 4.25).
- **mathlib nlinarith internals (review 12)**: `removeNe` splits `≠`
  hyps itself; the product round pairs EQUALITY hyps with everything
  (`zero_mul_eq`/`mul_zero_eq`); ONE round only, no
  products-of-products — degree-3 factorization conflicts with sign
  facts in a different variable escape it (witness-engineering note
  for discharge tests: even-mark the target factor, put helper sign
  facts in another variable).
- Core polarity: `arithClause core proj = proj ++ ¬core` — test cores
  invert into the clause (bit me twice; the checker correctly refused
  the invalid clauses).
- `command grep` on this box; check `uptime` before timings;
  `setGoals` not `replaceMainGoal` (empty-goal trap); `#guard_msgs
  (drop error)` takes the command's DOCSTRING as expected message
  (plain `/- -/` on rejection probes); withContext for meta ops on
  context fvars; `let mut` outer vars don't mutate inside
  `.withContext do` lambdas — thread values out.

## Roadmap after the census slice

19b (pseudoDivision/factorSplit identities → M3; `ordering_139`
standing target), 12e (integer branch-and-bound — solver-side too),
14 (the `nonlinear_arith` tactic, `withLayerHeartbeats`), 15 (tactus
wiring, ~½ session), 16 (parity harness; owns G8/G9/G10 measurement).
Tier B (G7, rootGeneric deg ≥ 3) via the S1 lane (11a resultants ∥
11c root continuity — the long pole).
