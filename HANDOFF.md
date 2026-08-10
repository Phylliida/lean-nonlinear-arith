# HANDOFF — 2026-08-10 (reviews 6–15 done; G4 census slice COMPLETE; next = 19b → M3)

Read first: `DESIGN-endgame.md` (master plan — §0 finish line, §2
critical path, §6 decisions + divergence register, §8 standing
directives), then `BOARD.md` — the nla-19a entry has design reviews
3–15, the G1–G10 gap inventory, the F1–F5 decisions, and all landing
blocks. Memory file `verus-cad/memory/project_tactus_nonlinear_port.md`
has the session history. Build: Nix `lake` on PATH (not elan);
`lake build` green (7612 jobs).

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

The **12d.6b ⇄ 19a arc is functionally complete at v0**, the discharge
layer covers ALL ineq-atom shapes unconditionally, and now the **G4
census slice is COMPLETE** (reviews 13–15; root atoms were the last
`extractFacts` skip class):

- **F3** (`Walk.lean`, `nlsat_refute`): the DAG walk — bridged input
  clauses, per-learned-cid RUP (`by decide` + `upRefutes_sound`), F2
  arith discharges in sandboxed sub-goals, final bundle ⇒ `False`.
  Goal contract (R-vi): `∀ ρ, (∀ C ∈ Cs, clauseHolds ρ atoms C) →
  False`, Cs = referenced input clauses in cid order (mismatch
  rejects). **Grammar gate (G4)**: `precheck` also requires every
  bundle's steps to satisfy `grammarOK` (native compute) — corrupted
  payloads reject before any discharge work.
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
  audit CLEAN; **R2' FIXED (review 14)**: duplicate-literal UP stalls
  via `List.dedup` at the four decide sites + trusted dedup bridges.
- **G4 census slice COMPLETE (review 15)** — all five items:
  1. `grammarOK` decidable grammar mirror + `grammarOK_sound`
     (Trace.lean).
  2. root-atom extraction + `rootDefiniteClose` (deg-2 neg-disc /
     deg-2 A=B=0 / deg-1 A=0 lanes) + kernel-checked
     concrete-coefficient reducer (`reduceAdd`/`reduceGo`/
     `coeffsOfValue`).
  3. **Step-fact collection** (`Refute.collectStepFacts` — the
     cross-links census member): per `.arith` marker the bundle's
     preceding projection steps are consumed; for each encoding step
     matched against an extracted root fact `(k, y, i, p)`, the opaque
     `rootCmp k (ρ y) (rootVal …)` converts into glue-ready
     first-order facts. Lanes: **linearRoot** direct (kind×polarity
     coverage: lt/gt/eq → not-not, le/ge → mt — table-pinned),
     **sa = 0 degenerate reroute** (`rootVal_eq_degenerate` +
     coefficient links + `rootVal_eq_linear`; A = 0 sign literal
     load-bearing), **encoding-free lane** (foreign traces: deg-1
     const-lc converts with no step — grammar-free sound insurance),
     **thomQuadratic** (`thom_discharge` + `rootVal_eq_quad` in RAW
     coefficient-expansion form; `leadSgn` resolved via
     `leadSgn_of_pos`/`leadSgn_of_neg`; accessors rewritten at the
     noted formula so `simp only [thomFormula]` yields Or/And
     comparisons `findOr` consumes). Every production is a
     kernel-checked term; missing evidence skips soundly.
  4. **F-w probes pinned**: mkNeg corrupt (grammar-BREAKING) → reject;
     sq mismatch (grammar-clean, semantic mismatch) → skip ⇒
     load-bearing reject; sq=0 with sp≠0 (E1 placeholder, both
     grammar-gate and consumption-time) → reject. sp-values inside
     valid ranges are unconsumed by the certificates — accepted-trace
     SUPERSET is sound by kernel checking (review-6 F-w semantics).
  5. Review 15 on BOARD: audit, traps, honest inventory.
- **New trusted mirror**: `Monomial.canonOK`/`MPoly.canonOK` +
  soundness (TypesOrder) — the canonicity `decide` ticket the
  Semantics docstring promised; used by all step-consumption lanes.

**Imported fixtures (all pinned, RefuteTests + WalkTests)**: thom
const lane (x²−2), thom clause lane (multivariate by-value
discPoly-of reconstruction), linear lt/eq/ge/le table, degenerate
reroute const-lc + non-const-lc (clause lane), encoding-free foreign
bilinear, xl end-to-end walk fixture + load-bearing + grammar-gate
variants, per-fixture load-bearing negative probes.

## Next: 19b (pseudoDivision/factorSplit identities → M3)

Per DESIGN-endgame §2 the census slice closes G4; the roadmap is:
**19b** (G5 — pseudoDivision/factorSplit per-instance ring identities
+ parity cases → M3; `ordering_139` is the standing end-to-end target
if its trace stays in fragment), **12e** (G6 — integer
branch-and-bound: search-side port of z3's nra/nlsat branch policy as
trace steps; checker-side each split is an omega-trivial disjunction),
**nla-14** (the `nonlinear_arith` tactic: L1 saturate → L2/L3
search+check, `withLayerHeartbeats`, Int→Real atom mapping; owns the
F-y alignment contract), **nla-15** (tactus wiring, ~½ session),
**nla-16** (parity harness over the workspace corpus; gate = zero
sites Z3 closes that we don't; owns G8/G9/G10 measurement; M6 closes
here). Tier B (G7, rootGeneric deg ≥ 3) stays via the S1 lane (11a
resultants ∥ 11c root continuity — the long pole). Parked
candidates: R-q rootCount-evaluation lane (const-coefficient deg-2
count contradictions — see review 15's honest inventory), sq=0 Thom
fixture (grammar admits; production supports; orthogonal to R-q).

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
  Name throwaways accordingly.
- Full build: `lake build` (green = 7612 jobs); module-scoped:
  `lake build LeanNonlinearArith.Nlsat.X`.
- Refute-level pinning for step work: `nlsat_arith_valid_steps`
  (takes the steps term, runs F2 including step-fact collection);
  `nlsat_arith_valid` is the no-steps variant.

## Traps / lessons

Reviews 3–14 (kept): `Meta.evalExpr` of a bare FUNCTION const
mis-evaluates (full applications fine); `mkApp` applies to leading
implicit binders (use `mkAppM`; `mkAppM f #[]` needs `mkAppOptM` +
pins); `Classical.byContradiction : (¬p → False) → p`; `lemma` is a
reserved word (anonymous `⟨steps, lemma⟩` TraceBundle literals);
tactic-quotation simp sets elaborate at runtime; **wf-compiled
`MPoly.mul`/`add` do NOT reduce under kernel whnf/rfl/decide**
(ride equation-lemma bridges: `MPoly.add_cons_cons_*`,
`coeffsOf_go_cons`; two-hop congrArg + rfl-defeq; always
withLocalDecl+mkLambdaFVars for congr lambdas; `absurd`'s Sort
binder needs pinning); `List.mem_cons` binder order (element LAST);
`List.dedup` kernel-reduces on literals (`List.mem_dedup` the bridge);
evalTactic mangles assign the goal mvar (take `← getMainGoal` after);
mathlib nlinarith internals (ONE product round, equality hyps pair
with everything); the arith-clause polarity inversion (`core` inverts
into the clause); `#guard_msgs (drop error)` takes the DOCSTRING —
use `/- -/` on rejection probes; `let mut` doesn't mutate across
`.withContext do` — thread values out.

Review 15 additions (G4 census):
- **`matches` is a reserved word** (like `lemma`).
- **No `ToExpr RootKind`/`ToExpr TraceStep`** — hand-quote
  (`rootKindToExpr`/`thomStepToExpr` in Refute.lean).
- **`mkAppM ``decide` does NOT synthesize the `Decidable` instance** —
  use `mkAppOptM … #[some goal, none]`; `grammarOK` on the
  `coeffsIn` route is kernel-incomputable (`MPoly.add` wall) — the
  linear grammar ticket is CONSTRUCTED from the reducer +
  `coeffsOf_getElem!_eq`, not decided.
- **`Eq.trans` cannot serve as Prop transport through a congrArg'd
  prop-family** — `Eq.mpr` is the combinator (the hAs nível error);
  `Or.inr`/`Or.inl` under `mkAppM` need side-Prop pins (`mkAppOptM`)
  or HOU mvars linger ("result contains metavariables").
- **`v < 0` is a Prop, `decide (v < 0)` the Bool** (`mkNeg := v < 0`
  silently becomes Prop-typed).
- **`OfNat.ofNat`'s raw literal is Nat** (`toExpr (1 : Nat)`, not
  `(1 : Int)` — the value-side close then fails oddly).
- **`whnf`-indexing into `em`-projections can panic** (index out of
  bounds) — rebuild `IneqAtom.Holds` propositions natively instead
  (hand-quoted `IneqKind` + structure ctor).
- Polarity table for the linear collapse: `eq/lt/gt →` emitted
  polarity true (`¬SHolds = ¬¬Holds`, route `Iff.mp not_not`),
  `le/ge →` false (`¬Holds`, route `mt (Iff.mpr …)`). The inversion
  was caught by the lt fixture — pin both routes.
- Split-fuel budgets must count step-produced Or carriers: review-11
  clause-based fuel now `× 2^(matched disjunctive thomOrs)`.
- `Grammar.linearRoot`'s implicit `{j, i, p, mkNeg, lcFact}` binders
  need `mkAppOptM` pinning or `?lcFact`'s match can't reduce.

## Roadmap after 19b

12e (G6 integer b&b), 14, 15, 16 (parity harness; M6). Tier B (G7,
rootGeneric deg ≥ 3) via the S1 lane (11a resultants ∥ 11c root
continuity — the long pole). Background/parked: L1 hardening (nla-07b
meta-Buchberger, nla-06 simplex model, nla-21 shared atom space,
nla-22 work-queues), nla-30, nla-31 termination proofs (refineNzBound
first), M5 containment writeup, R-q rootCount let-evaluation lane.
