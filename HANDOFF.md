# HANDOFF — 2026-08-10 (reviews 3–15 done; G4 census COMPLETE; NEXT = 19b → M3)

Read first: `DESIGN-endgame.md` (master plan — §0 finish line, §2
critical path, §8 standing directives), then `BOARD.md` — the
nla-19a entry has design reviews 3–15, the G1–G10 gap inventory, the
F1–F5 decisions, all landing blocks. Memory file
`verus-cad/memory/project_tactus_nonlinear_port.md` has the session
history. Build: Nix `lake` on PATH (not elan); `lake build` green
(7612 jobs, commit 60b0038).

**Source-of-truth rule (unchanged): all ports cite
`git show z3-4.12.5:<path>` (repo: `verus-cad/z3`), never the working
tree.**

**Standing directive (Danielle, 2026-08-09): cover ALL cases no matter
how rare — never defer a known gap with "until it shows up in
practice".**

## Where we are

The discharge layer is complete through the **G4 census slice**
(reviews 3–15). No un-owned known gaps remain; the last
`extractFacts` skip class (root atoms) is closed.

- **F3/F4 walk** (`Walk.lean`, `nlsat_refute`): bridged input clauses,
  per-learned-cid RUP (`by decide` + `upRefutes_sound`), F2 arith
  discharges, final bundle ⇒ `False`. Grammar gate (G4): `precheck`
  rejects bundles whose steps fail `grammarOK` (native).
- **Discharge completeness** (R-series complete): zero-product close
  with native `factorM` + kernel identity check; multi-factor /
  even-parity / negChain / chain-in-branch extraction and splitting.
- **Census slice (G4)** — all five items: grammarOK decidable mirror;
  root-atom extraction + rootDefiniteClose + kernel-checked reducer
  (`coeffsOfValue`); **step-fact collection**
  (`Refute.collectStepFacts`) — linear/Thom cross-links, degenerate
  reroute, encoding-free lane, all lanes pinned incl. le/ge Thom
  (review-15 addendum: fuel `thomDisjunctive` table verified
  cell-by-cell vs `Semantics.thomFormula`); F-w corruption probes;
  review 15 close-out. Fuel budget clause-shaped × 2^thomOrs.
- **Data**: machine-generated WalkTests snapshot defs; four end-to-end
  walks + probes; Refute-level fixtures for every production lane.

## Next: nla-19b — full checker glue → M3 *(1–2 sessions)*

**Slice 0 DONE (2026-08-10, see BOARD "nla-19b Slice 0"):**
simplify-cluster drivers pd1/pd2/pd3/pd4/pd6 in `scratch_dump.lean`
(all refute; payloads + paths censused); structural findings R-a..R-i
(reorder live in pd3; **path (e) `normalizeLit` is UNREACHABLE for
in-core simplify — (c)/(d) only; (e) is x2eq-lower-stage-only**;
const-drops create empty atoms never in clauses; all four lc lanes +
lcConst lane witnessed; parity quadrant complete). **Standing-target
RESOLVED: M3 acceptance driver = pd1** (`x1−x0²=0 ∧ x1<0`;
in-fragment, fully quadratic, pseudoDivision-bearing, multi-bundle
DAG). **NEW ITEM (search-side, 12c/explain territory, NOT 19b):
ordering_139 raw-form search diverges** — our port ≥60 min/5.8 GB
killed twice; z3 4.16 classic config (`nlsat.lws=false
nlsat.randomize=false`) refutes instantly (6 conflicts, param parity
confirmed; front-end preprocessing caveat open). Debug recipe on
board. Unexercised lanes for Slice 2 synthetics: (c) keep-original,
(e)/x2eq, isEven=true, d≥3.

Per DESIGN-endgame §2.5: **`pseudoDivision` per-instance ring
identities + parity cases.** Scope (already on the board):

- **R7 is why:** pseudoDivision is NOT safe to ignore — the simplify
  cluster REWRITES literals (the A3 rebuilt-literal sites :471/:1194
  with kind-flip + neg fold, A4 lc ineq :1259, A5 lc diseq :1261 —
  the A-tier provenance enumeration), and the identity can be the
  semantic link the final derivation needs. v0 currently rejects such
  bundles (`isV0` gate at Walk.lean + `preform`); F5 emission already
  emits the steps (undischarged).
- **factorSplit identity is NOT in this slice**: R6 (board, approved)
  — ignoring factorSplit steps loses NO coverage; don't pull it
  forward.
- **What to build** (extend grammar + coverage *in the same pattern*
  as the census slice, per the 19a design note):
  1. `grammarOK`/`Grammar` extension for `pseudoDivision` steps
     (payload shape, from the F5 emission + z3 source), preference
     for decide-grade tickets like the item-1/3 pattern — watch the
     kernel-reduction trap (the `coeffsIn` wall keeps `grammarOK`'s
     decide version of poly-equality checks kernel-incomputable;
     construct with the `coeffsOfValue` reducer, as
     `mkLinearRootGrammar` does).
  2. Trusted Discharge theorems: the pseudo-remainder sign-invariance
     identity (board G5 row names it: "verified pseudo-remainder sign
     invariance") — the numeric content of
     `pseudoDivisionCore` (12d.1b-i, `Nlsat/MPolyOps.lean`, done);
     per-instance `evalP` ring identities (closure via the evalP
     simp set, same idiom as `zeroProductClose`'s `ring` hop).
  3. Refute-side consumption: rewritten/merged literal handling —
     the simplify cluster's literal can arrive REBUILT (A3: kind-flip
     + neg fold), so `extractFacts` must normalize rebuilt literals
     against the step payloads (this is the genuinely new extraction
     work; pinned per shape with the F2-seam decode discipline).
  4. Lift the `isV0` pseudoDivision gate once 1–3 are pinned; boards
     have warned mitigation: pin which emission shapes each acceptance
     driver actually emits (keep `intBranch` gated → 12e).
- **Standing targets:** `ordering_139` (the L1-open specimen,
  degree-3 cross products) **if** its trace stays in fragment; else
  the first fully-quadratic census row. End-to-end acceptance:
  census-shaped goal through search → trace → checked theorem.
- **Effort estimate (2026-08-10):** 1–2 sessions; risk concentrated in
  (3) — rebuilt-literal extraction is new-shape work, the rest is
  established idiom.

## Roadmap after 19b

**12e** (G6 → M4, 1–2 sessions): integer branch-and-bound — port z3's
integer branching policy (`x ≤ ⌊v⌋ ∨ x ≥ ⌈v⌉`) as trace steps;
checker-side each split is an omega-trivial disjunction, so this is
mostly search-side; confirm the exact branch site (nra_solver.cpp /
nlsat's mk_branch analogue) before porting. Then L2's polynomial atoms
only invariant at the frontend boundary.
**nla-14** (2–3 sessions): the `nonlinear_arith` front-end tactic —
L1 fast path → L2/L3 search+check, `withLayerHeartbeats` (per-layer
fresh budget, never fraction-of-remaining), Int→Real mapping,
hypothesis selection; owns F-y. Largest remaining piece; candidate
for a small standalone first slice (hypothesis ingestion + atom
mapping).
**nla-15** (~½ session): tactus wiring. **nla-16** (1–2 sessions +
findings): parity harness over the workspace corpus; gate = zero
sites Z3 closes that we don't; owns G8/G9/G10 measurement. **M6
closes there.**
**Tier B** (G7, rootGeneric deg ≥ 3, 3–6 sessions, high variance):
the S1 lane — nla-11a resultants ∥ 11c root continuity — the long
pole; defer unless 16's measurement shows the corpus needs it.

Total-to-M6 estimate (2026-08-10): **~6–10 sessions**.

Parked (owners on the board): L1 hardening (nla-07b meta-Buchberger
2–3 sessions, nla-06, nla-21, nla-22 — none block M3, all block
calling L1 port-complete for M5's writeup), nla-30, nla-31
termination proofs (refineNzBound first), M5 containment writeup
(~½ session), R-q rootCount-evaluation lane, sq=0 Thom fixture.

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
  `scratch_dump.lean`/`scratch_probe.lean`.
- Full build: `lake build` (green = 7612 jobs); module-scoped:
  `lake build LeanNonlinearArith.Nlsat.X`.
- Refute-level pinning for step work: `nlsat_arith_valid_steps`
  (steps term + F2 incl. step-fact collection); `nlsat_arith_valid`
  for the no-steps variant.

## Traps / lessons

Reviews 3–14 (kept): `Meta.evalExpr` of a bare FUNCTION const
mis-evaluates (full applications fine); `mkApp` applies to leading
implicit binders (`mkAppM`; `mkAppM f #[]` → `mkAppOptM` + pins);
`lemma` is a reserved word (anonymous `⟨steps, lemma⟩` TraceBundle
literals); tactic-quotation simp sets elaborate at runtime;
**wf-compiled `MPoly.mul`/`add` do NOT reduce under kernel
whnf/rfl/decide** (ride equation-lemma bridges: `MPoly.add_cons_cons_*`,
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

Review 15 additions (G4 census): `matches` is reserved; no
`ToExpr RootKind`/`ToExpr TraceStep` (hand-quote); `mkAppM ``decide`
doesn't synthesize the instance (`mkAppOptM … none`); `grammarOK`'s
`coeffsIn` branch is kernel-incomputable (`MPoly.add` wall) — build
the linear grammar ticket from the reducer + `coeffsOf_getElem!_eq`;
`Eq.mpr` (NOT `Eq.trans`) for congrArg'd prop-family transports;
`Or.inr` needs side-Prop pins under `mkAppM` (`mkAppOptM`);
`v < 0` is a Prop, `decide (v < 0)` the Bool; `OfNat.ofNat` raw
literal is Nat; `whnf`-indexing into em-projections can panic —
rebuild `IneqAtom.Holds` natively; linear collapse polarity table:
eq/lt/gt → `¬¬Holds` (route `Iff.mp not_not`), le/ge → `¬Holds`
(route `mt (Iff.mpr …)`) — the inversion is real and the lt fixture
caught it; split-fuel must count step-produced Ors (clause-part
× 2^thomOrs); `Grammar.linearRoot` implicit binders need
`mkAppOptM` pinning (its `?lcFact` match won't reduce otherwise).
