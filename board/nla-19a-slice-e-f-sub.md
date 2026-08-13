## nla-19a Slice E/F sub-slice plan (2026-08-06, planning session)

Sub-slice breakdown of the NEXT block above.

**Slice E — Q1 coverage lemma:**
- **E1** finalize `Trace.Grammar` (currently DRAFT, Trace.lean:220):
  line-by-line audit of each constructor vs
  `git show z3-4.12.5:src/nlsat/nlsat_explain.cpp` at the cited lines,
  RULES.md provenance style. Open point: the Q1 enumeration's A1–A5
  INEQ-LITERAL shapes (:280/:289/:471/:1194/:1259/:1261) are clause-
  literal shapes, not step shapes — decide where that contract lives
  (candidate: the F2 clause-decode contract, not `TraceStep.Grammar`)
  and record the decision here.
- **E2** prove coverage as ONE consumable theorem, not a paper claim:
  `Grammar s → s.inFragment → (step obligation)` per constructor,
  shaped so the F assembly calls it directly (linearRoot →
  `linearRoot_discharge`; thomQuadratic → `thom_discharge`; cellBound →
  wrappers; rootGeneric deg ≤ 2 → `rootGeneric_discharge` + no-roots
  rule; leafNumeric → glue/CertGen). If any constructor's obligation
  outruns the S3 family, extend the family first (standing rule).
- **E3** drop the DRAFT marker; update BOARD/HANDOFF.

**E1 audit DONE (2026-08-06).** Method: full re-read of the
4.12.5 explain source (:211-:1368 — sign/ensure_sign, add_zero_
assumption, elim_vanishing, normalize, add_root_literal chain,
add_cell_lits, simplify cluster) against every `TraceStep.Grammar`
constructor. Findings, all FIXED in Trace.lean same day:
1. **const-lcFact gap (the real one):** `mk_plinear_root` is reachable
   ONLY via the quadratic degenerate (:811-812; `add_root_literal`'s
   chain :730-731 never tries it), and its lc is the parent
   quadratic's `B` — which CAN be a nonzero constant (then
   `ensure_sign` adds no literal, :845 `is_const` skip, and
   `s = Int.sign B`). The grammar's `c.asConst?.isNone` condition
   rejected those legitimate emissions = contract completeness bug.
   Fixed: lcFact condition is now `c = lc ∧ s ≠ 0 ∧ (c const →
   s = Int.sign c)`. The discharge needed NO change —
   `linearRoot_discharge`'s `hAq` is parametric in the lc-sign
   evidence (const → decide; non-const → the sign literal failing).
2. **thomQuadratic `sp` placeholder:** source computes `sp` only when
   `sq > 0` (:815-817); emission writes `sp = 0` when `sq = 0`.
   Grammar tightened with `sq = 0 → sp = 0` (exact emission range;
   better corruption detection, F4).
3. **linearRoot none-variant tightened** to nonzero const
   (`∃ v, asConst? = some v ∧ v ≠ 0` — :745 SASSERT, port's
   defensive `c == 0` reject).
4. Line-ref drift fixed (:784 → :763-765).
Verified clean (conditions match source exactly): rootGeneric
(`1 ≤ i`, negated literal :733), cellBound (kind/side agreement, both
bounds may emit, ROOT_EQ early-return, :917 max_var filter ⇒
`1 ≤ degreeIn y p`), leafNumeric (marker), the 19b shapes.
**A-tier decision (the E1 open point):** the A1–A5 literal shapes are
CLAUSE-literal provenance, not step well-formedness — they do NOT
belong in `TraceStep.Grammar`. They pin as a per-literal inductive
consumed by the F2-seam decoder (F1 sub-slice; rule 3 — pin when
consumed). Enumeration for that contract (all sites audited): core
literals; A1 zero assumption (:280, also via elim_vanishing :345) —
multi-factor ¬EQ, all is_even=false; A2 sign assumption (:289 via
:427-433/:847/:878) — single-factor, is_even=false, k ∈ {EQ,LT,GT},
incl. the even-factor diseq variant (:429); A3 rebuilt literal
(:471/:1194, kind-flip + neg fold — may collapse to true/false
literal, :435-438/:465/:1248-1251, and false_literal RESETS the core);
A4 lc ineq (:1259); A5 lc diseq (:1261); lower-stage eq assumption
(:1368); root literal (:733); simplify-direct add (:1204). Each is
reconstructible from step payloads + the atom table (factorSplit → A1;
linearRoot/thom signs → A2; pseudoDivision → A3/A4/A5; rootGeneric →
root literal), matching the F4 payload principle.

**E2 DONE (2026-08-06): `Nlsat/Coverage.lean`, build green 7604
jobs, axiom-clean (propext/choice/Quot.sound only).** The coverage
theorems, shaped for direct F-assembly consumption:
`coverage_linearRoot` (grammar + Canon + the lc sign fact ⇒ emitted-
literal failure ⟺ `rootCmp` at `rootVal`; the lc-sign evidence `hAq`
is DERIVED inside — `linearRoot_hAq` — by decide-grade reasoning in
both const cases via the grammar's new `mkNeg` folds, and from the
sign literal failing in the non-const plinear case);
`coverage_thomQuadratic` (grammar + Canon + A/disc sign facts ⇒
`rootCmp` ⟺ Thom region formula at `rootVal`; formula evaluation from
the `spd`/`sp` facts is F2 case work, per plan); `cellBound_plinear`
(the quadratic-degenerate pairing — NEW wrapper closing the gap where
the paired linearRoot is on the reduct `q = B·y+C`; transports along
coefficient links the F1 decoder supplies by value) and
`cellBound_generic` (the fact is the negated root atom failing);
`rootVal_eq_degenerate` (the `A = 0` rootVal unfold). Helpers:
`evalP_eq_of_asConst`, `coeffsOf_getElem!_eq`. No S3-family extension
was needed — the grammar is fully inside the existing kit. Deferred to
F by design: per-`(k,i)` `thomFormula` evaluation, by-value decode
matching, bundle-level pairing decode. **Trap (new class, cost ~1h):
in the `LeanNonlinearArith.Nlsat` namespace context, a standalone
`0` in a statement Prop position can elaborate as `Nat.cast 0`
(OfNat defaulting beats unification — triggered by `[1]!` subterms);
the goal shows `↑0`, which is NOT defeq to `(0:ℝ)` at default
transparency (exact/application mismatch, linarith blind to Int
hyps). Discipline: annotate `(0 : ℝ)` in statements; bridge to
Check.lean's cast-zero hypotheses with goal-directed
`exact_mod_cast`; use `Int.cast_lt_zero.mpr`/`Int.cast_pos.mpr`,
never `exact_mod_cast` in argument position.**

**F0 + F1 + F3-engine DONE (2026-08-06 pm).** F0: `isV0`
reconciled with R1/R6 (rejects only pseudoDivision/intBranch; the
four-shapes reading rejected every real bundle). F1 + the F3 engine:
`Nlsat/Assemble.lean` — decode layer (`litHolds`/`clauseHolds` over the
atom-table snapshot, junk = not-holding = sound direction;
`litSatI`/`clauseSatI` interpretation form + `interp` bridge, with
DECODABILITY hypotheses — the two forms disagree on negated junk
literals by design); `arithClause` (proj ++ ¬core); and the verified
unit-propagation/RUP engine (`upLoop`/`upRefutes`, structural
recursion over literal lists — connective lemmas are plain
inductions): `upRefutes_sound` is the whole trusted content of the R1
replay (completeness for z3's resolution chains = the reverse-
induction RUP argument; stalls reject soundly). Pins in
`AssembleTests.lean` (incl. a negative probe and an end-to-end
soundness application). Build green 7606 jobs, axioms clean.
**Traps:** `List.getElem?_set` is the if-form
`(l.set i a)[j]? = if i = j then (if i < l.length then some a else
none) else l[j]?` — one rewrite covers both self and ne cases;
`_set_self`/`_set_ne` have side conditions/argument orders that make
them worse. `split` on a 2-arm match with a wildcard arm yields 2
goals; it does NOT recurse into nested matches — `revert h; split <;>
intro h <;> simp at h` handles the nested case robustly.
**NEXT: F2** (per-bundle arith-lemma validity — the elaborator that
discharges `arithClause core proj` from the bundle's steps via the
Coverage theorems + linarith/nlinarith glue), then the DAG walk
(per-cid fold + final-bundle close), then F4 acceptance.

**F2 groundwork (2026-08-06 pm, live dump reproduced):** the
x0²+x1²<0 refutation dumps through the F2 seam exactly as the HANDOFF
described (recipe: `Solver.run' (Solver.init; mkVar × 2; mkIneqLiteral
⟨.lt, [(x0²+x1², false)]⟩; mkClause; check (resolve Explain.explain))`,
print `s.refutation`). Read off the dump, the assembly pattern is now
CONCRETE: per bundle, the RUP target is `bundle.lemma`, the F set is
{antecedent clause cids} ∪ {`arithClause core proj` per arith marker};
the walk is a per-cid fold (antecedent cids are always smaller —
creation order), input clauses come from hypotheses, learned from
their bundles, the final bundle's empty lemma closes via
`upRefutes_sound` with target `[]`. Bundle 2 of the dump is the
minimal case (no projection steps — factorSplit ignored per R6): the
arith clause `¬(x0=0) ∨ ¬(x0²+x1²<0)` is nlinarith-grade directly
from the two atoms' `IneqAtom.Holds` unfoldings. Note this example's
arith lemmas are ALL trivially valid (x0²+x1²<0 is unsat by itself),
so the discharge chain (linearRoot/cellBound facts feeding the glue)
is only exercised by the √2-grade acceptance goal — shape:
`x0 ≥ 0 ∧ x0² ≥ 2 ∧ x0 ≤ 1` (the √2 cell bound is load-bearing).
Elaborator pattern per arith marker: (1) compute `arithClause core
proj`; (2) intro all-literals-fail, unfold `litHolds`/`IneqAtom.Holds`
to evalP-level ℝ facts; (3) collect per-step facts from the preceding
projection steps through the Coverage theorems (`rootCmp`-facts are
ℝ-comparisons of `ρ y` with `rootVal` values — sqrt-valued constants
are opaque atoms to linarith, with `quad_roots_order`/`quadRoot_le`
supplying the order facts); (4) close by nlinarith/linarith. Grammar
witnesses for the Coverage theorems are elaborator-built from the
payload data (all conditions decidable-by-construction). Failure at
any point = sound rejection.

**Slice F/G — assembly + acceptance:**
- **F0** reconcile `TraceBundle.isV0` (Trace.lean:203) with R1/R6: it
  currently rejects bundles carrying `resolution`/`factorSplit` steps,
  but the live dump shows every real bundle has both, R1 pulled
  resolution replay into v0, and R6 makes factorSplit always ignorable.
  v0-checkable := in-fragment ∧ no `pseudoDivision`/`intBranch`. The
  "scope tension" docstring note is stale post-R1/R6.
- **F1** F2-seam decode: solver snapshot → semantic clauses/bundles
  (atom table inlined; `ALitHolds` is the literal semantics).
- **F2** per-bundle arith-lemma validity: `proj ++ ¬core` valid by
  linarith/nlinarith over the per-step facts; factorSplit ignored (R6);
  pseudoDivision ignored with sound failure (R7). THE risk item: if
  glue proves insufficient, fall back to per-shape composition lemmas
  (more code, same trust).
- **F3** propositional DAG walk (R1): antecedent cids + arith lemma →
  learned lemma per bundle (tauto-grade); walk from `finalRefutation`
  to the empty clause ⇒ `Γ ⊢ False` over a `Nat → ℝ` valuation.
- **F4** acceptance: √2-grade hand goals (x²−2 square-free, in-fragment
  per F5's mitigation), one factorSplit-bearing trace (x²+2x+1 — the
  knob that may pull the factorSplit discharge forward from 19b,
  accepted risk), negative probes (corrupted trace rejected), 12c/12d
  pins re-green.
- **F5** R8 housekeeping at the boundary: split Check.lean into
  Semantics/Discharge; unify discharge hypotheses on full
  `MPoly.Canon`; normalize `↑0`-form hypotheses to `(0 : ℝ)`
  annotations (R1', approved).

**F5 DONE (2026-08-10, commits f2196d9/045d677/5d0e1e3, build green
7612):** Check.lean → `Check/Semantics.lean` (eval/hom suite, coeffsOf
machinery, atom + root-atom semantics incl. `rootCmp`/`thomFormula`/
`leadSgn`/`rootVal`/`rootCount`, the coeffsOf↔coeffsIn R3 bridge) +
`Check/Discharge.lean` (the four discharges, `thom_iff`,
discPolyOf/pDiffPolyOf reconstructions) with `Check.lean` as a pure
re-export — 96 declarations preserved verbatim, namespaces unchanged.
Canon unification: the four discharges + `evalP_coeffsOf`/
`evalP_linear_form`/`evalP_quadratic_form` take `MPoly.Canon p` (weak
per-term form derived internally); Coverage's `hcan'` weakenings
deleted; CheckTests helpers restated via new `MPoly.canon_two`
(TypesOrder.lean, the `ofInt_canon`/`ofVar_canon` family). R1': the
two `hAq` binders carry `(0 : ℝ)` annotations; all
`exact_mod_cast`-bridges dropped. Trap rediscovered: `by decide`
on `MPoly.Canon p` fails — Canon is a non-reducible def to instance
search even after `unfold`; the Pairwise/∀-mem layers synthesize
individually only via the explicit constructors.

