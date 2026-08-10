import LeanNonlinearArith.Nlsat.Types
import LeanNonlinearArith.Certificates.Defs

/-!
# nla-12d.6b ⇄ nla-19a — the trace language (search → checker contract)

The shared datatype the search emits and the trusted checker consumes
(DESIGN-nlsat-quadratic §2; module map row "Nlsat/Trace.lean — shared
datatype"). Emission is nla-12d.6b (untrusted, inside `Nlsat/Explain.lean`
+ `Nlsat/Solver.lean`); consumption is nla-19a's `Nlsat/Check.lean`
(trusted). Standing rule 3: payloads pin only when the checker consumes
them — the pseudoDivision/factorSplit/resolution/intBranch payloads here
are emission-side best effort (they OCCUR under the nra defaults, F5 of
the 2026-08-03 design review), and 19b finalizes their consumption.

**The 8 conceptual shapes** (DESIGN-nlsat-quadratic §2), with the B-tier
generic root-atom fallback spelled out as its own constructor
(`rootGeneric` — the grammar's "generic mk_root_atom fallback :732";
the fragment gate is syntactic on it, F3 checker-computed):

```
leafNumeric | thomQuadratic | linearRoot | cellBound |
pseudoDivision | factorSplit | intBranch | resolution   (+ rootGeneric)
```

**Payload principles:**
- every payload is decidable DATA (polys, signs, indices, certificates) —
  never propositions, never "trust me" markers;
- the emitted clause literals are RECONSTRUCTIBLE from the payloads +
  constness (the reconstruction is exactly what the emission grammar
  below formalizes — F4), so steps carry no duplicate literal copies;
- root indices are 1-based, matching z3 (`nlsat_explain.cpp` passim);
- sign payloads are the values `ensure_sign`/`sign` computed at the
  sample (−1/0/+1) — they determine the emitted literal polarities.

**Two-step emission for cell bounds:** `add_cell_lits` calls
`add_root_literal`, which runs the encoding chain
(mk_linear_root → mk_quadratic_root → generic). The trace mirrors that:
each such call emits an ENCODING step (`linearRoot`/`thomQuadratic`/
`rootGeneric` — the equivalence obligation: the sign literals correctly
encode the root atom) followed by a `cellBound` step (the ordering
obligation: the sample's value of `y` bears the stated relation to
`root_i(p)`, i.e. the emitted bound describes the cell containing the
sample; discharge = the S3 ordering family).

**Polarity (load-bearing, `Explain.lean` header):** explain's output is
a theory-lemma clause, so assumptions appear NEGATED; root literals are
always emitted negated EXCEPT the `mk_linear_root` encodings, which fold
the negation into the kind/lsign remap (`RootKind.toIneqSign`,
nlsat_explain.cpp:866-874).
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel LeanNonlinearArith.Certificates

/-! ## Stage-1 univariate leaves

The nla-09 certificate machinery (`Certificates/Defs.lean` —
`checkNoRoot`/`checkUniqueRoot`/`checkPosOn`/`checkNegOn` over
ℤ-scaled coefficient lists with rational interval endpoints) is the
discharge kit for stage-1 leaves. The step itself is a MARKER (F3:
the checker recomputes the univariate-leaf property from the arith
lemma's polys, and generates certificates at check time via the nla-09
`CertGen` bisection — nothing search-asserted is trusted). -/

/-! ## Cell bounds -/

/-- Which bracketing case `add_cell_lits` (nlsat_explain.cpp:899) hit:
`exact` = the sample IS `root_i(p)` (the ROOT_EQ early return :936-937,
immediate return skipping the upper bound); `lower`/`upper` = the
tightest root bounds (:965/:968; kind is `gt`/`lt`, or `ge`/`le` under
`full_dimensional`). -/
inductive CellSide | exact | lower | upper
deriving Repr, DecidableEq

/-! ## Resolution antecedents (the `resolution` shape; 19b discharges) -/

/-- One antecedent processed by `resolve`'s trail scan
(nlsat_solver.cpp:1756-1812 region @ 4.12.5), in processing order:
an existing clause (`justification.clause`), a lazy arith justification
(`resolve_lazy_justification` :1813 — the arith lemma is `proj ++ ¬core`,
justified by the projection steps immediately preceding this marker in
the bundle), or a decision literal (stays in the learned lemma). -/
inductive ResolutionAntecedent
  | clause (cid : Nat)
  | arith (core proj : Array Literal)
  | decision (l : Literal)
deriving Repr

/-! ## The trace step language -/

inductive TraceStep
  /-- Stage-1 univariate leaf (marker, F3): the arith lemma this step
  precedes (the `resolution (.arith …)` marker in the same bundle) is a
  univariate-in-`x` (constant-coefficient) conflict — its disjunction
  is valid over ℝ. The checker recomputes the property from the
  lemma's polys and discharges by the nla-09 sweep (v0: direct
  trichotomy/`nlinarith` glue; higher-degree: `CertGen` certificates +
  `check*_sound (by decide)`). -/
  | leafNumeric (x : Var)
  /-- Degree-1 root-atom encoding (z3 `mk_linear_root` :861 /
  `mk_plinear_root` :756): `y ⋈_k root(p)` with `p` linear in `y`.
  `mkNeg` = the lc-sign fold (negate the poly when the leading
  coefficient is negative). `lcFact` = the `mk_plinear_root` variant:
  the lc and its `ensure_sign`'d sign (when the lc is non-const the
  lc-sign assumption is part of the encoding's hypotheses; a CONST lc
  is reachable via the quadratic degenerate :811-812 and needs none —
  its sign is decidable). `none` = the const-lc variant (sign
  decidable). Discharge (v0): plain inequality lemmas incl. the
  LE/GE kind remap + negation fold (:869-878). -/
  | linearRoot (k : RootKind) (y : Var) (p : MPoly) (mkNeg : Bool)
      (lcFact : Option (MPoly × Int))
  /-- Quadratic Thom encoding (z3 `mk_quadratic_root` :787):
  `y ⋈_k root_i(p)`, `p = A·y² + B·y + C`, witnessed purely by sign
  literals on {disc = B²−4AC, A, p′ = 2Ay+B, p}. Sign payloads are the
  sample signs (`sq` disc, `sa` A, `spd` p′, `sp` p itself — emitted
  only when `sq > 0`, :814-817). Pre: `sa ≠ 0` (the `sa = 0` degenerate
  falls back to `mk_plinear_root` on `B·y + C` :811-812 — traced as a
  `linearRoot` step with `lcFact`). Discharge (v0): the S3 kit
  (`Templates/Quadratic.lean`). -/
  | thomQuadratic (k : RootKind) (y : Var) (i : Nat) (p : MPoly)
      (sq sa spd sp : Int)
  /-- The generic root-atom fallback (z3 `add_root_literal` :731-733):
  no encoding applied; the NEGATED root atom enters the clause
  verbatim. Reachable at deg ≤ 2 too (deg-1 with vanishing lc sign;
  deg-2 with negative sample discriminant) — so this constructor is NOT
  per se out of fragment: the gate is `p.degreeIn y ≤ 2`, computed by
  the checker (F3). -/
  | rootGeneric (k : RootKind) (y : Var) (i : Nat) (p : MPoly)
  /-- Cell bracketing around the sample (z3 `add_cell_lits` :899),
  emitted right after the encoding step of the same `add_root_literal`
  call. `k` is the kind passed to `add_root_literal` (`.eq` for
  `exact`; `gt`/`ge` for `lower`; `lt`/`le` for `upper`).
  Discharge (v0): the S3 point-vs-root ordering family +
  `quad_roots_order`. -/
  | cellBound (side : CellSide) (k : RootKind) (y : Var) (i : Nat) (p : MPoly)
  /-- Pseudo-division sign transfer in `simplify` (z3 :1096-1341):
  `lc(eq)^d · f = q·eq + r` with the sign-flip rule :1132-1137
  (`d` odd ∧ factor odd ∧ `lcSign < 0`). 19b discharge: per-instance
  ring identity + parity cases. -/
  | pseudoDivision (f eq : MPoly) (x : Var) (d : Nat) (r : MPoly)
      (lcSign : Int) (isEven : Bool)
  /-- Factor split (z3 `add_zero_assumption` :262 / `add_factors` :578
  with `factor=true`): `p` factors as the distinct `fs`;
  `vanished` = the factors with sign 0 at the sample (the emitted
  multi-factor ¬EQ literal's factors). v0 IGNORES the step (R6: the
  factored poly never appears in any clause literal — only its factors
  do — so ignoring is sound AND loses zero z3-coverage). The
  per-instance ring identity + zero-product cases remain available for
  19b-grade completeness insurance. -/
  | factorSplit (p : MPoly) (fs vanished : Array MPoly)
  /-- Integer branch-and-bound split `x ≤ ⌊v⌋ ∨ x ≥ ⌈v⌉` (12e seam —
  `search_check`; not yet emitted). Discharge: omega-trivial. -/
  | intBranch (x : Var) (v : Rat)
  /-- Boolean resolution glue: one antecedent of the round, in
  processing order. v0 discharge (R1 — came forward from 19b):
  propositional composition (tauto-grade DAG walk from
  `finalRefutation` to the empty clause), NOT a z3 trail-scan. -/
  | resolution (ant : ResolutionAntecedent)
deriving Repr

namespace TraceStep

/-! ### The fragment gate (F3: checker-computed, decidable)

z3's projection is degree-generic; the CHECKABLE fragment is: every
projection/root step stays at degree ≤ 2 in its top variable
(DESIGN-nlsat-quadratic §0). `leafNumeric` certificates are
degree-generic (nla-09), `pseudoDivision`/`factorSplit`/`resolution`/
`intBranch` are degree-neutral (ring identities / glue), so the gate
bites exactly at `rootGeneric` with `degreeIn y p > 2`. Any other shape
with an off-grammar degree is rejected by the GRAMMAR (below), not the
gate. -/

/-- Steps whose obligation is projection-degree-sensitive. -/
def inFragment : TraceStep → Bool
  | rootGeneric _ y _ p => p.degreeIn y ≤ 2
  | _ => true

/-- The S1-gate mark (advisory, search-side; the checker recomputes —
F3). A bundle is S1-gated iff some step fails `inFragment`. -/
def isS1Gated (s : TraceStep) : Bool := !s.inFragment

end TraceStep

/-! ## Bundles: the refutation-DAG node (F1)

One bundle per learned clause (flushed from `Solver.pendingTrace` at
the `mkClause` sites in `resolve`, Solver.lean:1002/:1019) plus the
designated `finalRefutation` bundle at the empty-lemma UNSAT exit
(Solver.lean:993). `lemma` is the learned clause the bundle derives
(solver-level literals; semantic decoding happens at the F2 extraction
seam). `steps` interleave projection steps (justify the arith lemmas)
and `resolution` markers (the antecedent skeleton) in emission order. -/

structure TraceBundle where
  steps : Array TraceStep := #[]
  lemma : Array Literal := #[]
deriving Repr, Inhabited

namespace TraceBundle

/-- A bundle is S1-gated (advisory mark) iff some step is. -/
def isS1Gated (b : TraceBundle) : Bool := b.steps.any TraceStep.isS1Gated

/-- A bundle is v0-checkable iff every step is in-fragment AND no step
is `pseudoDivision` or `intBranch` (19b/12e shapes — a pseudoDivision
rewrite can be load-bearing, R7, so its presence means sound
rejection). `resolution` markers are v0 (R1 — the propositional replay
came forward) and `factorSplit` steps are always safe to ignore (R6 —
the factored poly never appears in any clause literal, so ignoring
loses zero z3-coverage). Every real bundle carries both (the live
x²+y²<0 dump), so the four-shapes-only reading of v0 rejected
everything — reconciled 2026-08-06 (F0). -/
def isV0 (b : TraceBundle) : Bool :=
  !b.isS1Gated && b.steps.all fun
    | .pseudoDivision .. | .intBranch .. => false
    | _ => true

end TraceBundle

/-! ## The emission grammar (Q1/F4 — FINALIZED 2026-08-06)

The checker's INPUT CONTRACT, enumerated from
`git show z3-4.12.5:src/nlsat/nlsat_explain.cpp` (the A1–A5 ineq shapes,
B root tiers, C cell literals of the nla-19a board entry, spelled as
step-level well-formedness), audited line-by-line in E1 (the const-
lcFact gap fix, the `sp` placeholder and `mkNeg`-fold pinings — see
the BOARD 19a entry). Coverage (E2): `Nlsat/Coverage.lean` proves per
constructor that the grammar conditions + the bundle-context facts
suffice for the Check.lean discharge kit. Proved direction: grammar →
S3-coverage. Explain → grammar is source-fidelity + pins (the search
is untrusted — F4). A step outside the grammar is a parse-level
checker rejection (the sound failure mode). -/

inductive Grammar : TraceStep → Prop
  /-- B-tier linear (:742/:756/:861): the guard is `degreeIn y p = 1`;
  the const-lc variant has `(coeffsIn y)[1]` constant NONZERO (:745
  SASSERT; the port rejects `c == 0` defensively) with `mkNeg` the
  const's negativity (:746); `lcFact = some (c, s)` requires `c` that
  lc, `s ≠ 0` (:763-765 — vanishing lc ⇒ generic fallback), and
  `mkNeg = decide (s < 0)` (:767). The plinear path is reachable ONLY
  via the quadratic degenerate (:811-812 — `add_root_literal`'s chain
  :730-731 does not try it), where the lc is the parent quadratic's `B`
  and CAN be a nonzero constant; then `s = Int.sign c` and
  `ensure_sign` adds no literal (:845 `is_const` skip). E1 audit
  2026-08-06: the original `c.asConst?.isNone` condition rejected those
  legitimate emissions; the `mkNeg` folds were pinned with the E2
  design (they make the lc-sign evidence derivable by `decide` in the
  const cases). -/
  | linearRoot {k : RootKind} {y : Var} {p : MPoly} {mkNeg : Bool}
      {lcFact : Option (MPoly × Int)} :
      p.degreeIn y = 1 →
      (match lcFact with
       | none => ∃ v, ((p.coeffsIn y)[1]!).asConst? = some v ∧ v ≠ 0 ∧
           mkNeg = decide (v < 0)
       | some (c, s) => c = (p.coeffsIn y)[1]! ∧ s ≠ 0 ∧
           mkNeg = decide (s < 0) ∧
           ∀ v, c.asConst? = some v → s = Int.sign v) →
      Grammar (.linearRoot k y p mkNeg lcFact)
  /-- B-tier Thom (:787-820): `degreeIn y p = 2`, 1-based `i ∈ {1, 2}`,
  disc sign `sq ≥ 0` (:806 rejects negative), `sa ≠ 0` (the degenerate
  reroutes to `linearRoot` :811-812), signs in {−1, 0, 1}. `sp` is only
  computed when `sq > 0` (:815-817); emission writes the placeholder
  `sp = 0` when `sq = 0`, and the contract requires exactly that (E1
  audit 2026-08-06 — tightens corruption detection, F4). -/
  | thomQuadratic {k : RootKind} {y : Var} {i : Nat} {p : MPoly}
      {sq sa spd sp : Int} :
      p.degreeIn y = 2 → (i = 1 ∨ i = 2) →
      sq = 0 ∨ sq = 1 →
      (sa = -1 ∨ sa = 1) →
      (spd = -1 ∨ spd = 0 ∨ spd = 1) →
      (sp = -1 ∨ sp = 0 ∨ sp = 1) →
      (sq = 0 → sp = 0) →
      Grammar (.thomQuadratic k y i p sq sa spd sp)
  /-- B-tier generic (:731-733): no shape constraint beyond data —
  fragment membership is the `inFragment` gate, not the grammar. -/
  | rootGeneric {k : RootKind} {y : Var} {i : Nat} {p : MPoly} :
      1 ≤ i →
      Grammar (.rootGeneric k y i p)
  /-- C-tier cell literals (:899-968): kind/side agreement (exact ⇔
  ROOT_EQ; lower ⇔ GT/GE; upper ⇔ LT/LE), 1-based index, and the bound
  poly is non-const in `y` (it contributed a root). -/
  | cellBound {side : CellSide} {k : RootKind} {y : Var} {i : Nat} {p : MPoly} :
      (match side with
       | .exact => k = .eq
       | .lower => k = .gt ∨ k = .ge
       | .upper => k = .lt ∨ k = .le) →
      1 ≤ i → 1 ≤ p.degreeIn y →
      Grammar (.cellBound side k y i p)
  /-- Stage-1 leaves: the marker carries no shape constraint (the
  univariate-leaf property is checker-recomputed from the arith
  lemma's polys — F3; nla-09 is degree-generic). -/
  | leafNumeric {x : Var} :
      Grammar (.leafNumeric x)
  /-- 19b shapes: emission-side grammar only (consumption pins in 19b). -/
  | pseudoDivision {f eq : MPoly} {x : Var} {d : Nat} {r : MPoly}
      {lcSign : Int} {isEven : Bool} :
      Grammar (.pseudoDivision f eq x d r lcSign isEven)
  | factorSplit {p : MPoly} {fs vanished : Array MPoly} :
      Grammar (.factorSplit p fs vanished)
  | intBranch {x : Var} {v : Rat} :
      Grammar (.intBranch x v)
  | resolution {ant : ResolutionAntecedent} :
      Grammar (.resolution ant)

/-! ### The decidable mirror `grammarOK` + soundness

G4 census slice (review-6's optional `grammarOK` lint, consumed here):
the walk re-discharges arith lemmas from clause literals alone, so
payloads are PARTICIPANT-GRADE never trust-grade — but the step-fact
collection (rootCmp cross-links idle-F2 side) REQUIRES grammar
evidence from payload data, which must be decide-grade on concrete
steps. `grammarOK` mirrors each `Grammar` constructor; every emission
side feeds only `decide`-able payloads, so the checker enforces the
input contract against real traces too (sound rejection on mismatch). -/

/-- Decidable mirror of `TraceStep.Grammar`. -/
def grammarOK : TraceStep → Bool
  | .linearRoot _k y p mkNeg lcFact =>
    decide (p.degreeIn y = 1) &&
    match lcFact with
    | none =>
      match ((p.coeffsIn y)[1]!).asConst? with
      | some v => decide (v ≠ 0) && mkNeg == decide (v < 0)
      | none => false
    | some (c, s) =>
      decide (c = (p.coeffsIn y)[1]!) && s != 0 && mkNeg == decide (s < 0) &&
        (match c.asConst? with
         | none => true
         | some v => decide (s = Int.sign v))
  | .thomQuadratic _k y i p sq sa spd sp =>
    decide (p.degreeIn y = 2 ∧ (i = 1 ∨ i = 2) ∧
      (sq = 0 ∨ sq = 1) ∧ (sa = -1 ∨ sa = 1) ∧
      (spd = -1 ∨ spd = 0 ∨ spd = 1) ∧ (sp = -1 ∨ sp = 0 ∨ sp = 1) ∧
      (sq = 0 → sp = 0))
  | .rootGeneric _k _y i _p => decide (1 ≤ i)
  | .cellBound side k y i p =>
    (match side with
     | .exact => decide (k = .eq)
     | .lower => decide (k = .gt ∨ k = .ge)
     | .upper => decide (k = .lt ∨ k = .le)) &&
      decide (1 ≤ i) && decide (1 ≤ p.degreeIn y)
  | .leafNumeric _ | .pseudoDivision .. | .factorSplit ..
  | .intBranch .. | .resolution _ => true

/-- Soundness: decide-grade grammar membership implies the Prop grammar. -/
theorem grammarOK_sound (s : TraceStep) (h : grammarOK s) : Grammar s := by
  cases s with
  | leafNumeric x => exact Grammar.leafNumeric
  | linearRoot k y p mkNeg lcFact =>
    unfold grammarOK at h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hdeg, hcond⟩ := h
    apply Grammar.linearRoot hdeg
    cases lcFact with
    | none =>
      cases hcc : ((p.coeffsIn y)[1]!).asConst? with
      | none =>
        simp only [hcc] at hcond
        exact Bool.noConfusion hcond
      | some v =>
        simp only [hcc] at hcond
        rw [Bool.and_eq_true] at hcond
        obtain ⟨hvne, hmk⟩ := hcond
        rw [decide_eq_true_eq] at hvne
        exact ⟨v, rfl, hvne, beq_iff_eq.mp hmk⟩
    | some cs =>
      obtain ⟨c, s'⟩ := cs
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcond
      obtain ⟨⟨⟨hc, hss⟩, hmk⟩, hconst⟩ := hcond
      refine ⟨of_decide_eq_true hc, bne_iff_ne.mp hss, beq_iff_eq.mp hmk, ?_⟩
      intro v hv
      cases hdc : c.asConst? with
      | none =>
        simp only [hdc] at hv
        exact Option.noConfusion hv
      | some v' =>
        simp only [hdc] at hv hconst
        have heq : v' = v := Option.some.inj hv
        subst heq
        exact of_decide_eq_true hconst
  | thomQuadratic k y i p sq sa spd sp =>
    unfold grammarOK at h
    have h' := of_decide_eq_true h
    exact Grammar.thomQuadratic h'.1 h'.2.1 h'.2.2.1 h'.2.2.2.1
      h'.2.2.2.2.1 h'.2.2.2.2.2.1 h'.2.2.2.2.2.2
  | rootGeneric k y i p =>
    unfold grammarOK at h
    exact Grammar.rootGeneric (of_decide_eq_true h)
  | cellBound side k y i p =>
    unfold grammarOK at h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hside, hi⟩, hdeg⟩ := h
    cases side with
    | exact =>
      exact Grammar.cellBound (of_decide_eq_true hside)
        (of_decide_eq_true hi) (of_decide_eq_true hdeg)
    | lower =>
      exact Grammar.cellBound (of_decide_eq_true hside)
        (of_decide_eq_true hi) (of_decide_eq_true hdeg)
    | upper =>
      exact Grammar.cellBound (of_decide_eq_true hside)
        (of_decide_eq_true hi) (of_decide_eq_true hdeg)
  | pseudoDivision feq eqe xe de re lcSign isEven => exact Grammar.pseudoDivision
  | factorSplit pe fse vanished => exact Grammar.factorSplit
  | intBranch xe ve => exact Grammar.intBranch
  | resolution ant => exact Grammar.resolution

end LeanNonlinearArith.Nlsat
