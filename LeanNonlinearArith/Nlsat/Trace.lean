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

/-! ## Stage-1 univariate leaves -/

/-- The nla-09 certificate claim shapes (`Certificates/Defs.lean`).
`cs` on the `leafNumeric` step is the ℤ-scaled coefficient list of the
univariate poly (the `evalZ` reflection domain); `a`, `b` are the
rational interval endpoints (`PairQ`, positive denominators checked by
the wrappers). -/
inductive LeafClaim
  | noRoot (a b : PairQ) (c : Cert)
  | uniqueRoot (a b : PairQ) (dc : Cert)
  | posOn (a b : PairQ) (c : Cert)
  | negOn (a b : PairQ) (c : Cert)
deriving Repr

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
  /-- Stage-1 univariate leaf: a numeric certificate claim about the
  ℚ[x] poly whose ℤ-scaled coefficients are `cs`. Discharge (v0):
  `checkNoRoot_sound` / `checkUniqueRoot_sound` / `checkPosOn_sound` /
  `checkNegOn_sound (by decide)` (Certificates/Sound.lean:286/313/376/393). -/
  | leafNumeric (x : Var) (cs : List Int) (claim : LeafClaim)
  /-- Degree-1 root-atom encoding (z3 `mk_linear_root` :861 /
  `mk_plinear_root` :756): `y ⋈_k root(p)` with `p` linear in `y`.
  `mkNeg` = the lc-sign fold (negate the poly when the leading
  coefficient is negative). `lcFact` = the `mk_plinear_root` variant:
  the non-const lc and its `ensure_sign`'d sign (the lc-sign assumption
  is part of the encoding's hypotheses); `none` = the const-lc variant
  (sign decidable). Discharge (v0): plain inequality lemmas incl. the
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
  multi-factor ¬EQ literal's factors). 19b discharge: per-instance
  ring identity + zero-product cases. -/
  | factorSplit (p : MPoly) (fs vanished : Array MPoly)
  /-- Integer branch-and-bound split `x ≤ ⌊v⌋ ∨ x ≥ ⌈v⌉` (12e seam —
  `search_check`; not yet emitted). Discharge: omega-trivial. -/
  | intBranch (x : Var) (v : Rat)
  /-- Boolean resolution glue: one antecedent of the round, in
  processing order. 19b discharge: propositional composition. -/
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

/-- A bundle is v0-checkable iff every step is in-fragment AND in one of
the four v0 shapes (the pseudoDivision/factorSplit/resolution/intBranch
shapes discharge in 19b — the registered v0 scope tension). -/
def isV0 (b : TraceBundle) : Bool :=
  !b.isS1Gated && b.steps.all fun
    | .leafNumeric .. | .thomQuadratic .. | .linearRoot .. | .cellBound .. => true
    | _ => false

end TraceBundle

/-! ## The emission grammar (Q1/F4, DRAFT — finalizes with the checker)

The checker's INPUT CONTRACT, enumerated from
`git show z3-4.12.5:src/nlsat/nlsat_explain.cpp` (the A1–A5 ineq shapes,
B root tiers, C cell literals of the nla-19a board entry, spelled as
step-level well-formedness). Proved direction: grammar → S3-coverage
(Slice E). Explain → grammar is source-fidelity + pins (the search is
untrusted — F4). A step outside the grammar is a parse-level checker
rejection (the sound failure mode). -/

inductive Grammar : TraceStep → Prop
  /-- B-tier linear (:742/:756/:861): the guard is `degreeIn y p = 1`;
  the const-lc variant has `(coeffsIn y)[1]` constant nonzero;
  `lcFact = some (c, s)` requires `c` that lc, non-const, `s ≠ 0`
  (:784 — vanishing lc ⇒ generic fallback). -/
  | linearRoot {k : RootKind} {y : Var} {p : MPoly} {mkNeg : Bool}
      {lcFact : Option (MPoly × Int)} :
      p.degreeIn y = 1 →
      (match lcFact with
       | none => ((p.coeffsIn y)[1]!.asConst?).isSome
       | some (c, s) => c = (p.coeffsIn y)[1]! ∧ c.asConst?.isNone ∧ s ≠ 0) →
      Grammar (.linearRoot k y p mkNeg lcFact)
  /-- B-tier Thom (:787-820): `degreeIn y p = 2`, 1-based `i ∈ {1, 2}`,
  disc sign `sq ≥ 0` (:806 rejects negative), `sa ≠ 0` (the degenerate
  reroutes to `linearRoot` :811-812), signs in {−1, 0, 1}. -/
  | thomQuadratic {k : RootKind} {y : Var} {i : Nat} {p : MPoly}
      {sq sa spd sp : Int} :
      p.degreeIn y = 2 → (i = 1 ∨ i = 2) →
      sq = 0 ∨ sq = 1 →
      (sa = -1 ∨ sa = 1) →
      (spd = -1 ∨ spd = 0 ∨ spd = 1) →
      (sp = -1 ∨ sp = 0 ∨ sp = 1) →
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
  /-- Stage-1 leaves: univariate data — the coefficient list is the
  poly's (no shape constraint on degree; nla-09 is degree-generic). -/
  | leafNumeric {x : Var} {cs : List Int} {claim : LeafClaim} :
      Grammar (.leafNumeric x cs claim)
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

end LeanNonlinearArith.Nlsat
