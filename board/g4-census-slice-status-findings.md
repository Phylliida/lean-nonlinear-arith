## G4 census slice — status + findings (2026-08-10, iteration 1)

**Empirical column (live dumps, all walked end-to-end):**

| driver | goal | shapes in arith clauses | locality |
|---|---|---|---|
| sq | x0²+x1²<0 | factorSplit, linearRoot, cellBound, leafNumeric | literal-local ✓ |
| drv | x0²+x1²≥2 ∧ bounds | factorSplit, linearRoot, thomQuadratic, cellBound | literal-local ✓ |
| fs1/fs2 | factor-degree-2 zero products | (stage-0; factorization internal) | literal-local ✓ |
| fs3/fs4 | factor-degree-3 | (G1 zero-product close) | literal-local ✓ |
| sqrt2 | x0≥0 ∧ x0²≥2 ∧ x0≤1 √2-grade | leafNumeric only (stage-0) | literal-local ✓ pinned |
| def1/def2 | x0²+1<0, x0²+x0+1<0 | leafNumeric only | literal-local ✓ |
| rg | x0²+x1<0 ∧ x1>1 | (stage-0 signs) | literal-local ✓ |

Every live arith clause is literal-local — review-5's F-i holds
empirically everywhere we can drive the solver. **No driver ever emits
`rootGeneric`.** Source-derived reason (nlsat_explain.cpp@4.12.5, read
:z3-4.12.5): `add_root_literal` is only called from `add_cell_lits`,
whose roots come from `isolate_roots` at the sample. A deg-≤2 poly
with an isolated real root always has `disc ≥ 0` at the sample, so
`mk_quadratic_root` never fails for it (`sq < 0` impossible, `i ≤ 2`
always by bracketing). Negative-disc quads have NO roots and never
reference one. ⇒ **rootGeneric at deg ≤ 2 is unreachable via 4.12.5
production; the grammar region is foreign-trace defense.** Synthetic
bundles (fs3FinalBad discipline) are its pinning vehicle.

**√2-grade acceptance:** `goSqrt2` refutes STAGE-0 with core = the
three input atoms, arith clause pure-projection — pinned positive in
WalkTests (machine-generated snapshot; the solver never constructed
cells for it — recorded fact, the "load-bearing cellBound" framing
predates the live dump).

**The two members whose contradiction is NOT literal-local (design
column, locality census unchanged):**
- **rootGeneric-definite-disc** (foreign traces): arith clause with
  `¬atom⟨k,y,i,p⟩` and disc<0. Locality fix = F2-side: extend
  `extractFacts` to root atoms — `rootGeneric_discharge` gives
  `1 ≤ i ≤ rootCount ∧ rootCmp`; plus `rootCount_zero_of_neg_disc`
  (the glue's disc-sign fact) ⇒ `i ≤ 0`, contradiction. ALL literal-
  local once root atoms extract — no step-fact machinery needed for
  THIS member (the R-a lesson: atom semantics is the extraction site).
- **rootCmp cross-links** (the payload-consuming member, review-6
  F-w territory): contradiction needs `rootVal`-vs-`ρ y` orderings
  CONNECTED to ineq-atom signs — the encoding literal may be absent
  from the clause. Here step-fact collection is genuinely required:
  per `.arith` marker, read the preceding encoding steps and generate
  `rootCmp k (ρ y) (rootVal …)` / sign facts via the Coverage
  theorems (linearRoot_hAq, rootVal_eq_*, thom_discharge — the R-ii
  by-value reconstruction of `discPolyOf`/`pDiffPolyOf` matched
  against clause literal failures).

**Implementation order (this slice):**
1. `grammarOK : TraceStep → Bool` (decidable mirror of
   `TraceStep.Grammar` + `grammarOK_sound : grammarOK s → Grammar s`)
   — review-6's optional lint, now REQUIRED: step-fact collection
   needs grammar evidence from payload data (decide-grade).
   **DONE 2026-08-10** (Trace.lean; ⊥→Prop soundness via
   `of_decide_eq_true` naming conventions — LEARN: `decide_eq_true`
   is the FORWARD direction; Bool-chain proofs choke on
   `cases`/`obtain` deep-pattern dependent elimination — convert
   componentwise, never rw `decide_eq_true_eq` over multi-occurrence
   `decide ?p` shapes).
2. `extractFacts` root-atom branch (the definite-disc member + its
   synthetic pin in RefuteTests).
3. Step-fact collection from bundle context (the cross-links member +
   synthetic pins — synthetic because no live driver emits it).
   **DONE** (review 15 below).
4. F-w: mkNeg/sp payload-corruption probes (negative probes on the
   synthetic fixtures). **DONE** (review 15 below).
5. Pin + BOARD review. **DONE** — the review-15 entry below is the
   close-out; the census slice (G4) is COMPLETE.

