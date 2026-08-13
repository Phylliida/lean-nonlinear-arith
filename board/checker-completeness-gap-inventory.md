## Checker-completeness gap inventory (2026-08-09, consolidated at Danielle's request)

Every case where the checker soundly rejects but z3 (or our own
solver) succeeds, with owner and effort class. Sources: reviews
5/6/7 + roadmap items.

| # | Gap | Owner | Effort |
|---|-----|-------|--------|
| G1 | ~~Zero-product eq-implication lemmas, total factor degree ≥ 3 (fs3/fs4 pins)~~ **DONE 2026-08-09** — `Refute.zeroProductClose`: native `factorM` + kernel-verified product identity (evalP simp + `ring`) + `mul_ne_zero`/`pow_ne_zero` chain; fs3/fs4 flipped to positive pins; fs3FinalBad soundness probe (invalid clause that passes RUP, rejected at the discharge) | landed in Refute.lean | — |
| G2 | ~~Multi-factor eq atoms skipped by `extractFact`~~ **DONE 2026-08-09** — `extractFacts` multi path: `holds_multi_eq_ne`/`holds_multi_eq_prod` (Check.lean); per-factor diseqs feed `zeroProductClose` (the z3 `add_zero_assumption` shape); composite-wrong-factor negative probe green | landed | — |
| G3 | ~~Even-parity-marked atoms skipped by `extractFact`~~ **DONE 2026-08-09** — same multi path: eq is parity-blind (per-factor/product facts); lt/gt positive gives the `oddProd` sign fact + per-factor ≠0 (`holds_multi_sign_*`/`holds_multi_allNe_*`); lt/gt NEGATIVE (disjunctive) still skipped — sound, rare, noted | landed | — |
| G4 | In-fragment non-literal-local bundles (rootGeneric definite-disc; √2-grade cellBound goal) | census slice (step-fact collection) | MEDIUM — needs the F-i step-fact machinery, census-first |
| G5 | ~~pseudoDivision bundles (isV0 gate; Explain EMITS these — vanishing-lc path)~~ **DONE 2026-08-13 (19b Slices 0–3)** — structural grammar + per-instance ring-identity discharge (d-parity never trusted), sign-transfer family + `pdSign_eq`, rebuilt-literal equivalence transport + drop lane in Refute, isV0 gate lifted (intBranch stays gated → G6); pd1 AND o139 walked end-to-end = M3 | landed in Trace/Walk/Refute/Check | — |
| G6 | intBranch (integer branch-and-bound) | 12e | HARD — solver-side port too (steps never emitted today) |
| G7 | rootGeneric degree > 2 (S1 gate) | Tier B (11a resultants / 11c root continuity) | LONG POLE |
| G8 | Unmapped glue tail (lemmas beyond linarith + one nlinarith round + sq_nonneg hints) | census + nla-16 measurement | open-ended by nature |
| G9 | RUP stall (theoretical; argued impossible for z3 chains) | nla-16 backstop | none — watch item |
| G10 | Resource ceiling (kernel decide / heartbeats on huge refutations) | nla-16 measurement | none — watch item |

**G1 quick-win recipe (verified feasible 2026-08-09):**
`MPolyFactor.factorM : MPoly → MFactors` is PURE (factors carry
multiplicities) and `Check.evalP_mul` exists — in Refute.lean, on glue
failure with a zero-product core shape (`p = 0` fact + `qᵢ ≠ 0` facts):
factor p natively (untrusted), check the factors match the diseq
literals, verify `evalP ρ p = c * ∏ (evalP ρ qᵢ)^kᵢ` via the existing
evalP simp set + `ring_nf` (kernel-checked identity — wrong
factorization = loud failure), build the `mul_ne_zero`/`pow_ne_zero`
chain, contradict `p = 0`. Discharge-side only; no Coverage machinery
needed. G1/G2/G3 are all discharge-side and independent of the
step-fact machinery — pullable forward ahead of the census if desired.

