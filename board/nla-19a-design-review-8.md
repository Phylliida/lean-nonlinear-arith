## nla-19a design review 8 `done` (2026-08-09, post-G1/G2/G3; Danielle-requested gap audit)

Question: did G1/G2/G3 introduce NEW gaps, or just close the corner?

**No regressions possible by construction:**
- `zeroProductClose` is shape-gated and fall-through: any internal
  failure returns `false` and the pre-G1 pipeline runs unchanged. All
  prior pins green.
- `extractFacts`' multi paths only fire on atoms that previously
  returned `none` (skipped). The single-factor-odd path is
  byte-identical.
- ONE theoretical perturbation, no observed instance: the new
  per-factor diseq facts enter the trichotomy-split pool
  (`findDiseq`), changing split order/fuel on glue-failure paths
  (fuel 8, one-at-a-time). A pathological case could burn fuel on the
  new splits first. Watch item, nla-16 territory.

**Found + FIXED during the audit (R-d):** sign-flipped factor
matching — a composite atom carrying `-fᵢ` (e.g. `2-x0`) where
`factorM` has `fᵢ` (`x0-2`) gate-failed the zero-product close.
Fixed: match up to negation, convert the fact via `evalP_neg` +
`neg_ne_zero` (`MPoly.neg` is a plain `List.map` — kernel-reduces, so
the conversion is defeq-clean). Pinned: `gAtomsFlip` test.

**Residual sub-corners (remaining, NOT new — the corner is narrowed,
not perfectly closed):**
- **R-a:** lt/gt NEGATIVE multi-factor literals stay skipped
  (¬Holds is disjunctive there: some factor vanishes ∨ the sign
  flips). Sound; rare; census slice if it ever shows up.
- **R-b:** multi-eq-POSITIVE facts are glue-only — the zero-product
  index can't defeq-match `factorProd fs` against a natively-folded
  product (the `MPoly.mul` kernel-reduction trap). A clause needing
  factorization OF a positive multi-factor eq still rejects. Not
  observed in z3-faithful traces (our input atoms are single-poly;
  explain's composites are negative per `add_zero_assumption`).
- **R-c:** `factorM`'s own completeness (multivariate/sparse
  factorization limits) — z3's `factor()` is also partial; roughly
  comparable; nla-16 measures.

**Soundness:** every new path produces kernel-checked terms; wrong
factorizations fail at the `ring`-verified identity; the Check.lean
additions are plain tactic proofs (no new axioms). Trust surface
unchanged. Gap inventory: G1/G2/G3 done; G4–G7 stand as before.

