## nla-19a design review 9 `done` (2026-08-09; Danielle-requested: can R-a/R-b/R-c be fixed to full z3 parity?)

- **R-b: FIXED.** `holds_multi_eq_prod` restated to the
  `List.prod`-of-evals form (`((fs.map Prod.fst).map (evalP ρ)).prod`)
  — no `MPoly.mul` in the type, sidestepping the kernel-reduction trap
  entirely (`factorProd`/`evalP_factorProd` DELETED, dead). New trusted
  `listEvalProd_ne_zero` closes multi-eq-positive facts against
  per-factor diseqs — NO factorization needed (the factors are given).
  `zeroProductClose` gained the branch; the flip conversion factored
  out as `diseqFactFor`; the ∀-chain uses `forallMemNe` (the
  forall_mem_cons fold, binder order as probed). Pins: 2-factor +
  **degree-3** (glue-unreachable — the branch necessarily fired).
- **R-a: FIXED conditionally.** New trusted `holds_multi_neg_sign_lt/gt`:
  a negative multi-factor lt/gt literal collapses to the negated
  `oddProd` sign when every factor independently has a diseq fact
  (¬(A ∧ B) with A discharged — the common case; normalize's
  bookkeeping provides the diseqs). Without the side condition the
  shape is genuinely DISJUNCTIVE (some factor vanishes ∨ sign flips)
  and stays skipped — the full fix is Or-fact splitting in the glue
  loop, deferred to the census slice until a live probe needs it.
  Pin: the x0∈(-1,1) collapse test.
- **R-c: documented as a NON-ISSUE for our pipeline (no fix needed).**
  The composite atoms the checker must factor-match are created by OUR
  Explain via the SAME `factorM` — solver and checker cannot diverge
  from each other. Divergence vs z3's factorizer (polynomial.cpp's
  Hensel machinery) is a SEARCH-level parity question (12c/12d + nla-16
  territory), not a checker gap; porting it would be its own arc and
  buys nothing here. Residual: hand-built/foreign traces whose factors
  are non-`factorM`-normalized — out of contract.
- Mangle simp sets gained `List.map_cons/map_nil/prod_cons/prod_nil,
  Prod.fst` (the `List.prod`-form facts); `factorProd` removed.

Gap inventory after review 9: G1/G2/G3 done, R-a (conditional)/R-b
done, R-c documented non-issue. Standing: G4 (census), G5 (19b),
G6 (12e), G7 (Tier B), G8–G10 (nla-16).

