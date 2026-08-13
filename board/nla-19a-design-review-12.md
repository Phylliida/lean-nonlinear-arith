## nla-19a design review 12 `done` (2026-08-10; R-e FIXED — zero-product closes inside Or-split branches)

**R-e is fixed.** TDD: the discriminating test went RED first
("glue failed") then green. Two design findings worth recording:

- **Witness engineering**: the chain's factor must be EVEN-marked
  (oddProd excludes it) so no global sign fact involves it — otherwise
  nlinarith closes the branch without factorization via its
  EQ-PAIRINGS: `nlinarithGetProductsProofs` pairs equality hyps with
  everything (`zero_mul_eq`/`mul_zero_eq`) and `removeNe` splits `≠`
  hyps itself. One round of pairwise products only (squares + pairs of
  `new_es ++ ls`, NO products-of-products) — so degree-3 factorization
  conflicts with the sign facts in a different variable DO escape it.
  Pin: `p = (x0-1)(x0-2)(x0-3)` even-marked in a 2-factor lt atom with
  `x1`; the `p = 0` branch needs factorM + the composite-eq diseqs.
- **Implementation**: `FactKind.negChain`; `extractFacts` classifies;
  `chainLoop` splits chains PRE-mangle via `g.cases` (whnf's the
  `negChain` def to the nested Or); the left-branch field fvar
  (`CasesSubgoal.fields` — inherited from `InductionSubgoal`; there is
  no `fieldHyps` in 4.25) extends the eq index; terminal branches run
  `zeroProductClose` with the extended index, then mangle+glue+splits.

**Trap (bit hard, 15 tests red): the evalTactic mangle (simp/ring_nf)
ASSIGNS the goal mvar** — after `mangle` you must pass `getMainGoal`
(the fresh post-mangle mvar), not the pre-mangle one. Symptom:
"metavariable has already been assigned" deep in closeWithSplits.

**The R-series is now COMPLETE** (R-a..R-e all fixed); the
discharge layer covers every ineq-atom shape unconditionally, with
zero-product reasoning available in every Or-split branch.

