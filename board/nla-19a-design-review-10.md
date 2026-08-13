## nla-19a design review 10 `done` (2026-08-09; R-a FULL — Danielle's standing directive: cover ALL cases, never "defer until it shows up")

**The full unconditional fix for negative multi-factor lt/gt
literals.** Key mathematical subtlety found en route: the per-factor
RECURSIVE expansion is WRONG (the odd-product sign couples all odd
factors — `oddProd ((f,false)::rest) = evalP f * oddProd rest` is not
sign-determined by `oddProd rest`). The correct expansion is FLAT:
`¬ Holds ⟨.lt, fs⟩ ⟺ f₁ = 0 ∨ (f₂ = 0 ∨ … ∨ ¬ oddProd fs < 0)`.

- Check.lean (trusted): `negChain ρ fs tail` (the flat nested-Or fold;
  `g.1` not a pair pattern so the cons equation fires on variables),
  `negChain_tail`, `negChain_mem`, `negHolds_chain_lt/gt` (via
  `by_cases` on all-factors-nonzero: the collapse lemma for the tail
  branch, `push_neg` + `negChain_mem` for the vanishing branch).
- Refute.lean: `extractFacts` returns the negChain fact for negative
  multi lt/gt (nothing ineq-shaped is skipped anymore — only root
  atoms skip); the review-9 conditional collapse pass REMOVED
  (subsumed); `closeWithSplits` gains Or-splitting (`findOr` +
  `g.cases`, before the diseq trichotomy splits); mangle simp set +=
  `negChain`.
- Pins: the review-9 conditional-collapse test still green (now via
  splits); NEW: the no-diseq-facts case (`[⟨4,false⟩, ⟨5,true⟩]` on
  rAtoms) — necessarily through the Or-split path (Or hyps are
  invisible to linarith/nlinarith).
- Trap found: `push_neg` on `¬(a ≠ 0)` already yields `a = 0` (no
  `not_not.mp` needed); tactic simp sets are RUNTIME-elaborated
  (deleting a def doesn't break the build — check by hand).

**extractFacts skip-set after review 10: root atoms only** (G4/census
territory). R-a fully closed; the R-series is done.

