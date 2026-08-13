- **nla-23** `todo` **q-formula optimality proofs.** The D4/D5 quotient
  candidates and down-prop β formulas are hand-derived Euclidean interval
  reasoning; soundness rides on templates (wrong formula = lost tightness
  only). Prove them RIGHT once and for all in Lean: per formula, an
  attainment lemma (`∃ x y` in the mined box with `x / y = q`) certifies
  the emitted bound is the exact interval optimum — stronger than Z3,
  which never proves its own tightness. Same treatment for corner-fold
  min/max and the k-th-root exactness window.

