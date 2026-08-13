- **nla-06** `todo` Linear leaf. **v0 decision: omega IS the leaf** — after
  monomial abstraction (each monomial -> fresh variable) the per-round closure
  check is a linear-ℤ problem, exactly omega's domain; no simplex needed until
  we want *models* to guide generation (Z3-style model-based lemma selection).
  v1 (only if blind saturation proves too slow on real corpora): untrusted
  exact-rational simplex (~300 lines meta) for models + Farkas certificates
  via linear_combination. Base to extend: `Tactic/Oracle.lean` (2026-07-25)
  already parses the atomized constraint system and propagates bounds —
  the simplex adds a feasible point over the same structure. Consumers
  waiting on the model: clause-phase relevance filtering, model-anchored
  D4/D5/M/T tightness, derived product-pair comparisons (O2/O3 residual).
  Documented divergence to close here (2026-07-26): Z3's column bounds
  can come from simplex TABLEAU rows — linear combinations of the
  original constraints — which row-interval propagation over the original
  rows cannot reach; the simplex port restores that strength (and its
  octagon-term bounds then feed `collect_equivs` at full Z3 strength).
