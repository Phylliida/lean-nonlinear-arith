- **nla-07b** `todo` **Gröbner→saturation propagation.** Z3's
  `propagate_eqs`/`propagate_fixed`/`propagate_linear_equations` feed
  Gröbner-DERIVED equalities back into the LRA solver, where they become
  anchors/pins for the order/tangent/interval machinery on inequality
  goals — a composition the goal-directed grind reuse cannot replicate
  (grind exposes no basis API; probe: it derives `e*a - c*d = 0` in its
  basis yet fails the ≤ goal). Port: small meta-Buchberger over ℚ[atoms]
  with cofactor tracking (untrusted, oracle-style), noting derived
  equalities whose monomials all live in the collected atom vocabulary,
  each certified by `linear_combination` with delaborated cofactors (or
  discharged by a grind call on the equality subgoal). Pairs naturally
  with the nla-06 simplex work.

