## nla-19a design review 13 `done` (2026-08-10; Danielle-requested z3-divergence audit of review 12)

Method: adversarial re-read of the chainLoop/`g.cases` machinery +
z3-source re-read (`mk_ineq_atom` nlsat_solver.cpp:587-620) + two new
pins.

**z3-source findings (no divergences):**
- `mk_ineq_atom` SASSERTs `sz >= 1` — z3 atoms NEVER have empty factor
  lists; our empty-factor handling is a harmless superset.
- `mk_ineq_atom` sign-normalizes every factor (`flip_sign_if_lm_neg`)
  and flips the kind on odd-marked flips — z3-faithful atoms never
  carry lm-negative factors, so R-d's sign-flip matching is
  belt-and-braces for foreign traces (keep it; out-of-contract input
  robustness).
- The even-factor semantics (any zero factor falsifies the atom; even
  factors are sign-absorbed) match `Holds`/`negChain` exactly —
  including that `negChain` lists ALL factors as eq-disjuncts
  regardless of parity (any factor vanishing falsifies the atom).

**Coverage verified (new pins, green):**
- TWO chains in one clause (the chainLoop multi-chain recursion,
  incl. a duplicate-factor chain `x1=0 ∨ (x1=0 ∨ …)`);
- a single-factor EVEN-marked negative lt (length-1 chain with the
  trivially-true tail `¬(1<0)`).

**Verified by re-read:**
- `CasesSubgoal.subst` only re-maps fvars whose types mention the
  split major — our fact indexes never do (the R-e pin uses original
  diseqFacts two cases-levels deep; green ⟹ fvarIds survive).
- Branch-context ⊆ whole-context reasoning: Or facts are invisible to
  linarith/nlinarith, so removing the chain fact and adding one
  disjunct never loses a whole-clause close; the whole-clause ZP fast
  path runs before any splitting.
- chainLoop termination is structural (chs shrinks); `fuel` only
  bounds closeWithSplits' trichotomy/Or-fallback splits, and
  split-produced eq hyps create no new trichotomy needs (they're Eq,
  not Ne).
- The post-mangle `findOr` is now a dead path in practice (all chains
  are consumed pre-mangle) — kept deliberately as a safety net.
- Degenerate: `(_, []) :: rest` chain entries (fs = []) skip splitting
  — the fact IS the bare tail, handled by the terminal glue (dAtoms
  pin 3 covers).

**Honest remaining divergence inventory (all owned, none new):**
root atoms in cores (G4 census slice); pseudoDivision steps (G5/19b);
intBranch (G6/12e); rootGeneric deg ≥ 3 (G7/Tier B); the glue's
heuristic ceiling (G8 — nla-16 measures; full Positivstellensatz
completeness is the certificates' job, not the glue's); resource
ceiling (G10). Within the discharge layer for ineq-atom cores: NO
known rejection class remains.

