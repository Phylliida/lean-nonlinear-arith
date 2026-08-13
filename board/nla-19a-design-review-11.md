## nla-19a design review 11 `done` (2026-08-09; Danielle-requested audit of review 10: nothing deferred, no uncovered edge cases)

**Coverage edge found + FIXED: the split fuel was hardcoded 8.** A
clause with a 9+-factor negative sign atom (or many multi-factor
literals) would exhaust fuel and reject — an arbitrary bound, exactly
the kind of rare-case rejection we don't want. Fuel is now sized from
the clause: 2·(factors+1) per literal + margin covers every Or-split
(negChain depth) and every trichotomy split (per extracted diseq).

**Degenerate shapes pinned (all green):**
- empty-factor eq atom, negated in the clause (extracts `1 = 0` from
  the False hypothesis; glue closes);
- all-even lt atom (oddProd = 1; the degenerate sign fact closes);
- empty-factor lt atom UNnegated (an invalid clause — rejects);
- verified by re-read: eq-negative with `fs = []` extracts NOTHING and
  that is COMPLETE (¬Holds is vacuously true — no constraint to give);
  duplicate factors in one atom (the ∀-chain is positional); Or-split
  termination (each split consumes its Or; nested chains decrease);
  the trichotomy Ors never leak into `findOr` (consumed at creation);
  the mangle unfolds `negChain` on concrete lists (empirically, via
  the pins).

**The remaining deferral/skip inventory, honestly:**
- **Root atoms in `extractFacts`** — the ONLY skip class left. Owned
  by G4 (census slice): a SCHEDULED board item with a recipe (Coverage
  theorems + step-fact collection), not a deferral-until-observed.
  Root-atom semantics need the RAlg bridge; that's the slice's content.
- **R-e (new, recorded):** zero-product reasoning inside an Or-split
  BRANCH. The fact indexes are built pre-mangle; post-split branches
  only get the glue (the indexes' fvar types are mangled by then —
  `zeroProductClose` can't re-run reliably). Requires a negative
  multi-factor sign atom AND a separate factorization-depth-≥3 conflict
  in the SAME arith lemma. Fix sketch: unfold negChain at extraction
  time and interleave zeroProductClose into closeWithSplits with
  branch-local re-indexing. Not observed; the mechanism is recorded.
- **G5/G6/G7** — scheduled (19b pseudoDivision identities, 12e integer
  branching, Tier B rootGeneric deg ≥ 3).
- **G8/G9/G10** — measurement/watch items for nla-16 (glue-heuristic
  tail, RUP stall (argued impossible for z3 chains), resource ceiling).

