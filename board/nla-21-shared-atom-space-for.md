- **nla-21** `todo` **Shared atom space for noted facts.** The right fix for
  the orientation-bug class (review fix e104567 covers only `mul_comm` of
  the div defining equation): meta-built composites in noted conclusions
  can land on different omega atoms than ring_nf's canonization of the same
  user-written term (instance spellings remain even after the orientation
  fix). Design constraints mapped during review: (a) `ring_nf at *` after
  noting invalidates positive discharge-cache entries — their proof terms
  reference hypothesis fvars that ring_nf replaces; (b) per-fact
  `ring_nf at h` inside `noteFact` is safe for the cache (user fvars
  untouched) and dedup keys (computed pre-normalization from the built
  conclusion), but then the appended `ms` product spelling must ALSO be the
  canonical form or `mineBounds`' syntactic lookups miss — needs a meta
  entry point to ring_nf-normalize an `Expr` (investigate
  `Mathlib.Tactic.RingNF` internals) applied consistently to noted facts
  AND collected/appended atom spellings; (c) the clause phase instantiates
  from pre-canonical `ms` exprs and must go through the same normalization.
  Scope: noting path + collection + clause phase, one design.
