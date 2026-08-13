- **nla-03** `done` (descoped by design decision 2026-07-24). The project is
  proof-first: we cover all cases by porting the equivalent of everything Z3
  does and proving containment — coverage never depends on which goal shapes
  are common, and build order follows Z3's own pipeline architecture, so the
  census shape distribution is not an input to anything. Kept as record only:
  `Corpus/Rational.lean` with 3 proven specimens as plain regression tests;
  `data/census-*.txt` as the historical experiment log. Dropped: mass
  transcription, baseline tables, second-crate census, v0 heuristic tactic.
