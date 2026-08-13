- **nla-24** `active` **Kernel/oracle correctness lemmas** (2026-07-26).
  Proving the untrusted computations right where it is cheap, per
  Danielle's review directives. Done: the oracle tighten formulas are
  fully characterized (`cdivPos_le_iff` / `le_fdiv_iff_mul_le` in
  Oracle.lean — iff = soundness + tightness; the ub step recomputed in
  positive-divisor form to match the lemma verbatim); `nonRootSplit`'s
  try count made provably sufficient (counting argument in the
  docstring). Remaining candidates, roughly by value: `propagate`'s
  sup-accumulation loop (the residual trust in the oracle),
  `QPoly.psc = S1Statement.psc` bridge (the kernel's numbers ARE the
  spec's numbers — currently by construction-mirroring, provable as a
  determinant identity), Yun reconstruction (`∏ aᵢ^i = monic p` — pinned
  by #guard on specimens today), Sturm correctness (= S2/nla-10
  territory, don't duplicate).
