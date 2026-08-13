- **nla-08** `done` (2026-07-25) Computational ℚ[x] kernel (untrusted),
  `Kernel/QPoly.lean`: dense ops, exact divRem, monic-Euclid gcd,
  square-free part + Yun, Sturm chains + root counting, Cauchy bound;
  psc/resultant chains computed as determinants of the EXACT Sylvester
  submatrices from `Projection/S1Statement.lean` (spec-faithful — the
  kernel's numbers are definitionally the spec's numbers). **Perf derisk
  cleared decisively**: sturm/wilkinson-40 14ms, deg-16×16 psc chains
  ~70ms, quadratic-lane degrees (≤8) sub-ms — determinant route stands,
  subresultant-PRS fast path only if the deep tail ever demands it.
  Benchmark honesty lesson recorded in `Kernel/QPolyBench.lean`: pure
  computations must be forced (unless-throw) before the closing
  timestamp, else the compiler defers them past it and every phase reads
  0ms.
