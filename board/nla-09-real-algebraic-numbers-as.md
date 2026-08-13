- **nla-09** `done` (2026-07-26) Real algebraic numbers as (poly, isolating
  interval). **Computational half (2026-07-25)**, `Kernel/Roots.lean`:
  Sturm-bisection isolation (disjoint rational open intervals, non-root
  endpoints by split-nudging, square-free internally), interval
  refinement, Tarski-query sign determination at an isolated root
  (generalized chain `f, f'·g`; single-root TaQ = sign, incl. the 0 case).
  **Trusted bridge (2026-07-26)**, `Certificates/{Defs,Sound}.lean` +
  `Kernel/CertGen.lean`: certificate checkers as Bool programs over
  **unnormalized `Int × Int` fractions** (probe: kernel `decide` cannot
  whnf `Rat.add` — normalization sticks — while gcd-free cross-mult pair
  arithmetic reduces GMP-fast; coefficients ℤ-scaled by the kernel), so a
  claim enters a proof as `check*_sound (by decide)` with an O(1) proof
  term. Certificate language: `lip` (MVT Lipschitz-margin leaf:
  `(absZ p')(max |a| |b|) · (b−a)/2 < |p(mid)|`) + `split` — complete for
  root-free closed intervals by compactness; no monotonicity node needed
  yet. Trusted claims: `checkNoRoot_sound`, `checkUniqueRoot_sound`
  (∃!-root via IVT both orientations + strict mono/anti from
  sign-invariant derivative — nla-02's lemmas doing exactly their planned
  job), `checkPosOn_sound`/`checkNegOn_sound` (cell signs). Generation:
  refine-until-margin bisection; unique-root claims shrink the isolating
  interval until the derivative is root-free on the *closed* interval
  (reachable: square-free ⇒ simple root); `certify*` re-verify through the
  trusted checker before returning (`isSome` ⇒ the `decide` succeeds).
  Tests: kernel-`decide` end-to-end (√2 ∃!, cubic sign cell, generator's
  own x²+1 cert re-checked, ℝ-form massage example = the future tactic's
  emission shape), negative probes, square-free path `(x²−2)²`, √3 from
  `(x²−2)(x²−3)`. Full file elab ~10s incl. all decides.
