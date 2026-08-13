## nla-27 `done` (2026-07-28) — univariate ℤ factorization (default-Z3 parity; Danielle, 2026-07-26 review)

Complete in 4 slices (commits e7b4e41..9a0c69a), full build 7580 jobs
green, 120+ pins. What landed:

1. **`Kernel/Zp.lean` + `Kernel/ZPoly.lean`** — modular context and
   ℤ[x] layer. Fidelity catches: (a) z3's zp is **balanced**
   `(−m/2, m/2]` (`mpzzp_manager::p_normalize_core`), not `[0, m)` —
   load-bearing for `exact_div` and the CRA first image; (b) z3's ℤ gcd
   is `mod_gcd` (231-big-prime table from `polynomial_primes.h`,
   `CRA_combine_images` with balanced reps, primitive-candidate trial
   division, Euclid fallback), not subresultant. **Mathlib reverted
   out of the kernel** after its `!![` matrix-literal token glued
   `![` and broke `x[i]![j]!` chains downstream (AnumEval parse
   error) — local `bezoutCoeffs`/`isqrt` instead; kernel stays
   mathlib-free (per-file elab ~2-4s vs ~15-20s as a bonus).
2. **`Kernel/Factor.lean` GF(p) half** — `zpSquareFreeFactor` (Yun in
   char p with the Frobenius p-th-root step), `berlekamp_matrix` port
   (Q−I recurrence, column-op diagonalize, null-space enumeration),
   `zpFactorSquareFreeBerlekamp` (randomized=false — the deterministic
   path `zp_factor_square_free` actually selects), `zpFactor`.
3. **`Kernel/Factor.lean` ℤ half** — `henselLiftStep`/
   `henselLiftQuadratic`/multi-factor `henselLift` (last factor carries
   `lc⁻¹`), `mignotteBound`, `DegreeSet` (Nat bitset), `CombIter`
   (the `ufactorization_combination_iterator` state machine, faithful:
   removal, size growth, degree-set filter, left/right/tail products),
   `factorSquareFree` (prime trials 2..31, GF(p)-irreducible ⇒ done,
   degree-set-trivial ⇒ done, best-of-trials, Hensel, tail-coeff
   pre-checks, `exact_div` trials, budget ⇒ `false`), `factor2SqfPp`
   discriminant shortcut, `factorCore` (Yun over ℤ via `mod_gcd`),
   `factor`. Pins incl. x⁴−10x²+1 surviving the lifted search and
   x⁶−1 → 4 cyclotomic factors.
4. **RAlg wiring** — `RAlg.root` gains `minimal` (z3 `m_minimal`,
   defaulted ctor arg so bare constructions mean `false`);
   `isolateRoots` = `am::isolate_roots` (zero-strip → factor → linear
   basic → per-factor isolation with `minimal = full_fact` →
   `sort_roots`); `compareCore` **minimal-polynomial
   refine-until-disjoint branch** between `compare_p` and magnitude
   equalization (the COMMON path in default z3); `isRational`
   short-circuits on minimal cells (`m_not_rational` semantics);
   became-basic paths are safety nets, matching default-z3
   radical-only + the F1 guard. `factor=false` leaves the
   approved-divergence register.

Original item text (all consequences landed): port
`upolynomial_factorization.cpp` (~1300 lines): square-free
factorization, Berlekamp over `Z_p` (prime trials per
`factor_max_prime`/`factor_num_primes`), lifting + recombination
(`factor_search_size`). Wire into `RAlg.isolateRoots` per
`am::isolate_roots` (:605): strip zero roots → factor → degree-1
factors become basic `−b/a` directly, higher factors isolate per-factor
with `m_minimal` tracking. Consequences implemented WITH it: cells
gained the `minimal` flag; `compareCore`'s minimal-branch
(refine-until-disjoint) is now the COMMON path and is implemented;
became-basic paths are radical-only (F1 `separate` guard is a pure
safety net); eager rational-root discovery matches default Z3.

**Sequencing decided 2026-07-26 (Danielle's guiding rule, DESIGN-endgame
§6 Q4): EARLY — right after nla-28's signatures, before 12b-ii/12c.**
Build the evaluator/solver once against default parity; re-derive the
affected nla-26 behavioral pins from source during this arc.

