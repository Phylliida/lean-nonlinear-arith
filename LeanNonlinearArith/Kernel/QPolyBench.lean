import LeanNonlinearArith.Kernel.QPoly

/-!
# nla-08 benchmark — the perf derisk

Two stress profiles chosen from what the nlsat lane will actually ask of
the kernel:

* **Sturm on Wilkinson-40** — `∏ (x-i), i = 1..40`: degree 40, huge exact
  coefficients. The Sturm chain over ℚ is the classic coefficient-blowup
  torture test; root counting must still be exact.
* **psc chains at deep-tail projection degrees** — discriminant chain of a
  dense degree-16 polynomial and resultant chain of two dense degree-16s:
  the determinant route costs `O(s³)` per coefficient at `s = m+n-2j`,
  which is the price of spec-faithfulness. Quadratic-lane inputs
  (per-variable degree ≤ 2, projections ≤ 8-ish) measured sub-ms; deg-16
  chains are the full-nlsat worst case and the trigger threshold for a
  future subresultant-PRS fast path.

Timings print at build/`lake env lean` time via `#eval`; the `#guard`-style
checks inside keep the numbers honest (a fast wrong kernel is worthless).
Machine-load caveat applies as always — call counts and exactness are the
stable signal, wall-times are indicative.
-/

namespace LeanNonlinearArith.Kernel.QPoly.Bench

open LeanNonlinearArith.Kernel.QPoly

/-- `∏ (x - i)` for `i = 1..n`. -/
def wilkinson (n : Nat) : QPoly := Id.run do
  let mut acc : QPoly := #[1]
  for i in [1:n+1] do
    acc := mul acc #[-(i : Rat), 1]
  return acc

/-- Dense polynomial with pseudo-random-ish integer coefficients. -/
def denseSpec (deg : Nat) (seed : Nat) : QPoly := Id.run do
  let mut cs : Array Rat := #[]
  let mut s := seed
  for _ in [0:deg+1] do
    s := (s * 1103515245 + 12345) % 2147483648
    cs := cs.push ((s % 201 : Nat) - 100 : Int)
  return trim cs

/-! Benchmark honesty note: pure computations must be FORCED before the
closing timestamp — an IO-observable branch (`unless … throw`) between the
`let` and the second `monoMsNow` does it. Without that, the compiler is
free to defer the work into the later `println` interpolation and every
phase reads 0ms (observed; the first version of this file had exactly that
bug). -/

def benchMain : IO Unit := do
  -- Sturm on Wilkinson-40 (degree 40, coefficients ~10^47)
  let w := wilkinson 40
  let t0 ← IO.monoMsNow
  let n := countRealRoots w
  unless n == 40 do throw <| IO.userError s!"wilkinson-40 root count {n} ≠ 40"
  let t1 ← IO.monoMsNow
  IO.println s!"sturm/wilkinson-40: {n} roots, {t1 - t0}ms"
  -- interval counting exercises rational-point evaluation of the chain
  let t2 ← IO.monoMsNow
  let k := countRootsBetween w (11/2) (31/2)
  unless k == 10 do throw <| IO.userError s!"wilkinson-40 (5.5,15.5] count {k} ≠ 10"
  let t3 ← IO.monoMsNow
  IO.println s!"sturm/wilkinson-40 interval (11/2, 31/2]: {k} roots, {t3 - t2}ms"
  -- discriminant chain at deep-tail projection degree (dense, ±10^6 coeffs)
  let f := denseSpec 16 42
  let t4 ← IO.monoMsNow
  let dc := discChain f
  unless dc.size == 16 && dc[0]! != 12345 do throw <| IO.userError "disc chain"
  let t5 ← IO.monoMsNow
  IO.println s!"pscChain/disc deg-16: {dc.size} coeffs, {t5 - t4}ms"
  -- resultant chain, two dense degree-16s (size-32 determinants)
  let g := denseSpec 16 1337
  let t6 ← IO.monoMsNow
  let rc := resChain f g
  unless rc.size == 16 && rc[0]! != 12345 do throw <| IO.userError "res chain"
  let t7 ← IO.monoMsNow
  IO.println s!"pscChain/res deg-16×deg-16: {rc.size} coeffs, {t7 - t6}ms"
  -- gcd + square-free at Wilkinson scale: w² shares w with (w²)'
  let t8 ← IO.monoMsNow
  let sf := squarefreePart (mul w w)
  unless sf == monic w do throw <| IO.userError "squarefree(w²) ≠ w"
  let t9 ← IO.monoMsNow
  IO.println s!"squarefree/wilkinson-40²: deg {degree sf}, {t9 - t8}ms"

#eval benchMain

end LeanNonlinearArith.Kernel.QPoly.Bench
