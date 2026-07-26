import LeanNonlinearArith.Kernel.RAlg
import LeanNonlinearArith.Nlsat.Types

/-!
# nla-12b-i — evaluator anum foundations (Z3-shape, per decision 2026-07-26)

Building blocks for `eval_sign_at` / `isolate_roots` under partial
algebraic assignments, ported to Z3's actual shape (DESIGN-nlsat-quadratic
§4b; Danielle: similarity uncompromised — interval arithmetic first,
exact resultant-based zero test as fallback):

* exact rational interval arithmetic (`RatInterval`) with MPoly
  enclosure evaluation — endpoints are `Rat`, not Z3's dyadic `mpbq`;
  no rounding anywhere, so enclosures are never looser (declared
  representation divergence);
* `resultantElim`: `Res_x(f, q)` for `q` univariate rational — the only
  resultant both call sites need (algebraic cells' defining polynomials
  are univariate) — via the multiplication-matrix determinant on
  `ℚ(...)[x]/(q̂)`;
* `nonzeroRootLowerBound`: `k` with every nonzero root of magnitude
  `> 2^{−k}` (reverse-polynomial Cauchy bound), driving the exact
  zero test's `(−L, L)` termination;
* `RAlg` interval accessors and width-gated refinement.

Assembly of `evalSignAt` / `isolateRootsAt` (with the `q ≡ 0` fallback
paths) is nla-12b-ii.
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

/-- Closed rational interval `[lo, hi]` (`lo ≤ hi` by construction). -/
abbrev RatInterval := Rat × Rat

namespace RatInterval

def ofRat (q : Rat) : RatInterval := (q, q)

def add (i j : RatInterval) : RatInterval := (i.1 + j.1, i.2 + j.2)

def neg (i : RatInterval) : RatInterval := (-i.2, -i.1)

def mul (i j : RatInterval) : RatInterval :=
  let c1 := i.1 * j.1
  let c2 := i.1 * j.2
  let c3 := i.2 * j.1
  let c4 := i.2 * j.2
  (min (min c1 c2) (min c3 c4), max (max c1 c2) (max c3 c4))

/-- Interval power with the even-power tightening (`[-2,3]² = [0,9]`,
not `[-6,9]` — matches `mpbqi_manager::power`). -/
def pow (i : RatInterval) (n : Nat) : RatInterval :=
  if n == 0 then (1, 1)
  else if n % 2 == 1 then (i.1 ^ n, i.2 ^ n)
  else
    let l := i.1 ^ n
    let h := i.2 ^ n
    if i.1 ≥ 0 then (l, h)
    else if i.2 ≤ 0 then (h, l)
    else (0, max l h)

def containsZero (i : RatInterval) : Bool := i.1 ≤ 0 && 0 ≤ i.2

def width (i : RatInterval) : Rat := i.2 - i.1

end RatInterval

namespace MPoly

/-- Enclosure evaluation: every variable of `p` must be covered by `σ`
(rational values enter as point intervals). -/
def evalInterval (p : MPoly) (σ : Var → RatInterval) : RatInterval :=
  p.foldl (fun acc (a, m) =>
    RatInterval.add acc
      (m.foldl (fun acc (x, e) => RatInterval.mul acc (RatInterval.pow (σ x) e))
        (RatInterval.ofRat a)))
    (0, 0)

end MPoly

namespace AnumEval

open QPoly

/-- Powers of `x` modulo a monic `q̂` (degree `d`): entries `0 … maxK`,
each a `QPoly` of degree `< d`. -/
def powModTable (qhat : QPoly) (maxK : Nat) : Array QPoly := Id.run do
  let d := qhat.size - 1
  let mut tbl : Array QPoly := #[#[1]]
  let mut cur : QPoly := #[1]
  for _ in [0:maxK] do
    -- cur := (x · cur) mod q̂
    let mut nxt := QPoly.shift 1 cur
    if nxt.size == d + 1 then
      let c := nxt.back!
      -- subtract c·q̂: the top coefficient cancels exactly and
      -- `QPoly.sub`'s trim strips it
      nxt := QPoly.sub nxt (QPoly.smul c qhat)
    cur := nxt
    tbl := tbl.push cur
  return tbl

/-- Determinant of a small MPoly matrix by first-column Laplace
expansion (matrix sizes = defining-poly degrees; 2 dominates the
quadratic fragment). -/
partial def detMPoly (m : Array (Array MPoly)) : MPoly :=
  let n := m.size
  if n == 0 then MPoly.ofRat 1
  else if n == 1 then m[0]![0]!
  else Id.run do
    let mut acc : MPoly := []
    for i in [0:n] do
      let entry := m[i]![0]!
      if !entry.isZero then
        let minor : Array (Array MPoly) := Id.run do
          let mut rows : Array (Array MPoly) := #[]
          for r in [0:n] do
            if r != i then
              rows := rows.push (m[r]!.extract 1 n)
          return rows
        let term := MPoly.mul entry (detMPoly minor)
        acc := MPoly.add acc (if i % 2 == 0 then term else MPoly.neg term)
    return acc

/-- `Res_x(f, q)` for `q` a univariate rational polynomial of positive
degree (an algebraic cell's defining polynomial): eliminate `x` from `f`.

Method: with `q̂ = q / lc(q)` monic of degree `d`,
`Res(f, q) = lc(q)^{deg_x f} · (−1)^{deg_x f · d} · det(M)` where `M` is
the matrix of multiplication by `f mod q̂` on the basis
`1, x, …, x^{d−1}` of `ℚ(other vars)[x]/(q̂)` — entries are polynomials
in the remaining variables. Roots of the result (in the surviving
variables) contain the eliminations Z3's call sites need; the scalar
factor is kept for faithfulness even though callers only use roots. -/
def resultantElim (f : MPoly) (x : Var) (q : QPoly) : MPoly := Id.run do
  let degF := f.degreeIn x
  if q.size ≤ 1 then
    -- constant q: Res = q^{deg_x f}
    return MPoly.ofRat ((QPoly.lc q) ^ degF)
  let lcq := QPoly.lc q
  let qhat := QPoly.smul (1 / lcq) q
  let d := qhat.size - 1
  -- residues of x^k for all powers we touch (f's, and shifted by basis)
  let tbl := powModTable qhat (degF + d)
  -- f mod q̂ as d coefficient-polynomials in the remaining variables
  let cs := f.coeffsIn x
  let mut red : Array MPoly := Array.replicate d []
  for k in [0:cs.size] do
    let ck := cs[k]!
    if !ck.isZero then
      let rk := tbl[k]!
      for j in [0:d] do
        let coef := QPoly.coeff rk j
        if coef != 0 then
          red := red.set! j (MPoly.add red[j]! (MPoly.smulTerm coef [] ck))
  -- multiplication matrix: column j = (f mod q̂) · x^j mod q̂ in the basis
  let mut m : Array (Array MPoly) := Array.replicate d (Array.replicate d [])
  for j in [0:d] do
    for i in [0:d] do
      let gi := red[i]!
      if !gi.isZero then
        let rij := tbl[i + j]!
        for row in [0:d] do
          let coef := QPoly.coeff rij row
          if coef != 0 then
            let mrow := m[row]!
            m := m.set! row (mrow.set! j
              (MPoly.add mrow[j]! (MPoly.smulTerm coef [] gi)))
  let det := detMPoly m
  let signFactor : Rat := if (degF * d) % 2 == 0 then 1 else -1
  return MPoly.smulTerm (signFactor * lcq ^ degF) [] det

/-- `k` such that every nonzero real root `α` of `p` has `|α| > 2^{−k}`
(`upolynomial::nonzero_root_lower_bound` shape): strip the zero root
(`x^m` factor), reverse — roots of the reversal are the inverses — and
convert its Cauchy upper bound `U` to `k = ⌈log₂ U⌉`. -/
def nonzeroRootLowerBound (p : QPoly) : Nat := Id.run do
  -- strip trailing... leading? zero roots live in the LOW coefficients
  let mut lowZeros := 0
  while lowZeros < p.size && QPoly.coeff p lowZeros == 0 do
    lowZeros := lowZeros + 1
  if lowZeros >= p.size then return 0  -- zero polynomial
  let core := p.extract lowZeros p.size
  if core.size ≤ 1 then return 0       -- constant: no nonzero roots
  let rev := QPoly.trim core.reverse
  if rev.size ≤ 1 then return 0
  let u := QPoly.rootBound rev          -- |1/α| ≤ u  ⇒  |α| ≥ 1/u
  let mut k := 0
  let mut pw : Rat := 1
  while pw < u && k < 4096 do
    pw := pw * 2
    k := k + 1
  return k

end AnumEval

namespace RAlg

/-- Enclosing interval (point interval for rationals). -/
def intervalOf : RAlg → RatInterval
  | .rat q => (q, q)
  | .root _ a b => (a.toRat, b.toRat)

def width : RAlg → Rat
  | .rat _ => 0
  | .root _ a b => (Mpbq.sub b a).toRat

end RAlg

end LeanNonlinearArith.Nlsat
