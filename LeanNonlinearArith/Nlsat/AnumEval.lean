import LeanNonlinearArith.Kernel.RAlg
import LeanNonlinearArith.Nlsat.Types

/-!
# nla-12b-i — evaluator anum foundations (Z3-shape, per decision 2026-07-26)

Building blocks for `eval_sign_at` / `isolate_roots` under partial
algebraic assignments, ported to Z3's actual shape (DESIGN-nlsat-quadratic
§4b; Danielle: similarity uncompromised — interval arithmetic first,
exact resultant-based zero test as fallback):

* exact dyadic interval arithmetic (`MpbqI` — nla-26.1b second half:
  the 1:1 `mpbqi`/`basic_interval.h` port, replacing the interim
  `RatInterval` divergence) with MPoly enclosure evaluation; ℤ
  coefficients (nla-26.2) + denominator-clearing substitution mean
  nothing in the evaluator path ever needs rounding, exactly as in Z3
  (`eval_sign_at` asserts every interval-phase value is algebraic);
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

/-- Closed dyadic interval `[lo, hi]` — z3 `mpbqi`
(`basic_interval_manager<mpbq_manager, false>`; "for precise numerals":
every operation below is exact, there are no rounding hooks). -/
structure MpbqI where
  lo : Mpbq
  hi : Mpbq
deriving Repr, Inhabited, BEq

namespace MpbqI

def ofMpbq (a : Mpbq) : MpbqI := ⟨a, a⟩

def ofInt (n : Int) : MpbqI := ⟨.ofInt n, .ofInt n⟩

/-- `basic_interval.h` add. -/
def add (i j : MpbqI) : MpbqI := ⟨Mpbq.add i.lo j.lo, Mpbq.add i.hi j.hi⟩

/-- `basic_interval.h` sub (`lo − hi'`, `hi − lo'`). -/
def sub (i j : MpbqI) : MpbqI := ⟨Mpbq.sub i.lo j.hi, Mpbq.sub i.hi j.lo⟩

def neg (i : MpbqI) : MpbqI := ⟨Mpbq.neg i.hi, Mpbq.neg i.lo⟩

/-- `basic_interval.h` mul: min/max over the four endpoint products. -/
def mul (i j : MpbqI) : MpbqI :=
  let c1 := Mpbq.mul i.lo j.lo
  let c2 := Mpbq.mul i.lo j.hi
  let c3 := Mpbq.mul i.hi j.lo
  let c4 := Mpbq.mul i.hi j.hi
  ⟨Mpbq.min (Mpbq.min c1 c2) (Mpbq.min c3 c4),
   Mpbq.max (Mpbq.max c1 c2) (Mpbq.max c3 c4)⟩

/-- `basic_interval.h` power (:326): odd exponents map endpoints;
even exponents split on the interval's sign (`[-2,3]² = [0,9]`). -/
def pow (i : MpbqI) (n : Nat) : MpbqI :=
  if n % 2 == 1 then ⟨Mpbq.power i.lo n, Mpbq.power i.hi n⟩
  else
    let l := Mpbq.power i.lo n
    let h := Mpbq.power i.hi n
    if i.lo.isNonneg then ⟨l, h⟩
    else if i.hi.isNeg then ⟨h, l⟩
    else ⟨Mpbq.ofInt 0, Mpbq.max l h⟩

def containsZero (i : MpbqI) : Bool := i.lo.isNonpos && i.hi.isNonneg

def isPos (i : MpbqI) : Bool := i.lo.isPos

def isNeg (i : MpbqI) : Bool := i.hi.isNeg

def width (i : MpbqI) : Mpbq := Mpbq.sub i.hi i.lo

end MpbqI

namespace MPoly

/-- Enclosure evaluation: every variable of `p` must be covered by `σ`.
ℤ coefficients (nla-26.2) enter as exact dyadic point intervals —
nothing here rounds, exactly as in Z3's evaluator. -/
def evalInterval (p : MPoly) (σ : Var → MpbqI) : MpbqI :=
  p.foldl (fun acc (a, m) =>
    MpbqI.add acc
      (m.foldl (fun acc (x, e) => MpbqI.mul acc (MpbqI.pow (σ x) e))
        (MpbqI.ofInt a)))
    (MpbqI.ofInt 0)

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

/-! Since nla-26.2 `MPoly` is ℤ-coefficient; the multiplication-matrix
construction needs ℚ scalars internally (monic reduction divides by
`lc q`), so the matrix work runs on a small **parallel ℚ-term copy**
(same shapes, `Rat` coefficients) and the final determinant is ℤ-scaled
back by the positive lcm of denominators — root/sign-preserving,
matching the scaling conventions of `substRat`/`ofQPoly`. -/

/-- ℚ-coefficient terms for the matrix internals (parallel copy of the
`MPoly` list representation). -/
abbrev QTerms := List (Rat × Monomial)

namespace QTerms

def isZero (p : QTerms) : Bool := p.isEmpty

def add : QTerms → QTerms → QTerms
  | [], q => q
  | p, [] => p
  | (a, m) :: p, (b, n) :: q =>
    match Monomial.cmp m n with
    | .gt => (a, m) :: add p ((b, n) :: q)
    | .lt => (b, n) :: add ((a, m) :: p) q
    | .eq =>
      let c := a + b
      if c == 0 then add p q else (c, m) :: add p q

def neg (p : QTerms) : QTerms := p.map fun (a, m) => (-a, m)

def smulTerm (c : Rat) (mo : Monomial) (p : QTerms) : QTerms :=
  if c == 0 then [] else p.map fun (a, m) => (c * a, Monomial.mul mo m)

def mul (p q : QTerms) : QTerms :=
  p.foldl (fun acc (a, m) => add acc (smulTerm a m q)) []

def ofMPoly (p : MPoly) : QTerms := p.map fun (a, m) => ((a : Rat), m)

/-- Back to ℤ coefficients, scaled by the positive lcm of denominators. -/
def toMPolyScaled (p : QTerms) : MPoly :=
  let l : Nat := p.foldl (fun (acc : Nat) (t : Rat × Monomial) => Nat.lcm acc t.1.den) 1
  p.foldl (fun acc (a, m) => MPoly.add acc [((a * (l : Rat)).num, m)]) []

end QTerms

/-- Determinant of a small `QTerms` matrix by first-column Laplace
expansion (matrix sizes = defining-poly degrees; 2 dominates the
quadratic fragment). -/
partial def detQTerms (m : Array (Array QTerms)) : QTerms :=
  let n := m.size
  if n == 0 then [(1, [])]
  else if n == 1 then m[0]![0]!
  else Id.run do
    let mut acc : QTerms := []
    for i in [0:n] do
      let entry := m[i]![0]!
      if !entry.isZero then
        let minor : Array (Array QTerms) := Id.run do
          let mut rows : Array (Array QTerms) := #[]
          for r in [0:n] do
            if r != i then
              rows := rows.push (m[r]!.extract 1 n)
          return rows
        let term := QTerms.mul entry (detQTerms minor)
        acc := QTerms.add acc (if i % 2 == 0 then term else QTerms.neg term)
    return acc

/-- `Res_x(f, q)` for `q` a univariate rational polynomial of positive
degree (an algebraic cell's defining polynomial): eliminate `x` from `f`.

Method: with `q̂ = q / lc(q)` monic of degree `d`,
`Res(f, q) = lc(q)^{deg_x f} · det(M)` (`det(M) = ∏ f(β)` over `q`'s
roots — the norm; no parity factor in this orientation) where `M` is
the matrix of multiplication by `f mod q̂` on the basis
`1, x, …, x^{d−1}` of `ℚ(other vars)[x]/(q̂)` — entries are polynomials
in the remaining variables. Roots of the result (in the surviving
variables) contain the eliminations Z3's call sites need; the scalar
factor is kept for faithfulness even though callers only use roots. -/
def resultantElim (f : MPoly) (x : Var) (q : QPoly) : MPoly := Id.run do
  let degF := f.degreeIn x
  if q.size ≤ 1 then
    -- constant q: Res = q^{deg_x f}
    return QTerms.toMPolyScaled [((QPoly.lc q) ^ degF, [])]
  let lcq := QPoly.lc q
  let qhat := QPoly.smul (1 / lcq) q
  let d := qhat.size - 1
  -- residues of x^k for all powers we touch (f's, and shifted by basis)
  let tbl := powModTable qhat (degF + d)
  -- f mod q̂ as d coefficient-polynomials in the remaining variables
  let cs := f.coeffsIn x
  let mut red : Array QTerms := Array.replicate d []
  for k in [0:cs.size] do
    let ck := cs[k]!
    if !ck.isZero then
      let ckq := QTerms.ofMPoly ck
      let rk := tbl[k]!
      for j in [0:d] do
        let coef := QPoly.coeff rk j
        if coef != 0 then
          red := red.set! j (QTerms.add red[j]! (QTerms.smulTerm coef [] ckq))
  -- multiplication matrix: column j = (f mod q̂) · x^j mod q̂ in the basis
  let mut m : Array (Array QTerms) := Array.replicate d (Array.replicate d [])
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
              (QTerms.add mrow[j]! (QTerms.smulTerm coef [] gi)))
  let det := detQTerms m
  -- Res_x(f, q) = lc(q)^{deg_x f} · ∏_{q(β)=0} f(β), and det(M) is
  -- exactly the norm ∏ f(β): no parity factor for this orientation.
  -- (A (−1)^{degF·d} factor sat here through 12b-i — a sign bug the
  -- quadratic lane could never see, since d = 2 keeps the exponent
  -- even; the nla-25.3 cube-root pin caught it.)
  return QTerms.toMPolyScaled (QTerms.smulTerm (lcq ^ degF) [] det)

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

/-- Isolating interval of an algebraic cell (z3 `var2interval` — only
defined for non-basic values: rationals are substituted away before the
interval phase, `eval_sign_at`'s `SASSERT(!v.is_basic())`). -/
def intervalD : RAlg → Option MpbqI
  | .rat _ => none
  | .root _ a b _ => some ⟨a, b⟩

def width : RAlg → Rat
  | .rat _ => 0
  | .root _ a b _ => (Mpbq.sub b a).toRat

end RAlg

end LeanNonlinearArith.Nlsat
