import LeanNonlinearArith.Kernel.QPoly

/-!
# nla-29.1c — bivariate (ℚ[x])[y] for anum `mk_binary` resultants (untrusted)

Z3's `mk_add_polynomial` / `mk_mul_polynomial` (algebraic_numbers.cpp:1000-1044)
build the result polynomial for `a + b` / `a · b` of two algebraic cells as

    r(x) = Res_y(pa(x∓y), pb(y))        — add/sub
    r(x) = Res_y(y^n · pa(x/y), pb(y))  — mul, n = deg pa

in the general multivariate manager. Per the BOARD nla-29 decision
(2026-07-31), this file computes the same resultants by the approved
12b-i route extended to this shape: `pb` is always a univariate defining
polynomial, so with `p̂b = pb/lc(pb)` monic of degree `d`,

    Res_y(f, pb) = lc(pb)^{deg_y f} · det(M)

where `M` is the matrix of multiplication by `f mod p̂b` on the basis
`1, y, …, y^{d−1}` of `(ℚ[x])[y]/(p̂b)` — exact over `ℚ[x]`. Capability
identical to z3's on every reachable input (both compute the exact
mathematical resultant); multivariate second arguments are deferred to
nla-30. No parity factor in this orientation (the 25.3 lesson, pinned
by the √2+√3 differential below).

Same trust shape as the rest of `Kernel/`: untrusted search-side code;
outputs steer `mk_binary`'s factor/Sturm selection and everything
trusted is re-certified downstream.
-/

namespace LeanNonlinearArith.Kernel

/-- Bivariate polynomial as a dense polynomial in `y` with dense `ℚ[x]`
coefficients: `b[j]` = coefficient of `y^j`. Invariant (via `trim`):
the last entry is not the zero `QPoly`. -/
abbrev BivPoly := Array QPoly

namespace BivPoly

open QPoly

/-- Restore the no-trailing-zero-coefficient invariant. -/
def trim (b : BivPoly) : BivPoly := Id.run do
  let mut n := b.size
  while n > 0 && b[n - 1]!.isEmpty do
    n := n - 1
  return b.shrink n

def zero : BivPoly := #[]

def isZero (b : BivPoly) : Bool := b.isEmpty

/-- Constant (in `y`) bivariate from a `QPoly`. -/
def ofQPoly (p : QPoly) : BivPoly := if p.isEmpty then #[] else #[p]

/-- Degree in `y` (0 for zero; guard with `isZero`). -/
def degY (b : BivPoly) : Nat := b.size - 1

def coeffY (b : BivPoly) (j : Nat) : QPoly := b.getD j #[]

def lc (b : BivPoly) : QPoly := if b.isEmpty then #[] else b.back!

def add (f g : BivPoly) : BivPoly := Id.run do
  let n := max f.size g.size
  let mut r : BivPoly := Array.replicate n #[]
  for j in [0:n] do
    r := r.set! j (QPoly.add (coeffY f j) (coeffY g j))
  return trim r

def neg (f : BivPoly) : BivPoly := f.map QPoly.neg

def sub (f g : BivPoly) : BivPoly := add f (neg g)

/-- Scalar multiple by a `ℚ[x]` polynomial. -/
def smul (c : QPoly) (f : BivPoly) : BivPoly :=
  if c.isEmpty then #[] else trim (f.map (QPoly.mul c))

/-- Multiply by `y^s`. -/
def shiftY (s : Nat) (f : BivPoly) : BivPoly :=
  if f.isEmpty then #[] else Array.replicate s #[] ++ f

def mul (f g : BivPoly) : BivPoly := Id.run do
  if f.isEmpty || g.isEmpty then return #[]
  let mut r : BivPoly := Array.replicate (f.size + g.size - 1) #[]
  for i in [0:f.size] do
    for j in [0:g.size] do
      r := r.set! (i + j) (QPoly.add r[i + j]! (QPoly.mul f[i]! g[j]!))
  return trim r

/-- `x − y` as a bivariate. -/
def xMinusY : BivPoly := #[QPoly.X, QPoly.C (-1)]

/-- `x + y` as a bivariate. -/
def xPlusY : BivPoly := #[QPoly.X, QPoly.C 1]

/-- z3 `compose_x_minus_y` (polynomial.cpp:5171): `pa(x − y)`, by Horner
composition. z3 runs its general `compose` with `muladd` — the value is
the same polynomial by construction (both are exact composition). -/
def composeXMinusY (pa : QPoly) : BivPoly := Id.run do
  let mut r : BivPoly := #[]
  for i in [0:pa.size] do
    r := add (mul r xMinusY) (ofQPoly (QPoly.C pa[pa.size - 1 - i]!))
  return r

/-- z3 `compose_x_plus_y` (polynomial.cpp:5191): `pa(x + y)`. -/
def composeXPlusY (pa : QPoly) : BivPoly := Id.run do
  let mut r : BivPoly := #[]
  for i in [0:pa.size] do
    r := add (mul r xPlusY) (ofQPoly (QPoly.C pa[pa.size - 1 - i]!))
  return r

/-- z3 `compose_x_div_y` (polynomial.cpp:5018): `y^n · pa(x/y)` where
`n = deg pa` — coefficient of `y^j` is `pa[n−j] · x^{n−j}`. -/
def composeXDivY (pa : QPoly) : BivPoly := Id.run do
  if pa.isEmpty then return #[]
  let n := pa.size - 1
  let mut r : BivPoly := Array.replicate (n + 1) #[]
  for j in [0:n+1] do
    r := r.set! j (QPoly.smul pa[n - j]! (QPoly.shift (n - j) #[1]))
  return trim r

/-- Remainder of `f` modulo a divisor `q` that is monic in `y` (leading
coefficient the constant `1 : ℚ[x]`). Exact: monic division needs no
coefficient-field inverses, so `QPoly` arithmetic suffices. -/
def modMonic (f q : BivPoly) : BivPoly := Id.run do
  if q.isEmpty then return f
  let dq := q.size - 1
  let mut r := f
  while r.size > dq do
    let k := r.size - 1 - dq
    let c := lc r
    -- r := r − c·y^k·q; the leading terms cancel by construction
    r := sub r (smul c (shiftY k q))
  return r

/-- Powers of `y` modulo the monic `qhat` (degree `d` in `y`), entries
`0 … maxK`. The entries have *constant* `QPoly` coefficients whenever
`qhat`'s coefficients are constant — the case below, since `p̂b` comes
from a univariate `pb`. -/
def powModTableB (qhat : BivPoly) (maxK : Nat) : Array BivPoly := Id.run do
  let d := qhat.size - 1
  let mut tbl : Array BivPoly := #[ofQPoly #[1]]
  let mut cur : BivPoly := ofQPoly #[1]
  for _ in [0:maxK] do
    let mut nxt := shiftY 1 cur
    if nxt.size == d + 1 then
      let c := lc nxt
      nxt := sub nxt (smul c qhat)
    cur := nxt
    tbl := tbl.push cur
  return tbl

/-- Determinant of a small `QPoly`-entry matrix by first-column Laplace
expansion (parallel to `AnumEval.detQTerms`). Laplace is exact over the
*ring* `ℚ[x]` (no inverses needed); exponential in the matrix size —
fine at defining-polynomial degrees in the quadratic fragment and
beyond (`d = deg pb`). A fraction-free (Bareiss) route for large `d` is
nla-30 territory if deep nesting ever demands it. -/
partial def detBiv (m : Array (Array QPoly)) : QPoly :=
  let n := m.size
  if n == 0 then #[1]
  else if n == 1 then m[0]![0]!
  else Id.run do
    let mut acc : QPoly := #[]
    for i in [0:n] do
      let entry := m[i]![0]!
      if !entry.isEmpty then
        let minor : Array (Array QPoly) := Id.run do
          let mut rows : Array (Array QPoly) := #[]
          for r in [0:n] do
            if r != i then
              rows := rows.push (m[r]!.extract 1 n)
          return rows
        let term := QPoly.mul entry (detBiv minor)
        acc := QPoly.add acc (if i % 2 == 0 then term else QPoly.neg term)
    return acc

/-- `Res_y(f, pb)` for `pb` a univariate rational polynomial of positive
degree (an algebraic cell's defining polynomial) and `f` bivariate: the
`mk_binary` resultant shape. `lc(pb)^{deg_y f} · det(M)` per the file
header; the scalar is kept for faithfulness even though callers
(`mk_binary`'s factor/Sturm selection, nla-29.2) only use roots. -/
def resultantElimY (f : BivPoly) (pb : QPoly) : QPoly := Id.run do
  if f.isEmpty then return #[]
  let degF := f.size - 1
  if pb.size ≤ 1 then
    -- constant pb: Res_y(f, c) = c^{deg_y f}
    return QPoly.C (QPoly.lc pb ^ degF)
  let lcpb := QPoly.lc pb
  -- p̂b = pb/lc(pb) as a bivariate with constant coefficients
  let qhatB : BivPoly := (QPoly.smul (1 / lcpb) pb).map QPoly.C
  let d := qhatB.size - 1
  let tbl := powModTableB qhatB (degF + d)
  let fmod := modMonic f qhatB
  -- multiplication matrix: column j = (fmod · y^j) mod p̂b in the basis
  let mut m : Array (Array QPoly) := Array.replicate d (Array.replicate d #[])
  for j in [0:d] do
    for i in [0:d] do
      let fi := coeffY fmod i
      if !fi.isEmpty then
        let rij := tbl[i + j]!
        for row in [0:d] do
          let cr := coeffY rij row
          if !cr.isEmpty then
            -- cr is constant (p̂b's coefficients are)
            let r := QPoly.coeff cr 0
            let mrow := m[row]!
            m := m.set! row (mrow.set! j (QPoly.add mrow[j]! (QPoly.smul r fi)))
  let det := detBiv m
  return QPoly.smul (lcpb ^ degF) det

end BivPoly

end LeanNonlinearArith.Kernel
