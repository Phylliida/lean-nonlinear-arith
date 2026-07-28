import Mathlib

/-!
# nla-27 (slice 1a) — modular arithmetic context (z3 `zp_numeral_manager` / `zp_manager`)

Arithmetic mod `m` for polynomial factorization: prime moduli `p ≤ 31`
(Berlekamp, `factor_max_prime` default) and prime-power moduli `p^e`
(Hensel lifting). Elements are kept normalized to `[0, m)` (z3
`p_normalize`). Polynomial ops mirror the `zp_manager` surface the
factorization pipeline uses: schoolbook `divRem` (requires a unit
leading coefficient — always true over prime fields, and the lifted
factors are monic over prime powers), Euclid `gcd` with monic result,
`extGcd`, `mkMonic`, `isSquareFree`.

**Untrusted** (same trust shape as the rest of `Kernel/`): results are
consumed only by the search side; wrong answers surface as failed
certificates downstream, never unsoundness.
-/

namespace LeanNonlinearArith.Kernel

/-- Modulus context. `m` is the prime `p` or a prime power `p^e`. -/
structure ZpCtx where
  m : Int
deriving Repr, BEq, Inhabited

namespace ZpCtx

/-- z3 `p_normalize`: reduce into `[0, m)`. Lean's `%` is the
non-negative remainder for positive divisors. -/
def norm (c : ZpCtx) (a : Int) : Int := a % c.m

def add (c : ZpCtx) (a b : Int) : Int := (a + b) % c.m
def sub (c : ZpCtx) (a b : Int) : Int := (a - b) % c.m
def mul (c : ZpCtx) (a b : Int) : Int := (a * b) % c.m
def neg (c : ZpCtx) (a : Int) : Int := (-a) % c.m

/-- Multiplicative inverse mod `m` (z3 `zp_numeral_manager::inv`).
Precondition (z3 SASSERT): `gcd(a, m) = 1` — over prime fields every
nonzero element, over prime powers every non-multiple of `p` (the
lifted factors are monic, so their leading coefficients are units).
Via Bézout (mathlib `Nat.gcdA`): `gcdA·a' + gcdB·m = gcd(a', m) = 1`. -/
def inv (c : ZpCtx) (a : Int) : Int :=
  (Nat.gcdA (c.norm a).natAbs c.m.natAbs) % c.m

/-- `a·b + out` mod m (z3 `addmul`). -/
def addmul (c : ZpCtx) (a b out : Int) : Int := (a * b + out) % c.m

/-- `out − a·b` mod m (z3 `submul`). -/
def submul (c : ZpCtx) (a b out : Int) : Int := (out - a * b) % c.m

/-! ## Polynomials over the context (dense, trimmed, coefficients in `[0, m)`) -/

/-- Trim trailing zeros (z3 `trim`). -/
def ptrim (p : Array Int) : Array Int := Id.run do
  let mut n := p.size
  while n > 0 && p[n - 1]! == 0 do
    n := n - 1
  p.extract 0 n

/-- Normalize every coefficient into `[0, m)` and trim (z3
`to_zp_manager`). -/
def pnorm (c : ZpCtx) (p : Array Int) : Array Int :=
  ptrim (p.map (c.norm ·))

def pIsZero (p : Array Int) : Bool := p.isEmpty

def pdegree (p : Array Int) : Nat := p.size - 1

def pcoeff (p : Array Int) (i : Nat) : Int := p.getD i 0

/-- Leading coefficient (0 for the zero polynomial). -/
def plc (p : Array Int) : Int := p.getD (p.size - 1) 0

def padd (c : ZpCtx) (p q : Array Int) : Array Int := Id.run do
  let n := max p.size q.size
  let mut r := Array.mkEmpty n
  for i in [:n] do
    r := r.push (c.add (pcoeff p i) (pcoeff q i))
  ptrim r

def pneg (c : ZpCtx) (p : Array Int) : Array Int :=
  ptrim (p.map (c.neg ·))

def psub (c : ZpCtx) (p q : Array Int) : Array Int :=
  padd c p (pneg c q)

def pmul (c : ZpCtx) (p q : Array Int) : Array Int := Id.run do
  if p.isEmpty || q.isEmpty then return #[]
  let mut r := Array.replicate (p.size + q.size - 1) 0
  for i in [:p.size] do
    for j in [:q.size] do
      r := r.set! (i + j) (c.addmul p[i]! q[j]! r[i + j]!)
  ptrim r

/-- Scalar multiplication (z3 `mul(p, c)`). -/
def psmul (c : ZpCtx) (p : Array Int) (a : Int) : Array Int :=
  ptrim (p.map (c.mul · a))

/-- Exact scalar division by a unit (z3 `div(p, a)` after inversion).
Precondition: `a` is a unit mod `m` dividing every coefficient — in the
pipeline `a` is always a unit and the division is exact by construction. -/
def pdivScalarUnit (c : ZpCtx) (p : Array Int) (a : Int) : Array Int :=
  psmul c p (c.inv a)

/-- Make monic (z3 `mk_monic`): multiply by the inverse of the leading
coefficient. Precondition: `p` nonzero with unit leading coefficient. -/
def pmkMonic (c : ZpCtx) (p : Array Int) : Array Int :=
  pdivScalarUnit c p (plc p)

def pderivative (c : ZpCtx) (p : Array Int) : Array Int := Id.run do
  if p.size ≤ 1 then return #[]
  let mut r := Array.mkEmpty (p.size - 1)
  for i in [1:p.size] do
    r := r.push (c.mul (i : Int) p[i]!)
  ptrim r

/-- Schoolbook division with remainder (z3 `zp_manager::div_rem`).
Precondition (z3 SASSERT): the divisor's leading coefficient is a unit
mod `m` — over prime fields any nonzero divisor; over prime powers the
pipeline only divides by monic factors. -/
def pdivRem (c : ZpCtx) (p1 p2 : Array Int) : Array Int × Array Int := Id.run do
  if p2.isEmpty then return (#[], p1)   -- unreachable in the pipeline
  let lcInv := c.inv (plc p2)
  let mut r := c.pnorm p1
  let mut q : Array Int := #[]
  while r.size ≥ p2.size && !r.isEmpty do
    let d := r.size - p2.size
    let coeff := c.mul (plc r) lcInv
    -- extend q to position d
    while q.size ≤ d do
      q := q.push 0
    q := q.set! d coeff
    -- r := r − coeff·x^d·p2
    for i in [:p2.size] do
      r := r.set! (i + d) (c.submul coeff p2[i]! r[i + d]!)
    r := ptrim (r.extract 0 (r.size - 1)) -- leading coeff cancelled
  return (ptrim q, r)

/-- Exact division by a unit-lc divisor (z3 `div`): the quotient,
discarding the (zero) remainder. -/
def pdiv (c : ZpCtx) (p1 p2 : Array Int) : Array Int :=
  (pdivRem c p1 p2).1

/-- Euclid gcd with monic result (z3 `zp_manager::gcd` — `euclid_gcd`
with `field() = true`, so the result is made monic). -/
def pgcd (c : ZpCtx) (p1 p2 : Array Int) : Array Int := Id.run do
  let mut a := c.pnorm p1
  let mut b := c.pnorm p2
  while !b.isEmpty do
    let r := (pdivRem c a b).2
    a := b
    b := r
  if a.isEmpty then return #[]
  pmkMonic c a

/-- Extended gcd (z3 `zp_manager::ext_gcd`): returns `(U, V, D)` with
`U·p1 + V·p2 = D`, `D` monic, `deg U < deg p2`, `deg V < deg p1`
(the pipeline uses it on coprime inputs, `D = 1`). -/
def pextGcd (c : ZpCtx) (p1 p2 : Array Int) : Array Int × Array Int × Array Int := Id.run do
  let mut r0 := p1; let mut r1 := p2
  let mut s0 : Array Int := #[1]; let mut s1 : Array Int := #[]
  let mut t0 : Array Int := #[]; let mut t1 : Array Int := #[1]
  while !r1.isEmpty do
    let (q, r) := pdivRem c r0 r1
    r0 := r1; r1 := r
    let sNew := psub c s0 (pmul c q s1)
    s0 := s1; s1 := sNew
    let tNew := psub c t0 (pmul c q t1)
    t0 := t1; t1 := tNew
  -- normalize so that D is monic
  if r0.isEmpty then return (#[], #[], #[])
  let lcInv := c.inv (plc r0)
  (psmul c s0 lcInv, psmul c t0 lcInv, psmul c r0 lcInv)

/-- z3 `zp_manager::is_square_free`: gcd with the derivative is a
nonzero constant. -/
def pisSquareFree (c : ZpCtx) (p : Array Int) : Bool :=
  match pgcd c p (pderivative c p) with
  | #[] => false
  | g  => g.size == 1

/-- Evaluation (Horner, mod m). -/
def peval (c : ZpCtx) (p : Array Int) (x : Int) : Int := Id.run do
  let mut acc : Int := 0
  for i in [:p.size] do
    acc := c.addmul (pcoeff p (p.size - 1 - i)) 1 (c.mul acc x)
  acc

end ZpCtx

end LeanNonlinearArith.Kernel
