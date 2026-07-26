/-!
# nla-08 — computational ℚ[x] kernel (untrusted)

Dense univariate rational polynomials for the nlsat lane (L2/L3): the
search side (nla-12) and the certified checker's *hint generation*
(nla-09/13/19) both need fast exact polynomial arithmetic. Everything here
is **untrusted by design** — outputs steer the search and get re-certified
per instance by the checker, so no proofs accompany the code (same trust
shape as `Tactic/Oracle.lean`).

Contents (board scope for nla-08): dense ops, gcd, square-free
decomposition (Yun), psc chains — computed as determinants of the exact
Sylvester submatrices from `Projection/S1Statement.lean` (`pscMatrix`), so
the kernel's numbers are definitionally the spec's numbers, with zero
index-translation risk. A subresultant-PRS fast path is a later
optimization if the benchmark demands it. Sturm chains and root counting
ride along as the computational S2-lite (they drive the benchmark and
nla-09 will build isolation on them).

No `Expr`/meta involvement: plain computable defs over `Rat`, exercised by
`#guard` tests in `Kernel/QPolyTests.lean` and timed by
`Kernel/QPolyBench.lean`.
-/

namespace LeanNonlinearArith.Kernel

/-- Dense univariate ℚ[x]: index = degree. Invariant (maintained by `trim`):
the last entry is nonzero; the zero polynomial is the empty array. -/
abbrev QPoly := Array Rat

namespace QPoly

/-- Restore the no-trailing-zeros invariant. -/
def trim (p : Array Rat) : QPoly := Id.run do
  let mut n := p.size
  while n > 0 && p[n - 1]! == 0 do
    n := n - 1
  return p.shrink n

def zero : QPoly := #[]

def isZero (p : QPoly) : Bool := p.isEmpty

/-- Constant polynomial. -/
def C (c : Rat) : QPoly := if c == 0 then #[] else #[c]

def X : QPoly := #[0, 1]

/-- Degree, with the zero polynomial mapped to 0 (guard with `isZero`;
mirrors `natDegree`). -/
def degree (p : QPoly) : Nat := p.size - 1

def coeff (p : QPoly) (i : Nat) : Rat := p.getD i 0

/-- Leading coefficient (0 for the zero polynomial). -/
def lc (p : QPoly) : Rat := if p.isEmpty then 0 else p.back!

def add (p q : QPoly) : QPoly := Id.run do
  let n := max p.size q.size
  let mut r : Array Rat := Array.replicate n 0
  for i in [0:n] do
    r := r.set! i (coeff p i + coeff q i)
  return trim r

def neg (p : QPoly) : QPoly := p.map (-·)

def sub (p q : QPoly) : QPoly := add p (neg q)

/-- Scalar multiple. -/
def smul (c : Rat) (p : QPoly) : QPoly :=
  if c == 0 then #[] else p.map (c * ·)

/-- Multiply by `x^s`. -/
def shift (s : Nat) (p : QPoly) : QPoly :=
  if p.isEmpty then #[] else Array.replicate s 0 ++ p

def mul (p q : QPoly) : QPoly := Id.run do
  if p.isEmpty || q.isEmpty then return #[]
  let mut r : Array Rat := Array.replicate (p.size + q.size - 1) 0
  for i in [0:p.size] do
    for j in [0:q.size] do
      r := r.set! (i + j) (r[i + j]! + p[i]! * q[j]!)
  return trim r

/-- Euclidean division over ℚ: `(quotient, remainder)` with
`deg r < deg d` (or `r = 0`). Returns `(0, p)` for `d = 0`. -/
def divRem (p d : QPoly) : QPoly × QPoly := Id.run do
  if d.isEmpty then return (#[], p)
  let dl := lc d
  let dd := degree d
  let mut r := p
  let mut q : Array Rat := Array.replicate (p.size) 0
  while !r.isEmpty && r.size - 1 ≥ dd && r.size ≥ d.size do
    let k := (r.size - 1) - dd
    let c := lc r / dl
    q := q.set! k c
    -- r := r - c·x^k·d, and the leading term cancels by construction
    let mut r' := r
    for i in [0:d.size] do
      r' := r'.set! (k + i) (r'[k + i]! - c * d[i]!)
    r := trim r'
  return (trim q, r)

def rem (p d : QPoly) : QPoly := (divRem p d).2

def divExact (p d : QPoly) : QPoly := (divRem p d).1

def derivative (p : QPoly) : QPoly := Id.run do
  if p.size ≤ 1 then return #[]
  let mut r : Array Rat := Array.replicate (p.size - 1) 0
  for i in [1:p.size] do
    r := r.set! (i - 1) ((i : Rat) * p[i]!)
  return trim r

def eval (p : QPoly) (x : Rat) : Rat :=
  p.foldr (fun c acc => c + x * acc) 0

/-- Monic normalization (identity on the zero polynomial). -/
def monic (p : QPoly) : QPoly :=
  if p.isEmpty then p else smul (1 / lc p) p

/-- Monic gcd by the Euclidean algorithm, remainders re-normalized to monic
each step (kills ℚ coefficient blowup). Fueled by the degree sum. -/
def gcd (p q : QPoly) : QPoly := Id.run do
  let mut a := monic p
  let mut b := monic q
  for _ in [0:p.size + q.size + 2] do
    if b.isEmpty then return a
    let r := rem a b
    a := b
    b := monic r
  return a

/-- Square-free part `p / gcd(p, p')` (monic). -/
def squarefreePart (p : QPoly) : QPoly :=
  if p.size ≤ 1 then monic p
  else monic (divExact p (gcd p (derivative p)))

/-- Yun's square-free decomposition: returns `[a₁, a₂, …]` with
`p = lc·∏ aᵢ^i`, each `aᵢ` monic square-free, pairwise coprime (trailing
`aᵢ = 1` entries included so the index really is the multiplicity). -/
def yun (p : QPoly) : Array QPoly := Id.run do
  if p.size ≤ 1 then return #[]
  let p := monic p
  let g := gcd p (derivative p)
  if g.size ≤ 1 then return #[p]
  let mut out : Array QPoly := #[]
  -- Yun: b = p/g, c = p'/g, d = c - b'
  let mut b := divExact p g
  let mut c := divExact (derivative p) g
  let mut d := sub c (derivative b)
  for _ in [0:p.size + 1] do
    if b.size ≤ 1 then return out
    let a := gcd b d
    out := out.push a
    b := divExact b a
    c := divExact d a
    d := sub c (derivative b)
  return out

/-! ## psc chains — determinants of the spec's Sylvester submatrices

`pscMatrix`/`psc` mirror `LeanNonlinearArith.pscMatrix`/`psc` from
`Projection/S1Statement.lean` entry for entry: rows are the shifted
polynomials `x^(n-j-1)·f, …, f, x^(m-j-1)·g, …, g` in the monomial basis,
column `c` holds the degree-`(m+n-j-1-c)` coefficients. `psc f g 0` is the
resultant. Intended range `j < min m n`, matching the S1 statement. -/

/-- Coefficient of `x^d` in `x^s · h` (spec: `shiftCoeff`). -/
def shiftCoeff (h : QPoly) (s d : Nat) : Rat :=
  if s ≤ d then coeff h (d - s) else 0

/-- The `j`-th subresultant matrix, rows outermost. -/
def pscMatrix (f g : QPoly) (j : Nat) : Array (Array Rat) := Id.run do
  let m := degree f
  let n := degree g
  let sz := m + n - 2 * j
  let mut rows : Array (Array Rat) := #[]
  for i in [0:sz] do
    let mut row : Array Rat := Array.replicate sz 0
    for c in [0:sz] do
      let d := m + n - j - 1 - c
      let v := if i < n - j then
          shiftCoeff f (n - j - 1 - i) d
        else
          shiftCoeff g (m - j - 1 - (i - (n - j))) d
      row := row.set! c v
    rows := rows.push row
  return rows

/-- Exact determinant by Gaussian elimination with column pivoting. -/
def det (mat : Array (Array Rat)) : Rat := Id.run do
  let n := mat.size
  let mut a := mat
  let mut sign : Rat := 1
  for k in [0:n] do
    -- find a pivot row
    let mut piv := n
    for i in [k:n] do
      if piv == n && a[i]![k]! != 0 then
        piv := i
    if piv == n then return 0
    if piv != k then
      let tmp := a[k]!
      a := a.set! k a[piv]!
      a := a.set! piv tmp
      sign := -sign
    let pv := a[k]![k]!
    for i in [k+1:n] do
      let factor := a[i]![k]! / pv
      if factor != 0 then
        let mut row := a[i]!
        for c in [k:n] do
          row := row.set! c (row[c]! - factor * a[k]![c]!)
        a := a.set! i row
  let mut d := sign
  for k in [0:n] do
    d := d * a[k]![k]!
  return d

/-- The `j`-th principal subresultant coefficient (spec-faithful). -/
def psc (f g : QPoly) (j : Nat) : Rat := det (pscMatrix f g j)

/-- Resultant = `psc 0`. -/
def resultant (f g : QPoly) : Rat := psc f g 0

/-- The discriminant chain `psc p p' j` for `j < deg p` (S1's per-polynomial
sign-invariance obligations). -/
def discChain (p : QPoly) : Array Rat := Id.run do
  let d := derivative p
  let mut out : Array Rat := #[]
  for j in [0:degree p] do
    out := out.push (psc p d j)
  return out

/-- The resultant chain `psc f g j` for `j < min (deg f) (deg g)`. -/
def resChain (f g : QPoly) : Array Rat := Id.run do
  let mut out : Array Rat := #[]
  for j in [0:min (degree f) (degree g)] do
    out := out.push (psc f g j)
  return out

/-! ## Sturm chains and root counting (computational S2-lite)

The canonical Sturm sequence `p, p', -rem …` counts *distinct* real roots
via sign-variation differences — with multiple roots included, because the
chain bottoms out at `gcd(p, p')`. Drives the benchmark; nla-09 builds
root isolation on top. -/

/-- Sturm chain (each element monic — sign-variation counting only needs
signs, and monic remainders keep coefficients small... except monic
normalization FLIPS signs when lc < 0, which breaks variation counts, so
elements are normalized by |lc| instead). -/
def sturmChain (p : QPoly) : Array QPoly := Id.run do
  let absNorm (q : QPoly) : QPoly :=
    if q.isEmpty then q else
      let l := lc q
      smul (1 / (if l < 0 then -l else l)) q
  let mut chain : Array QPoly := #[absNorm p]
  let mut a := p
  let mut b := derivative p
  for _ in [0:p.size + 1] do
    if b.isEmpty then return chain
    chain := chain.push (absNorm b)
    let r := neg (rem a b)
    a := b
    b := absNorm r
  return chain

/-- Sign of a rational, as `-1 / 0 / 1 : Int`. -/
def sgn (q : Rat) : Int := if q < 0 then -1 else if q == 0 then 0 else 1

/-- Sign variations of the chain evaluated at `x`. -/
def signVarAt (chain : Array QPoly) (x : Rat) : Nat := Id.run do
  let mut prev : Int := 0
  let mut v := 0
  for p in chain do
    let s := sgn (eval p x)
    if s != 0 then
      if prev != 0 && s != prev then v := v + 1
      prev := s
  return v

/-- Sign variations at `+∞` (sign = sign of lc) or `-∞` (times parity). -/
def signVarAtInf (chain : Array QPoly) (pos : Bool) : Nat := Id.run do
  let mut prev : Int := 0
  let mut v := 0
  for p in chain do
    let s0 := sgn (lc p)
    let s := if pos || degree p % 2 == 0 then s0 else -s0
    if s != 0 then
      if prev != 0 && s != prev then v := v + 1
      prev := s
  return v

/-- Number of distinct real roots strictly between `a` and `b`, **for
non-root endpoints** (`p(a) ≠ 0 ≠ p(b)`) — the classical Sturm hypothesis.
At root endpoints the variation counts are convention-dependent and this
function makes no promise; every internal caller (isolation, refinement)
maintains the non-root-endpoint invariant. -/
def countRootsBetween (p : QPoly) (a b : Rat) : Nat :=
  let ch := sturmChain p
  signVarAt ch a - signVarAt ch b

/-- Total number of distinct real roots. -/
def countRealRoots (p : QPoly) : Nat :=
  if p.size ≤ 1 then 0
  else
    let ch := sturmChain p
    signVarAtInf ch false - signVarAtInf ch true

/-- Cauchy root bound: all real roots lie in `(-M, M)`. -/
def rootBound (p : QPoly) : Rat := Id.run do
  if p.size ≤ 1 then return 1
  let l := lc p
  let mut m : Rat := 0
  for i in [0:p.size - 1] do
    let a := p[i]! / l
    let a := if a < 0 then -a else a
    if a > m then m := a
  return 1 + m

end QPoly

end LeanNonlinearArith.Kernel
