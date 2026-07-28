import LeanNonlinearArith.Kernel.Zp

/-!
# nla-27 (slice 1b) — ℤ[x] polynomials (z3 `z_manager` / `core_manager`, non-field)

Dense integer polynomials for the univariate factorization pipeline:
arithmetic, content/primitive-part, exact division, pseudo-remainder,
and the **modular gcd** (`core_manager::mod_gcd` — big-prime images +
CRA, with the Euclid fallback), which is z3's default ℤ[x] gcd
(`gcd` dispatches to `mod_gcd` whenever the manager is not modular).

**Untrusted** (same trust shape as the rest of `Kernel/`).
-/

namespace LeanNonlinearArith.Kernel

/-- Dense integer polynomial, trimmed (no trailing zeros; zero = #[]). -/
abbrev ZPoly := Array Int

namespace ZPoly

/-- Trim trailing zeros (z3 `trim`). -/
def trim (p : Array Int) : ZPoly := Id.run do
  let mut n := p.size
  while n > 0 && p[n - 1]! == 0 do
    n := n - 1
  p.extract 0 n

def isZero (p : ZPoly) : Bool := p.isEmpty

def degree (p : ZPoly) : Nat := p.size - 1

def coeff (p : ZPoly) (i : Nat) : Int := p.getD i 0

/-- Leading coefficient (0 for the zero polynomial). -/
def lc (p : ZPoly) : Int := p.getD (p.size - 1) 0

def add (p q : ZPoly) : ZPoly := Id.run do
  let n := max p.size q.size
  let mut r := Array.mkEmpty n
  for i in [:n] do
    r := r.push (coeff p i + coeff q i)
  trim r

def neg (p : ZPoly) : ZPoly := p.map (-·)

def sub (p q : ZPoly) : ZPoly := add p (neg q)

def mul (p q : ZPoly) : ZPoly := Id.run do
  if p.isEmpty || q.isEmpty then return #[]
  let mut r := Array.replicate (p.size + q.size - 1) 0
  for i in [:p.size] do
    for j in [:q.size] do
      r := r.set! (i + j) (p[i]! * q[j]! + r[i + j]!)
  trim r

/-- Scalar multiplication. -/
def smul (p : ZPoly) (a : Int) : ZPoly :=
  if a == 0 then #[] else trim (p.map (· * a))

/-- Exact scalar division (z3 `div(p, a)`). Precondition: `a ≠ 0`
divides every coefficient (exact by construction in the pipeline). -/
def divScalar (p : ZPoly) (a : Int) : ZPoly :=
  trim (p.map (· / a))

/-- Integer divisibility with z3's `mpz::divides` convention:
`0 | b` iff `b = 0`. -/
def dvdInt (a b : Int) : Bool :=
  if a == 0 then b == 0 else b % a == 0

/-- Content: the positive scalar gcd of all coefficients
(z3 `numeral_manager::gcd(sz, p)`). Precondition: `p` nonzero. -/
def content (p : ZPoly) : Int :=
  (p.foldl (fun g c => (Int.gcd g c : Int)) 0)

/-- z3 `get_primitive_and_content`: `(pp, cont)` with `cont > 0` and
`p = cont · pp`. -/
def getPrimitiveAndContent (p : ZPoly) : ZPoly × Int :=
  let cont := content p
  if cont == 1 then (p, 1)
  else (p.map (· / cont), cont)

/-- Primitive part (z3 `get_primitive`). -/
def primitive (p : ZPoly) : ZPoly := (getPrimitiveAndContent p).1

/-- z3 `core_manager::normalize`: divide out the content; constants map
to their sign (z3 sets `±1` for ANY constant: `is_pos` decides). -/
def normalize (p : ZPoly) : ZPoly :=
  if p.size == 1 then #[if 0 < p[0]! then 1 else -1]
  else
    let g := content p
    if g == 1 then p else p.map (· / g)

def derivative (p : ZPoly) : ZPoly := Id.run do
  if p.size ≤ 1 then return #[]
  let mut r := Array.mkEmpty (p.size - 1)
  for i in [1:p.size] do
    r := r.push ((i : Int) * p[i]!)
  trim r

/-- z3 `flip_sign_if_lm_neg`. -/
def flipSignIfLmNeg (p : ZPoly) : ZPoly :=
  if lc p < 0 then neg p else p

/-- Exact polynomial division (z3 `core_manager::exact_div`): the
quotient when `p2 | p1` in ℤ[x], checked incrementally (leading and
constant coefficients must divide at every step). -/
def exactDiv (p1 p2 : ZPoly) : Option ZPoly := Id.run do
  if p2.isEmpty then return none
  if p1.isEmpty then return some #[]
  if p2.size > p1.size || !dvdInt (lc p2) (lc p1) || !dvdInt (coeff p2 0) (coeff p1 0) then
    return none
  let mut r := Array.replicate (p1.size - p2.size + 1) 0
  let mut cur := p1
  while true do
    if cur.isEmpty then return some r
    if p2.size > cur.size || !dvdInt (lc p2) (lc cur) || !dvdInt (coeff p2 0) (coeff cur 0) then
      return none
    let delta := cur.size - p2.size
    let aR := lc cur / lc p2
    r := r.set! delta aR
    for i in [:p2.size - 1] do
      if p2[i]! != 0 then
        cur := cur.set! (i + delta) (cur[i + delta]! - aR * p2[i]!)
    cur := trim (cur.extract 0 (cur.size - 1))
  return none -- unreachable

/-- Polynomial divisibility test (z3 `core_manager::divides`):
true iff `p2 | p1` in ℤ[x]. -/
def dvd (p1 p2 : ZPoly) : Bool := Id.run do
  if p2.isEmpty then return false
  if p1.isEmpty then return true
  if p2.size > p1.size || !dvdInt (lc p2) (lc p1) then return false
  let mut cur := p1
  while true do
    if cur.isEmpty then return true
    if p2.size > cur.size || !dvdInt (lc p2) (lc cur) then return false
    let delta := cur.size - p2.size
    let b := lc cur / lc p2
    for i in [:p2.size - 1] do
      if p2[i]! != 0 then
        cur := cur.set! (i + delta) (cur[i + delta]! - b * p2[i]!)
    cur := trim (cur.extract 0 (cur.size - 1))
  return true -- unreachable

/-- Floor square root (binary search, fueled). Local helper — the
kernel is deliberately mathlib-free. -/
def isqrt (n : Nat) : Nat :=
  let rec go (fuel : Nat) (lo hi : Nat) : Nat :=
    match fuel with
    | 0 => lo
    | fuel + 1 =>
      if hi ≤ lo + 1 then lo
      else
        let mid := (lo + hi) / 2
        if mid * mid ≤ n then go fuel mid hi else go fuel lo mid
  go (Nat.log2 n + 2) 0 (n + 1)

/-- Signed pseudo-remainder (the non-field branch of z3
`core_manager::rem`): `lc(p2)^d · p1 = Q·p2 + R` for some `d`, `R`
returned, `deg R < deg p2`. -/
def prem (p1 p2 : ZPoly) : ZPoly := Id.run do
  if p2.size ≤ 1 then return #[]
  let mut buf := p1
  while buf.size ≥ p2.size && !buf.isEmpty do
    let sz1 := buf.size
    let mN := sz1 - p2.size
    let aM := buf[sz1 - 1]!
    let bN := lc p2
    for i in [:sz1 - 1] do
      buf := buf.set! i (buf[i]! * bN)
    for i in [:p2.size - 1] do
      buf := buf.set! (i + mN) (buf[i + mN]! - aM * p2[i]!)
    buf := trim (buf.extract 0 (sz1 - 1))
  buf

/-- Euclid gcd over ℤ (z3 `euclid_gcd` non-field branch: pseudo-remainders
made primitive each step, result content-normalized with positive leading
coefficient). Used only as `mod_gcd`'s fallback. -/
def euclidGcdZ (p1 p2 : ZPoly) : ZPoly := Id.run do
  let mut a := p1
  let mut b := p2
  while !b.isEmpty do
    let r := normalize (prem a b)
    a := b
    b := r
  flipSignIfLmNeg (normalize a)

/-! ## Modular gcd (`core_manager::mod_gcd`) -/

/-- z3 `g_big_primes` (`polynomial_primes.h`, the active 231-prime table). -/
def bigPrimes : Array Int := #[
  39103, 39107, 39113, 39119, 39133, 39139, 39157, 39161, 39163, 39181,
  39191, 39199, 39209, 39217, 39227, 39229, 39233, 39239, 39241, 39251,
  39293, 39301, 39313, 39317, 39323, 39341, 39343, 39359, 39367, 39371,
  39373, 39383, 39397, 39409, 39419, 39439, 39443, 39451, 39461, 39499,
  39503, 39509, 39511, 39521, 39541, 39551, 39563, 39569, 39581, 39607,
  39619, 39623, 39631, 39659, 39667, 39671, 39679, 39703, 39709, 39719,
  39727, 39733, 39749, 39761, 39769, 39779, 39791, 39799, 39821, 39827,
  39829, 39839, 39841, 39847, 39857, 39863, 39869, 39877, 39883, 39887,
  39901, 39929, 39937, 39953, 39971, 39979, 39983, 39989, 40009, 40013,
  40031, 40037, 40039, 40063, 40087, 40093, 40099, 40111, 40123, 40127,
  40129, 40151, 40153, 40163, 40169, 40177, 40189, 40193, 40213, 40231,
  40237, 40241, 40253, 40277, 40283, 40289, 40343, 40351, 40357, 40361,
  40387, 40423, 40427, 40429, 40433, 40459, 40471, 40483, 40487, 40493,
  40499, 40507, 40519, 40529, 40531, 40543, 40559, 40577, 40583, 40591,
  40597, 40609, 40627, 40637, 40639, 40693, 40697, 40699, 40709, 40739,
  40751, 40759, 40763, 40771, 40787, 40801, 40813, 40819, 40823, 40829,
  40841, 40847, 40849, 40853, 40867, 40879, 40883, 40897, 40903, 40927,
  40933, 40939, 40949, 40961, 40973, 40993, 41011, 41017, 41023, 41039,
  41047, 41051, 41057, 41077, 41081, 41113, 41117, 41131, 41141, 41143,
  41149, 41161, 41177, 41179, 41183, 41189, 41201, 41203, 41213, 41221,
  41227, 41231, 41233, 41243, 41257, 41263, 41269, 41281, 41299, 41333,
  41341, 41351, 41357, 41381, 41387, 41389, 41399, 41411, 41413, 41443,
  41453, 41467, 41479, 41491, 41507, 41513, 41519, 41521, 41539, 41543,
  41549]

/-- z3 `CRA_combine_images`: combine coefficient images `C1 mod b1` and
`C2 mod b2` into `R mod b1·b2` with balanced representatives
(`(-b1·b2/2, b1·b2/2]`). Returns `(R, b1·b2)`. -/
def craCombineImages (C1 : ZPoly) (b1 : Int) (C2 : ZPoly) (b2 : Int) : ZPoly × Int := Id.run do
  -- b1·inv1 + b2·inv2 = 1 (Bézout, inputs coprime by construction)
  let (inv1', inv2') := ZpCtx.bezoutCoeffs b1 b2
  let inv1 := inv1' % b2
  let inv2 := inv2' % b1
  let a1 := b2 * inv2   -- multiplier for C1 coefficients
  let a2 := b1 * inv1   -- multiplier for C2 coefficients
  let newBound := b1 * b2
  let upper := newBound / 2
  let sz := max C1.size C2.size
  let mut r := Array.mkEmpty sz
  for i in [:sz] do
    let newA0 := (coeff C1 i * a1 + coeff C2 i * a2) % newBound
    let newA := if newA0 > upper then newA0 - newBound else newA0
    r := r.push newA
  return (trim r, newBound)

/-- z3 `core_manager::mod_gcd`: modular gcd over the big primes, CRA
accumulation, primitive-candidate trial division; Euclid fallback after
231 primes (unreachable in practice, ported for faithfulness). -/
def modGcd (u v : ZPoly) : ZPoly := Id.run do
  let (ppU, cU) := getPrimitiveAndContent u
  let (ppV, cV) := getPrimitiveAndContent v
  let cG : Int := (Int.gcd cU cV : Int)
  let dU := ppU.size - 1
  let dV := ppV.size - 1
  let lcG : Int := (Int.gcd (lc ppU) (lc ppV) : Int)
  let mut img : ZPoly := #[]
  let mut bound : Int := 0
  let mut done := false
  let mut result : ZPoly := #[]
  for i in [:bigPrimes.size] do
    if !done then
      let p := bigPrimes[i]!
      let zp : ZpCtx := ⟨p⟩
      let uZp := zp.pnorm ppU
      let vZp := zp.pnorm ppV
      if uZp.size - 1 ≥ dU && vZp.size - 1 ≥ dV then
        -- good prime: leading coefficients did not vanish
        let q := zp.psmul (zp.pgcd uZp vZp) lcG
        if q.size ≤ 1 then
          -- modular gcd is one: the gcd is the content gcd
          result := #[cG]; done := true
        else
          if i == 0 || q.size < img.size || p % 2 == 0 || bound % 2 == 0 then
            img := q; bound := p
          else
            let (img', bound') := craCombineImages q p img bound
            img := img'; bound := bound'
          let candidate := primitive img
          if candidate.size > 0 && dvdInt (lc candidate) lcG &&
              dvd ppU candidate && dvd ppV candidate then
            result := flipSignIfLmNeg (candidate.map (· * cG))
            done := true
  if done then return result
  -- Oops, modular GCD failed, not enough primes: fallback
  euclidGcdZ u v

/-- z3 `core_manager::gcd` dispatcher (non-modular manager ⇒ `mod_gcd`),
with the zero-input special cases (`flip_sign_if_lm_neg`). -/
def gcd (p1 p2 : ZPoly) : ZPoly :=
  if p1.isEmpty then flipSignIfLmNeg p2
  else if p2.isEmpty then flipSignIfLmNeg p1
  else modGcd p1 p2

end ZPoly

end LeanNonlinearArith.Kernel
