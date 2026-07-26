/-!
# nla-26.1 — binary rationals (`mpbq` port)

Faithful port of z3 `src/util/mpbq.{h,cpp}` (Leonardo de Moura, 2011):
binary rationals `num / 2^k`. They form a ring (not closed under
division); Z3 uses them as the endpoint type for algebraic-number
isolating intervals, and the root isolation operations only ever divide
by 2. This replaces the `Rat`-endpoint divergence declared in nla-12a/b-i
(BOARD nla-26.1 — the keystone: `am.select` niceness (26.4) and binary
magnitude gating (26.6) both live on this representation).

Ported surface = the census of what `algebraic_numbers.cpp` and
`upolynomial.cpp` actually call (`bqm().…` / `bqm.…`): constructors and
`normalize`, ring ops, `div2/div2k/mul2/mul2k/power`, the three
comparison families (dyadic/rational/integer), `magnitude_lb/ub`,
`lt_1div2k`, `floor/ceil`, `to_mpbq`, `refine_upper/refine_lower`,
`select_integer` (all four openness variants) and `select_small_core`
(all four), `select_small`.

**Not ported** (declared): `root_lower/root_upper` (single call site
each = `am::mk_root` radical construction, outside our §4b entry-point
surface) and `approx/approx_div` (no call sites in
`algebraic_numbers.cpp`/`upolynomial.cpp`; `mpbqi` interval arithmetic
is *exact* — `basic_interval.h` is "for precise numerals", no rounding
hooks — so rationals enter dyadic intervals only through
`to_mpbq` + `refine_upper/refine_lower` bracketing, which we do port).

Loops that Z3 writes as `while (true)` with real-analytic termination
arguments (`refine_*`: the target rational is not dyadic so no midpoint
ever equals it; `select_small_core`: scaling by 2 eventually puts an
integer in the interval — guaranteed at `k = min(lower.k, upper.k)` for
the dyadic/dyadic case) are `partial def`s with the argument recorded,
matching the unfueled-`isolateRoots` precedent (silent result-dropping
is the failure mode fuel would introduce). Untrusted kernel: every
consequence re-enters proofs through nla-09 certificates only.
-/

namespace LeanNonlinearArith.Kernel

/-- Binary rational `num / 2^k` (z3 `mpbq`). Normalized invariant
(maintained by every constructor below, matching `mpbq_manager`):
`num = 0 → k = 0`, and `k > 0 → num` odd. The raw anonymous constructor
is the only escape hatch — don't use it outside this file/tests. -/
structure Dyadic where
  raw ::
  num : Int
  k   : Nat
deriving Repr, Inhabited, DecidableEq

namespace Dyadic

/-- `n * 2^s` (z3 `mul2k` on `mpz`). -/
private def shl (n : Int) (s : Nat) : Int := n * ((1 <<< s : Nat) : Int)

/-- 2-adic valuation of `n`, capped at `cap`
(`power_of_two_multiple` + the `k > a.m_k` clamp in `normalize`). -/
private def twoAdicCapped : Nat → Nat → Nat
  | 0, _ => 0
  | cap + 1, n => if n % 2 == 0 && n != 0 then 1 + twoAdicCapped cap (n / 2) else 0

/-- z3 `mpbq_manager::normalize`. -/
def normalize (a : Dyadic) : Dyadic :=
  if a.k == 0 then a
  else if a.num == 0 then ⟨0, 0⟩
  else
    let t := twoAdicCapped a.k a.num.natAbs
    -- exact division: t ≤ 2-adic valuation of num
    ⟨a.num / ((1 <<< t : Nat) : Int), a.k - t⟩

/-- General constructor (z3 `set(a, n, k)` — normalizes). -/
def mk (n : Int) (k : Nat) : Dyadic := normalize ⟨n, k⟩

def ofInt (n : Int) : Dyadic := ⟨n, 0⟩

instance : OfNat Dyadic n := ⟨ofInt n⟩

def isInt (a : Dyadic) : Bool := a.k == 0
def isZero (a : Dyadic) : Bool := a.num == 0
def isPos (a : Dyadic) : Bool := 0 < a.num
def isNeg (a : Dyadic) : Bool := a.num < 0
def isNonneg (a : Dyadic) : Bool := 0 ≤ a.num
def isNonpos (a : Dyadic) : Bool := a.num ≤ 0

/-- Value as an exact rational. -/
def toRat (a : Dyadic) : Rat := (a.num : Rat) / (((1 <<< a.k : Nat) : Int) : Rat)

/-! ## Ring operations -/

def add (a b : Dyadic) : Dyadic :=
  if a.k == b.k then normalize ⟨a.num + b.num, a.k⟩
  else if a.k < b.k then normalize ⟨shl a.num (b.k - a.k) + b.num, b.k⟩
  else normalize ⟨a.num + shl b.num (a.k - b.k), a.k⟩

def sub (a b : Dyadic) : Dyadic :=
  if a.k == b.k then normalize ⟨a.num - b.num, a.k⟩
  else if a.k < b.k then normalize ⟨shl a.num (b.k - a.k) - b.num, b.k⟩
  else normalize ⟨a.num - shl b.num (a.k - b.k), a.k⟩

def neg (a : Dyadic) : Dyadic := ⟨-a.num, a.k⟩

def mul (a b : Dyadic) : Dyadic :=
  -- z3 skips normalize when both k > 0 (odd·odd is odd); same result
  if a.k == 0 || b.k == 0 then normalize ⟨a.num * b.num, a.k + b.k⟩
  else ⟨a.num * b.num, a.k + b.k⟩

def addInt (a : Dyadic) (b : Int) : Dyadic :=
  if a.k == 0 then ⟨a.num + b, 0⟩ else normalize ⟨a.num + shl b a.k, a.k⟩

def subInt (a : Dyadic) (b : Int) : Dyadic :=
  if a.k == 0 then ⟨a.num - b, 0⟩ else normalize ⟨a.num - shl b a.k, a.k⟩

def mulInt (a : Dyadic) (b : Int) : Dyadic := normalize ⟨a.num * b, a.k⟩

/-- Divide by 2: bump `k`; only an old integer can need normalization
(z3 comment: "when dividing by 2, we only need to normalize if m_k was
zero"). -/
def div2 (a : Dyadic) : Dyadic :=
  if a.k == 0 then normalize ⟨a.num, 1⟩ else ⟨a.num, a.k + 1⟩

def div2k (a : Dyadic) (s : Nat) : Dyadic :=
  if a.k == 0 then normalize ⟨a.num, s⟩ else ⟨a.num, a.k + s⟩

def mul2 (a : Dyadic) : Dyadic :=
  if a.k == 0 then ⟨a.num * 2, 0⟩ else ⟨a.num, a.k - 1⟩

def mul2k (a : Dyadic) (s : Nat) : Dyadic :=
  if s == 0 then a
  else if a.k < s then ⟨shl a.num (s - a.k), 0⟩
  else ⟨a.num, a.k - s⟩

/-- `a^n`. No normalization needed: an integer stays an integer, and an
odd numerator's power stays odd (z3 comment). -/
def power (a : Dyadic) (n : Nat) : Dyadic := ⟨a.num ^ n, a.k * n⟩

/-! ## Comparisons (dyadic / rational / integer) -/

/-- Structural equality is value equality on normalized dyadics
(z3 `eq`: `a.m_k == b.m_k && eq(a.m_num, b.m_num)`). -/
instance : BEq Dyadic := ⟨fun a b => a.num == b.num && a.k == b.k⟩

def lt (a b : Dyadic) : Bool :=
  if a.k == b.k then a.num < b.num
  else if a.k < b.k then shl a.num (b.k - a.k) < b.num
  else a.num < shl b.num (a.k - b.k)

def gt (a b : Dyadic) : Bool := lt b a
def le (a b : Dyadic) : Bool := !lt b a
def ge (a b : Dyadic) : Bool := !lt a b

def cmp (a b : Dyadic) : Ordering :=
  if lt a b then .lt else if a == b then .eq else .gt

/-- z3 `eq(mpbq, mpq)`. -/
def eqRat (a : Dyadic) (b : Rat) : Bool :=
  if a.k == 0 && b.den == 1 then a.num == b.num
  else shl b.num a.k == a.num * (b.den : Int)

/-- z3 `lt(mpbq, mpq)`: `a.num · b.den < b.num · 2^{a.k}`. -/
def ltRat (a : Dyadic) (b : Rat) : Bool :=
  if a.k == 0 && b.den == 1 then a.num < b.num
  else a.num * (b.den : Int) < shl b.num a.k

def leRat (a : Dyadic) (b : Rat) : Bool :=
  if a.k == 0 && b.den == 1 then a.num ≤ b.num
  else a.num * (b.den : Int) ≤ shl b.num a.k

def gtRat (a : Dyadic) (b : Rat) : Bool := !leRat a b
def geRat (a : Dyadic) (b : Rat) : Bool := !ltRat a b

def eqInt (a : Dyadic) (n : Int) : Bool := a.k == 0 && a.num == n

def ltInt (a : Dyadic) (n : Int) : Bool :=
  if a.k == 0 then a.num < n else a.num < shl n a.k

def leInt (a : Dyadic) (n : Int) : Bool :=
  if a.k == 0 then a.num ≤ n else a.num ≤ shl n a.k

def gtInt (a : Dyadic) (n : Int) : Bool := !leInt a n
def geInt (a : Dyadic) (n : Int) : Bool := !ltInt a n

/-! ## Magnitude (binary order of magnitude — nla-26.6 rides on these) -/

/-- z3 `magnitude_lb`: for `a > 0`, `2^r ≤ a ≤ 2^{r+1}`; for `a < 0`,
`-2^{r+1} ≤ a ≤ -2^r` — with `log2 = ⌊log₂⌋` of the magnitude.
Examples from the source: `5/2^3 ↦ -1`, `21/2^2 ↦ 2`, `-3/2^4 ↦ -2`. -/
def magnitudeLb (a : Dyadic) : Int :=
  if a.num == 0 then 0
  else if 0 < a.num then (Nat.log2 a.num.natAbs : Int) - a.k
  else (Nat.log2 a.num.natAbs : Int) - a.k + 1

/-- z3 `magnitude_ub`: `a ≤ 2^r` (positive) / `a ≤ -2^r` (negative). -/
def magnitudeUb (a : Dyadic) : Int :=
  if a.num == 0 then 0
  else if 0 < a.num then (Nat.log2 a.num.natAbs : Int) - a.k + 1
  else (Nat.log2 a.num.natAbs : Int) - a.k

/-- z3 `lt_1div2k`: `a < 1/2^s`. -/
def lt1Div2k (a : Dyadic) (s : Nat) : Bool :=
  if a.num ≤ 0 then true
  else if a.k ≤ s then false   -- num ≥ 1 ⇒ a ≥ 1/2^{a.k} ≥ 1/2^s
  else a.num < ((1 <<< (a.k - s) : Nat) : Int)

/-! ## Floor / ceiling -/

/-- z3 `floor`: machine (truncating) shift of the numerator, then a `−1`
adjustment for negatives. Exact on normalized values (`k > 0 ⇒ num` odd,
so the truncation is never already exact). -/
def floorInt (a : Dyadic) : Int :=
  if a.k == 0 then a.num
  else
    let f : Int := a.num.sign * ((a.num.natAbs >>> a.k : Nat) : Int)
    if a.num < 0 then f - 1 else f

/-- z3 `ceil` (mirror of `floorInt`). -/
def ceilInt (a : Dyadic) : Int :=
  if a.k == 0 then a.num
  else
    let f : Int := a.num.sign * ((a.num.natAbs >>> a.k : Nat) : Int)
    if 0 < a.num then f + 1 else f

/-- `⌊q⌋` for rationals (`qm.floor`). -/
def ratFloorInt (q : Rat) : Int := q.num.fdiv (q.den : Int)

/-- `⌈q⌉` for rationals (`qm.ceil`). -/
def ratCeilInt (q : Rat) : Int := -((-q.num).fdiv (q.den : Int))

/-! ## Rational entry points (the only rounding in the mpbq world) -/

/-- z3 `to_mpbq`: exact iff `q`'s denominator is a power of two (`true`
flag); otherwise the flag is `false` and the result is the approximation
`q.num / 2^{⌊log₂ den⌋ + 1}`, to be bracketed by `refineLower`/
`refineUpper`. -/
def ofRat (q : Rat) : Dyadic × Bool :=
  if q.den == 1 then (⟨q.num, 0⟩, true)
  else
    let s := Nat.log2 q.den
    if q.den == 1 <<< s then (mk q.num s, true)
    else (mk q.num (s + 1), false)

/-- z3 `refine_upper`: given dyadic `l < q < u` with `q` NOT dyadic
(denominator not a power of two — the precondition Z3 asserts; it is
what makes every bisection midpoint ≠ `q`, hence termination), tighten
`u` to a dyadic `u'` with `q < u' < u`, possibly also raising `l`. -/
partial def refineUpper (q : Rat) (l u : Dyadic) : Dyadic × Dyadic :=
  let mid := div2 (add l u)
  if gtRat mid q then (l, mid) else refineUpper q mid u

/-- z3 `refine_lower` (mirror). -/
partial def refineLower (q : Rat) (l u : Dyadic) : Dyadic × Dyadic :=
  let mid := div2 (add l u)
  if ltRat mid q then (mid, u) else refineLower q l mid

/-! ## Integer selection (all four openness variants) -/

/-- z3 `select_integer(mpbq, mpbq)`: some integer in `[lower, upper]`,
preferring the endpoints then `⌈lower⌉`. -/
def selectIntegerDD (lower upper : Dyadic) : Option Int :=
  if lower.k == 0 then some lower.num
  else if upper.k == 0 then some upper.num
  else
    let cl := ceilInt lower
    if cl ≤ floorInt upper then some cl else none

/-- z3 `select_integer(mpq, mpbq)`: some integer in `(lower, upper]`. -/
def selectIntegerQD (lower : Rat) (upper : Dyadic) : Option Int :=
  if upper.k == 0 then some upper.num
  else
    let cl := if lower.den == 1 then lower.num + 1 else ratCeilInt lower
    if cl ≤ floorInt upper then some cl else none

/-- z3 `select_integer(mpbq, mpq)`: some integer in `[lower, upper)`. -/
def selectIntegerDQ (lower : Dyadic) (upper : Rat) : Option Int :=
  if lower.k == 0 then some lower.num
  else
    let cl := ceilInt lower
    let fu := if upper.den == 1 then upper.num - 1 else ratFloorInt upper
    if cl ≤ fu then some cl else none

/-- z3 `select_integer(mpq, mpq)`: some integer in `(lower, upper)`. -/
def selectIntegerQQ (lower upper : Rat) : Option Int :=
  let cl := if lower.den == 1 then lower.num + 1 else ratCeilInt lower
  let fu := if upper.den == 1 then upper.num - 1 else ratFloorInt upper
  if cl ≤ fu then some cl else none

/-! ## Small-witness selection (`select_small_core` — nla-26.4 rides on
these: the preference for few-bit, small-denominator witnesses) -/

/-- z3 `LINEAR_SEARCH_THRESHOLD`. -/
def linearSearchThreshold : Nat := 8

/-- Linear branch: scale both endpoints by 2 until the scaled interval
contains an integer. Terminates: at `k = min(lower.k, upper.k)` one
endpoint is an integer. -/
private partial def selectSmallLinear (l2k u2k : Dyadic) (k : Nat) : Dyadic :=
  let l := mul2 l2k
  let u := mul2 u2k
  let k := k + 1
  match selectIntegerDD l u with
  | some n => mk n k
  | none => selectSmallLinear l u k

/-- Binary-search branch (faithful transcription of the `min_k`/`max_k`
loop, including the recompute-at-`max_k` corner when the last probe
failed). -/
private partial def selectSmallBinary (lower upper : Dyadic) (minK maxK : Nat) : Dyadic :=
  let midK := minK + (maxK - minK) / 2
  match selectIntegerDD (mul2k lower midK) (mul2k upper midK) with
  | some n =>
    if minK == midK then mk n midK
    else selectSmallBinary lower upper minK midK
  | none =>
    if minK + 1 == maxK then
      match selectIntegerDD (mul2k lower maxK) (mul2k upper maxK) with
      | some n => mk n maxK
      | none => panic! "selectSmallBinary: k = min(lower.k, upper.k) must admit an integer"
    else selectSmallBinary lower upper (midK + 1) maxK

/-- z3 `select_small_core(mpbq, mpbq)`: some dyadic in `[lower, upper]`
minimizing size in bits — an integer if the interval contains one,
otherwise the smallest `k` whose `2^k`-scaling does. Pre: `lower ≤ upper`. -/
partial def selectSmallCoreDD (lower upper : Dyadic) : Dyadic :=
  match selectIntegerDD lower upper with
  | some n => ofInt n
  | none =>
    let maxK := min lower.k upper.k
    if maxK ≤ linearSearchThreshold then selectSmallLinear lower upper 0
    else selectSmallBinary lower upper 0 maxK

/-- z3 `select_small`: `none` iff `lower > upper`. -/
def selectSmall (lower upper : Dyadic) : Option Dyadic :=
  if gt lower upper then none else some (selectSmallCoreDD lower upper)

/-- z3 `select_small_core(mpq, mpbq)`: some dyadic in `(lower, upper]`.
Pre: `lower < upper`. Terminates: doubling makes the scaled open interval
wider than 1. -/
partial def selectSmallCoreQD (lower : Rat) (upper : Dyadic) : Dyadic :=
  match selectIntegerQD lower upper with
  | some n => ofInt n
  | none => go (lower * 2) (mul2 upper) 1
where
  go (l2k : Rat) (u2k : Dyadic) (k : Nat) : Dyadic :=
    match selectIntegerQD l2k u2k with
    | some n => mk n k
    | none => go (l2k * 2) (mul2 u2k) (k + 1)

/-- z3 `select_small_core(mpbq, mpq)`: some dyadic in `[lower, upper)`.
Pre: `lower < upper`. -/
partial def selectSmallCoreDQ (lower : Dyadic) (upper : Rat) : Dyadic :=
  match selectIntegerDQ lower upper with
  | some n => ofInt n
  | none => go (mul2 lower) (upper * 2) 1
where
  go (l2k : Dyadic) (u2k : Rat) (k : Nat) : Dyadic :=
    match selectIntegerDQ l2k u2k with
    | some n => mk n k
    | none => go (mul2 l2k) (u2k * 2) (k + 1)

/-- z3 `select_small_core(mpq, mpq)`: some dyadic in `(lower, upper)`.
Pre: `lower < upper`. -/
partial def selectSmallCoreQQ (lower upper : Rat) : Dyadic :=
  match selectIntegerQQ lower upper with
  | some n => ofInt n
  | none => go (lower * 2) (upper * 2) 1
where
  go (l2k u2k : Rat) (k : Nat) : Dyadic :=
    match selectIntegerQQ l2k u2k with
    | some n => mk n k
    | none => go (l2k * 2) (u2k * 2) (k + 1)

instance : ToString Dyadic :=
  ⟨fun a =>
    if a.k == 0 then toString a.num
    else if a.k == 1 then s!"{a.num}/2"
    else s!"{a.num}/2^{a.k}"⟩

end Dyadic

end LeanNonlinearArith.Kernel
