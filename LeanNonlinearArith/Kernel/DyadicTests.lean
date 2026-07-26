import LeanNonlinearArith.Kernel.Dyadic

/-!
# Dyadic (mpbq) tests

`#guard` pins. Two layers: `toRat` as the semantic oracle over a sample
grid (ring ops, comparisons, floor/ceil, normalization), and pins
transcribed from z3 `mpbq.h/cpp` doc comments (magnitude examples,
`to_mpbq` rounding, select behavior).
-/

namespace LeanNonlinearArith.Kernel.DyadicTests

open LeanNonlinearArith.Kernel
open LeanNonlinearArith.Kernel.Dyadic

/-- Sample values hitting: integers (incl. 0, negatives), normalized
k > 0, and inputs that need normalization through `mk`. -/
def samples : List Dyadic :=
  [mk 0 0, mk 1 0, mk (-1) 0, mk 7 0, mk (-12) 0,
   mk 1 1, mk (-1) 1, mk 3 1, mk 5 3, mk (-5) 3, mk 21 2, mk (-3) 4,
   mk 4 2, mk (-6) 1, mk 40 3, mk 1024 5, mk (-1024) 12, mk 12345 7]

/-- Normalized invariant: `num = 0 → k = 0`; `k > 0 → num` odd. -/
def normalized (a : Dyadic) : Bool :=
  (a.num != 0 || a.k == 0) && (a.k == 0 || a.num % 2 != 0)

#guard samples.all normalized

-- normalization preserves value / hits the canonical form
#guard (mk 4 2) == ofInt 1
#guard (mk (-6) 1) == ofInt (-3)
#guard (mk 40 3) == mk 5 0
#guard (mk 1024 5) == ofInt 32
#guard (mk 0 9) == ofInt 0
#guard samples.all fun a => (mk a.num a.k).toRat == a.toRat

/-! ## Ring ops vs the `Rat` oracle -/

#guard samples.all fun a => samples.all fun b =>
  (add a b).toRat == a.toRat + b.toRat && normalized (add a b)
#guard samples.all fun a => samples.all fun b =>
  (sub a b).toRat == a.toRat - b.toRat && normalized (sub a b)
#guard samples.all fun a => samples.all fun b =>
  (mul a b).toRat == a.toRat * b.toRat && normalized (mul a b)
#guard samples.all fun a => (neg a).toRat == -a.toRat && normalized (neg a)
#guard samples.all fun a => (div2 a).toRat == a.toRat / 2 && normalized (div2 a)
#guard samples.all fun a =>
  (div2k a 5).toRat == a.toRat / 32 && normalized (div2k a 5)
#guard samples.all fun a => (mul2 a).toRat == a.toRat * 2 && normalized (mul2 a)
#guard samples.all fun a =>
  (mul2k a 4).toRat == a.toRat * 16 && normalized (mul2k a 4)
#guard samples.all fun a =>
  [0, 1, 2, 3, 5].all fun n =>
    (power a n).toRat == a.toRat ^ n && normalized (power a n)
#guard samples.all fun a =>
  [-3, 0, 7].all fun (n : Int) =>
    (addInt a n).toRat == a.toRat + (n : Rat) &&
    (subInt a n).toRat == a.toRat - (n : Rat) &&
    (mulInt a n).toRat == a.toRat * (n : Rat) &&
    normalized (addInt a n) && normalized (subInt a n) && normalized (mulInt a n)

/-! ## Comparisons vs the `Rat` oracle -/

#guard samples.all fun a => samples.all fun b =>
  lt a b == decide (a.toRat < b.toRat) &&
  le a b == decide (a.toRat ≤ b.toRat) &&
  (a == b) == (a.toRat == b.toRat)

def ratSamples : List Rat := [0, 1, -1, 3, 1/2, -5/8, 1/3, -2/3, 7/6, 22/7]

#guard samples.all fun a => ratSamples.all fun q =>
  eqRat a q == (a.toRat == q) &&
  ltRat a q == decide (a.toRat < q) &&
  leRat a q == decide (a.toRat ≤ q) &&
  gtRat a q == decide (a.toRat > q) &&
  geRat a q == decide (a.toRat ≥ q)

#guard samples.all fun a => [-2, 0, 1, 5].all fun (n : Int) =>
  eqInt a n == (a.toRat == (n : Rat)) &&
  ltInt a n == decide (a.toRat < (n : Rat)) &&
  leInt a n == decide (a.toRat ≤ (n : Rat)) &&
  gtInt a n == decide (a.toRat > (n : Rat)) &&
  geInt a n == decide (a.toRat ≥ (n : Rat))

/-! ## Magnitude — pins straight from the `mpbq.h` doc comment,
then the defining bounds over the grid -/

#guard magnitudeLb (mk 5 3) == -1     -- 5/2^3:  log2(5) − 3
#guard magnitudeLb (mk 21 2) == 2     -- 21/2^2: log2(21) − 2
#guard magnitudeLb (mk (-3) 4) == -2  -- −3/2^4: log2(3) − 4 + 1

/-- `2^e` as a rational, `e : Int`. -/
def pow2 (e : Int) : Rat :=
  if 0 ≤ e then ((1 <<< e.toNat : Nat) : Rat) else 1 / ((1 <<< (-e).toNat : Nat) : Rat)

#guard samples.all fun a =>
  if a.num == 0 then magnitudeLb a == 0 && magnitudeUb a == 0
  else if 0 < a.num then
    pow2 (magnitudeLb a) ≤ a.toRat && a.toRat ≤ pow2 (magnitudeUb a)
  else
    -pow2 (magnitudeUb a + 1) ≤ a.toRat && a.toRat ≤ -pow2 (magnitudeLb a - 1)

-- lt_1div2k
#guard lt1Div2k (mk 1 3) 2 == true    -- 1/8 < 1/4
#guard lt1Div2k (mk 1 3) 3 == false   -- 1/8 < 1/8 is false
#guard lt1Div2k (mk 3 3) 2 == false   -- 3/8 < 1/4 is false
#guard lt1Div2k (mk (-5) 1) 10 == true
#guard lt1Div2k (mk 0 0) 5 == true

/-! ## Floor / ceiling -/

#guard samples.all fun a =>
  floorInt a == ratFloorInt a.toRat && ceilInt a == ratCeilInt a.toRat

#guard ratSamples.all fun q =>
  ratFloorInt q == q.floor && ratCeilInt q == q.ceil

/-! ## `to_mpbq` (ofRat) -/

#guard ofRat (3/8) == (mk 3 3, true)
#guard ofRat (7 : Rat) == (ofInt 7, true)
#guard ofRat (-5/4) == (mk (-5) 2, true)
-- non-dyadic: flag false, value = num/2^{⌊log₂ den⌋+1}
#guard ofRat (1/3) == (mk 1 2, false)
#guard ofRat (5/6) == (mk 5 3, false)
#guard ofRat (-1/3) == (mk (-1) 2, false)

/-! ## refine_upper / refine_lower -/

-- bracket 1/3 within (0, 1)
#guard
  let (l, u) := refineUpper (1/3) (ofInt 0) (ofInt 1)
  ltRat l (1/3) && gtRat u (1/3) && lt u (ofInt 1)
#guard
  let (l, u) := refineLower (1/3) (ofInt 0) (ofInt 1)
  ltRat l (1/3) && gtRat u (1/3) && lt (ofInt 0) l
-- iterated: widths actually shrink and keep bracketing
#guard
  let (l₁, u₁) := refineLower (2/7) (ofInt 0) (ofInt 1)
  let (l₂, u₂) := refineUpper (2/7) l₁ u₁
  ltRat l₂ (2/7) && gtRat u₂ (2/7) &&
  le (ofInt 0) l₂ && lt (sub u₂ l₂) (sub u₁ l₁)

/-! ## Integer selection -/

#guard selectIntegerDD (mk 5 3) (mk 3 1) == some 1     -- [5/8, 3/2] ∋ 1
#guard selectIntegerDD (mk 5 3) (mk 7 3) == none       -- [5/8, 7/8]
#guard selectIntegerDD (ofInt 3) (mk 7 1) == some 3    -- lower endpoint integer
#guard selectIntegerDD (mk 5 1) (ofInt 3) == some 3    -- upper endpoint integer
#guard selectIntegerDD (mk (-3) 1) (mk (-1) 2) == some (-1)  -- [−3/2, −1/4] ∋ −1
#guard selectIntegerQD (1/3) (mk 3 1) == some 1        -- (1/3, 3/2] ∋ 1
#guard selectIntegerQD (2 : Rat) (mk 5 1) == none      -- (2, 5/2]
#guard selectIntegerQD (2 : Rat) (ofInt 2) == some 2   -- (2, 2] — z3 takes the
  -- integer upper endpoint unconditionally (faithful, even though 2 ∉ (2, 2])
#guard selectIntegerDQ (mk 3 1) (2 : Rat) == none      -- [3/2, 2)
#guard selectIntegerDQ (mk 3 1) (5/2) == some 2        -- [3/2, 5/2) ∋ 2
#guard selectIntegerQQ (1/3) (2/3) == none
#guard selectIntegerQQ (1/3) (4/3) == some 1
#guard selectIntegerQQ (1 : Rat) (2 : Rat) == none     -- (1, 2) has no integer
#guard selectIntegerQQ (-4/3) (-1/3) == some (-1)

/-! ## select_small — smallest-k dyadic witnesses -/

/-- Brute-force oracle: the smallest `k` such that `[l·2^k, u·2^k]`
contains an integer (what `select_small_core` minimizes). -/
def smallestK (l u : Dyadic) : Nat := go 0
where
  go (k : Nat) : Nat :=
    if k > l.k + u.k + 1 then k  -- unreachable: k = min(l.k,u.k) succeeds
    else match selectIntegerDD (mul2k l k) (mul2k u k) with
      | some _ => k
      | none => go (k + 1)
  termination_by l.k + u.k + 2 - k

#guard selectSmallCoreDD (mk 5 2) (mk 7 2) == mk 3 1     -- [5/4, 7/4] → 3/2
#guard selectSmallCoreDD (mk 9 4) (mk 5 3) == mk 5 3     -- [9/16, 5/8] → 5/8 (k=3)
#guard selectSmallCoreDD (mk 5 3) (mk 5 1) == ofInt 1    -- [5/8, 5/2] → 1
-- binary-search branch (min k > threshold), incl. negative mirror
#guard selectSmallCoreDD (mk 2049 12) (mk 2051 12) == mk 1025 11
#guard selectSmallCoreDD (mk (-2051) 12) (mk (-2049) 12) == mk (-1025) 11
-- the result always lies in [lower, upper] and at the oracle's k
#guard samples.all fun a => samples.all fun b =>
  lt b a ||   -- skip unordered pairs (precondition is a ≤ b)
  (let r := selectSmallCoreDD a b
   le a r && le r b && normalized r && r.k == smallestK a b)
#guard samples.all fun a => samples.all fun b =>
  if lt b a then selectSmall a b == none
  else selectSmall a b == some (selectSmallCoreDD a b)

-- mixed-endpoint variants: membership + pins
#guard selectSmallCoreQD (1/3) (mk 1 1) == mk 1 1        -- (1/3, 1/2] → 1/2
#guard selectSmallCoreDQ (mk 1 1) (2/3) == mk 1 1        -- [1/2, 2/3) → 1/2
#guard selectSmallCoreQQ (1/3) (2/3) == mk 1 1           -- (1/3, 2/3) → 1/2
#guard selectSmallCoreQQ (5/2) (7/2) == ofInt 3
#guard
  let r := selectSmallCoreQD (1/3) (mk 3 1)
  gtRat r (1/3) && le r (mk 3 1)
#guard
  let r := selectSmallCoreDQ (mk 5 3) (7/9)
  ge r (mk 5 3) && ltRat r (7/9)
#guard
  let r := selectSmallCoreQQ (-2/3) (-1/3)
  gtRat r (-2/3) && ltRat r (-1/3)

/-! ## toString cosmetics (source display format) -/

#guard toString (mk 5 3) == "5/2^3"
#guard toString (mk 3 1) == "3/2"
#guard toString (ofInt (-7)) == "-7"

end LeanNonlinearArith.Kernel.DyadicTests
