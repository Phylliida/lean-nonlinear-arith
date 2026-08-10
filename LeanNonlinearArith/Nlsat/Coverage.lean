import LeanNonlinearArith.Nlsat.Check

/-!
# nla-19a Slice E — the Q1 coverage lemma (grammar ⇒ the discharge applies)

The proved half of Q1 (F4 of the 2026-08-03 design review): every
in-grammar, in-fragment trace step's semantic obligation is discharged
by the kit in `Nlsat/Check.lean` (the extended S3 family + the linear
root lemmas). The per-constructor theorems below ARE the coverage
statement — each takes the `Trace.Grammar` hypothesis plus exactly the
facts the F-assembly must supply from the bundle context, and concludes
the step's obligation:

| step | grammar supplies | context supplies (F1/F2) | obligation |
|---|---|---|---|
| `linearRoot` | `degreeIn = 1`, lc shape, `mkNeg` fold | `Canon`; lc sign fact when the lc is non-const | emitted-literal failure ⟺ `rootCmp` at `rootVal` |
| `thomQuadratic` | `degreeIn = 2`, `i ∈ {1,2}`, sign ranges | `Canon`; `A`/disc sign facts (from the sign literals failing) | `rootCmp` at `rootVal` ⟺ Thom region formula |
| `cellBound` | side/kind agreement, `1 ≤ i`, `1 ≤ degreeIn` | the paired encoding step's outputs | `rootCmp k (ρ y) (rootVal ρ y i p)` |
| `rootGeneric` | `1 ≤ i` | — | `rootGeneric_discharge` (definitional; `inFragment` keeps `rootCount`/`rootVal` first-order) |
| `leafNumeric` | — | the arith lemma's polys | checker-recomputed marker (F3); no step-level obligation — R4 glue at F2 |

Explicitly NOT here (by design): the per-`(k, i)` evaluation of
`thomFormula` from the payload sign facts is tauto-grade case work the
F2 elaborator does with the concrete payload signs; the by-value
matching of emitted polys against the reconstructed `discPolyOf`/
`pDiffPolyOf` is the F1 decoder's (sound rejection on mismatch); the
19b shapes (`pseudoDivision`/`factorSplit`/`resolution`/`intBranch`)
are out of v0 scope (R1/R6/R7).

The `cellBound` wrappers come in three flavors matching the encoding
the step pairs with (the two-step emission, Trace.lean header):
`cellBound_linear`/`cellBound_thom` (Check.lean, same-p pairing),
`cellBound_plinear` (below — the quadratic-degenerate reroute, where
the paired `linearRoot` is on the reduct `q = B·y + C`), and
`cellBound_generic` (below — the fact is the negated root atom
failing, no encoding).
-/

namespace LeanNonlinearArith.Nlsat

open Check

/-- A constant polynomial evaluates to the constant. -/
theorem evalP_eq_of_asConst (ρ : Nat → ℝ) {p : MPoly} {v : Int}
    (h : p.asConst? = some v) : evalP ρ p = v := by
  cases p with
  | nil =>
    simp only [MPoly.asConst?, Option.some.injEq] at h
    subst h
    simp [evalP]
  | cons t ts =>
    obtain ⟨a, m⟩ := t
    cases ts with
    | nil =>
      cases m with
      | nil =>
        simp only [MPoly.asConst?, Option.some.injEq] at h
        subst h
        simp [evalP, evalM]
      | cons p' m' => simp [MPoly.asConst?] at h
    | cons t' ts' => simp [MPoly.asConst?] at h

/-- `coeffsOf` and `coeffsIn` index identically (the R3 bridge,
pointwise). -/
theorem coeffsOf_getElem!_eq (p : MPoly) (y : Var) (n : Nat) :
    (coeffsOf p y)[n]! = (p.coeffsIn y)[n]! := by
  rw [coeffsOf_eq_coeffsIn_toList, List.getElem!_toArray]

/-- The lc-sign evidence `hAq` of `linearRoot_discharge` is derivable
from the grammar in the const-lc cases (`decide`-grade — the `mkNeg`
folds pinned by the grammar are exactly z3's :746/:767) and from the
lc sign literal failing at `ρ` in the non-const plinear case. -/
theorem linearRoot_hAq (ρ : Nat → ℝ) (y : Var) (p : MPoly) (mkNeg : Bool)
    (lcFact : Option (MPoly × Int))
    (hcond : (match lcFact with
       | none => ∃ v, ((p.coeffsIn y)[1]!).asConst? = some v ∧ v ≠ 0 ∧
           mkNeg = decide (v < 0)
       | some (c, s) => c = (p.coeffsIn y)[1]! ∧ s ≠ 0 ∧
           mkNeg = decide (s < 0) ∧
           ∀ v, c.asConst? = some v → s = Int.sign v))
    (hlc : ∀ c s, lcFact = some (c, s) → c.asConst? = none →
      signMatches s (evalP ρ c)) :
    (0 : ℝ) < (if mkNeg then (-1 : ℝ) else 1) * evalP ρ ((coeffsOf p y)[1]!) := by
  cases lcFact with
  | none =>
    obtain ⟨v, hv, hvne, hmk⟩ := hcond
    rw [coeffsOf_getElem!_eq, evalP_eq_of_asConst ρ hv]
    by_cases hv0 : v < 0
    · have hmk' : mkNeg = true := by simp [hmk, hv0]
      rw [hmk', if_pos rfl, neg_one_mul]
      exact neg_pos.mpr (Int.cast_lt_zero.mpr hv0)
    · have hmk' : mkNeg = false := by simp [hmk, hv0]
      rw [hmk', if_neg Bool.false_ne_true, one_mul]
      exact Int.cast_pos.mpr (lt_of_le_of_ne (le_of_not_gt hv0) (Ne.symm hvne))
  | some cs =>
    obtain ⟨c, s⟩ := cs
    obtain ⟨hc, hsne, hmk, hsign⟩ := hcond
    rw [coeffsOf_getElem!_eq, ← hc]
    by_cases hcc : c.asConst?.isSome
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hcc
      have hs := hsign v hv
      rw [evalP_eq_of_asConst ρ hv]
      have hvne : v ≠ 0 := by
        intro hz
        rw [hz, Int.sign_zero] at hs
        exact hsne hs
      by_cases hv0 : v < 0
      · have hs1 : s = -1 := by rw [hs]; exact Int.sign_eq_neg_one_iff_neg.mpr hv0
        have hmk' : mkNeg = true := by simp [hmk, hs1]
        rw [hmk', if_pos rfl, neg_one_mul]
        exact neg_pos.mpr (Int.cast_lt_zero.mpr hv0)
      · have hvp : 0 < v := lt_of_le_of_ne (le_of_not_gt hv0) (Ne.symm hvne)
        have hs1 : s = 1 := by rw [hs]; exact Int.sign_eq_one_iff_pos.mpr hvp
        have hmk' : mkNeg = false := by simp [hmk, hs1]
        rw [hmk', if_neg Bool.false_ne_true, one_mul]
        exact Int.cast_pos.mpr hvp
    · have hnn : c.asConst? = none := by
        cases hh : c.asConst? with
        | none => rfl
        | some v => simp [hh] at hcc
      have hsm := hlc c s rfl hnn
      rcases hsm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hmk' : mkNeg = true := by simp [hmk, h1]
        rw [hmk', if_pos rfl, neg_one_mul]
        exact neg_pos.mpr h2
      · exact absurd h1 hsne
      · have hmk' : mkNeg = false := by simp [hmk, h1]
        rw [hmk', if_neg Bool.false_ne_true, one_mul]
        exact h2

/-- **Coverage, `linearRoot`** (z3 `mk_linear_root` :861-878): for an
in-grammar step, the emitted literal fails at `ρ` exactly when `ρ y`
bears the root comparison to `rootVal` (any `i` — the linear encoding
is index-independent, as upstream). The one context fact `hlc` is the
lc sign literal failing (only needed when the lc is non-const). -/
theorem coverage_linearRoot (ρ : Nat → ℝ) (k : RootKind) (y : Var) (i : Nat)
    (p : MPoly) (mkNeg : Bool) (lcFact : Option (MPoly × Int))
    (hgram : Grammar (.linearRoot k y p mkNeg lcFact))
    (hcan : MPoly.Canon p)
    (hlc : ∀ c s, lcFact = some (c, s) → c.asConst? = none →
      signMatches s (evalP ρ c)) :
    ¬ SHolds ρ (linearRootEmitted k p mkNeg).1 (linearRootEmitted k p mkNeg).2 ↔
      rootCmp k (ρ y) (rootVal ρ y i p) := by
  cases hgram with
  | linearRoot hdeg hcond =>
    have hAq := linearRoot_hAq ρ y p mkNeg lcFact hcond hlc
    rw [rootVal_eq_linear ρ y i p hdeg]
    apply linearRoot_discharge ρ k y p mkNeg hdeg hcan
    exact_mod_cast hAq

/-- **Coverage, `thomQuadratic`** (z3 `mk_quadratic_root` :787-820):
for an in-grammar step, the root comparison at `rootVal` is the Thom
region formula. The context facts are the `A` and disc sign literals
failing at `ρ` (the disc one stated over the reconstructed
`discPolyOf` — the F1 decoder's by-value match). Evaluating the
formula from the `spd`/`sp` sign facts is F2 case work. -/
theorem coverage_thomQuadratic (ρ : Nat → ℝ) (k : RootKind) (y : Var) (i : Nat)
    (p : MPoly) (sq sa spd sp : Int)
    (hgram : Grammar (.thomQuadratic k y i p sq sa spd sp))
    (hcan : MPoly.Canon p)
    (hAm : signMatches sa (evalP ρ ((coeffsOf p y)[2]!)))
    (hdm : signMatches sq (evalP ρ (discPolyOf p y))) :
    rootCmp k (ρ y) (rootVal ρ y i p) ↔
      thomFormula k i
        (leadSgn (evalP ρ ((coeffsOf p y)[2]!)) * evalP ρ p)
        (leadSgn (evalP ρ ((coeffsOf p y)[2]!)) *
          (2 * evalP ρ ((coeffsOf p y)[2]!) * ρ y +
            evalP ρ ((coeffsOf p y)[1]!))) := by
  cases hgram with
  | thomQuadratic hdeg hi hsq hsa _ _ _ =>
    have hsa' : sa ≠ 0 := by rcases hsa with h | h <;> omega
    rw [rootVal_eq_quad ρ y i p hdeg (hAm.ne_zero hsa')]
    rw [evalP_discPolyOf] at hdm
    exact thom_discharge ρ k y i p sq sa hdeg hi hcan hsa' hAm hsq hdm

/-- `rootVal` in the degenerate-quadratic case: `A` vanishes at `ρ`
(the `sa = 0` reroute of `mk_quadratic_root` :809-812), so the root is
the degenerate linear one. -/
theorem rootVal_eq_degenerate (ρ : Nat → ℝ) (y : Var) (i : Nat) (p : MPoly)
    (hdeg : p.degreeIn y = 2) (hA0 : evalP ρ ((coeffsOf p y)[2]!) = (0 : ℝ)) :
    rootVal ρ y i p =
      -evalP ρ ((coeffsOf p y)[0]!) / evalP ρ ((coeffsOf p y)[1]!) := by
  unfold rootVal
  rw [if_neg (by rw [hdeg]; decide), if_neg (not_not_intro hA0)]

/-- **Coverage, `cellBound` (degenerate pairing)**: the parent
quadratic's `A` vanishes at `ρ` (the `sa = 0` EQ sign literal
failing), and the paired `linearRoot` step is on the reduct
`q = B·y + C` — the ordering it discharges transports to `rootVal` of
the parent. The coefficient links are the F1 decoder's by-value
reconstruction of `q` from `p`'s coefficients. -/
theorem cellBound_plinear (ρ : Nat → ℝ) (k : RootKind) (y : Var) (i : Nat)
    (p q : MPoly)
    (hdeg : p.degreeIn y = 2)
    (hA0 : evalP ρ ((coeffsOf p y)[2]!) = (0 : ℝ))
    (hlink1 : evalP ρ ((coeffsOf q y)[1]!) = evalP ρ ((coeffsOf p y)[1]!))
    (hlink0 : evalP ρ ((coeffsOf q y)[0]!) = evalP ρ ((coeffsOf p y)[0]!))
    (hcmp : rootCmp k (ρ y)
      (-evalP ρ ((coeffsOf q y)[0]!) / evalP ρ ((coeffsOf q y)[1]!))) :
    rootCmp k (ρ y) (rootVal ρ y i p) := by
  rw [rootVal_eq_degenerate ρ y i p hdeg hA0, ← hlink1, ← hlink0]
  exact hcmp

/-- **Coverage, `cellBound` (generic pairing)**: the clause's negated
root atom failing at `ρ` IS the cell fact (z3's no-roots rule
included — the count side comes along for free). -/
theorem cellBound_generic (ρ : Nat → ℝ) (k : RootKind) (y : Var) (i : Nat)
    (p : MPoly)
    (hfails : ¬ ALitHolds ρ (.root ⟨k, y, i, p⟩) true) :
    i ≤ rootCount ρ y p ∧ rootCmp k (ρ y) (rootVal ρ y i p) :=
  (rootGeneric_discharge ρ k y i p).mp hfails

end LeanNonlinearArith.Nlsat
