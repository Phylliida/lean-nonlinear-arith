import Mathlib

/-!
# Templates: tangent lemmas (RULES.md rows T1–T2)

Schemas from `nla_tangent_lemmas.cpp`: the surface `z = xy` is bounded by its
tangent planes at a point `(a, b)`, with the direction decided by the sign of
`(x−a)(y−b)`. T1 (tangent lines, `x = a → xy = ay`) is substitution-trivial.
-/

namespace LeanNonlinearArith.Templates.Tangent

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## T2 — tangent planes (4 orientations) -/

theorem plane_gt (x y a b : R) (h : 0 < (x - a) * (y - b)) :
    a * y + b * x - a * b < x * y := by
  nlinarith

theorem plane_lt (x y a b : R) (h : (x - a) * (y - b) < 0) :
    x * y < a * y + b * x - a * b := by
  nlinarith

theorem plane_ge (x y a b : R) (h : 0 ≤ (x - a) * (y - b)) :
    a * y + b * x - a * b ≤ x * y := by
  nlinarith

theorem plane_le (x y a b : R) (h : (x - a) * (y - b) ≤ 0) :
    x * y ≤ a * y + b * x - a * b := by
  nlinarith

end LeanNonlinearArith.Templates.Tangent
