import LeanNonlinearArith.Nlsat.Assemble

/-!
# nla-19a Slice F — assembly pins

UP-engine computation pins and an end-to-end `upRefutes_sound`
application. (The real decode/assembly pins land with F4's acceptance
goals.)
-/

namespace LeanNonlinearArith.Nlsat

-- {b0 ∨ b1, ¬b0} ⊩ b1: the unit ¬b1 forces b0, conflict on ¬b0.
example : upRefutes [[⟨0, false⟩, ⟨1, false⟩], [⟨0, true⟩]] [⟨1, false⟩]
    = true := by native_decide

-- the same set does NOT refute ¬b1 (fixpoint) → sound rejection
example : upRefutes [[⟨0, false⟩, ⟨1, false⟩], [⟨0, true⟩]] [⟨1, true⟩]
    = false := by native_decide

-- a 3-clause resolution chain: {x∨y, ¬x∨z, ¬z∨w} ⊩ y∨w
example : upRefutes
    [[⟨0, false⟩, ⟨1, false⟩], [⟨0, true⟩, ⟨2, false⟩], [⟨2, true⟩, ⟨3, false⟩]]
    [⟨1, false⟩, ⟨3, false⟩] = true := by native_decide

-- complementary literals in the target: contradictory units → true
example : upRefutes [] [⟨0, false⟩, ⟨0, true⟩] = true := by native_decide

-- empty target refuted iff F is UP-inconsistent
example : upRefutes [[⟨0, true⟩], [⟨0, false⟩]] [] = true := by native_decide
example : upRefutes [[⟨0, true⟩]] [] = false := by native_decide

-- end-to-end: the soundness theorem applied to hand-built clause facts
example (I : Nat → Prop)
    (h1 : clauseSatI I [⟨0, false⟩, ⟨1, false⟩])
    (h2 : clauseSatI I [⟨0, true⟩])
    (ht : ¬ litSatI I ⟨1, false⟩) : False := by
  apply upRefutes_sound I [[⟨0, false⟩, ⟨1, false⟩], [⟨0, true⟩]] [⟨1, false⟩]
      _ _ (by native_decide)
  · intro C hC
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
    rcases hC with rfl | rfl
    · exact h1
    · exact h2
  · intro l hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
    subst hl
    exact ht

end LeanNonlinearArith.Nlsat
