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

/-! # nla-14 Slice 1 — BoolDef / Tseitin proxy pins

The checker-side proxy semantics (`Atom.bool` + `interp`/`litHolds`
arms) and the `taut`/`conseq` reflection. -/

namespace LeanNonlinearArith.Nlsat

open Check (evalP ALitHolds holds_single_lt)

/-- b0: `x0 < 0`; b1: proxy ⇔ b0. -/
private def pinAtoms : Array (Option Atom) :=
  #[some (.ineq ⟨.lt, [([(1, [(0, 1)])], false)]⟩),
    some (.bool (.lit ⟨0, false⟩))]

/-- Same, but the proxy's def leaf is junk (out-of-range bvar). -/
private def pinAtomsBad : Array (Option Atom) :=
  #[some (.ineq ⟨.lt, [([(1, [(0, 1)])], false)]⟩),
    some (.bool (.lit ⟨9, false⟩))]

-- decodability through the `.bool` arm (precheck's gate, unchanged code)
example : clauseDecodable pinAtoms [⟨1, false⟩, ⟨0, true⟩] = true := by native_decide
-- control: junk slots still rejected
example : clauseDecodable pinAtoms [⟨7, false⟩] = false := by native_decide
example : clauseDecodable pinAtomsBad [⟨1, false⟩] = true := by native_decide

-- proxy semantics: interp unfolds the definition
example (ρ : Nat → ℝ) : interp ρ pinAtoms 1 ↔ evalP ρ [(1, [(0, 1)])] < 0 := by
  simp [interp, boolDefHolds, arithLitHolds, ALitHolds, pinAtoms, Check.Atom.Holds,
    holds_single_lt]

-- literal polarity on a proxy
example (ρ : Nat → ℝ) :
    litHolds ρ pinAtoms ⟨1, true⟩ ↔ ¬ evalP ρ [(1, [(0, 1)])] < 0 := by
  simp [litHolds, boolDefHolds, arithLitHolds, ALitHolds, pinAtoms, Check.Atom.Holds,
    holds_single_lt]

-- junk leaves poison to False (the sound direction — degrades, never unsound)
example (ρ : Nat → ℝ) : interp ρ pinAtomsBad 1 ↔ False := by
  simp [interp, boolDefHolds, arithLitHolds, pinAtomsBad]

-- taut: the three Tseitin definitional-clause shapes for p ⇔ (l0 ∧ l1),
-- with the proxy's def inlined (the Slice-2 compiler's output shape)
example : BoolDef.taut
    (.or (.neg (.and (.lit ⟨0, false⟩) (.lit ⟨1, false⟩))) (.lit ⟨0, false⟩))
    = true := by native_decide
example : BoolDef.taut
    (.or (.neg (.and (.lit ⟨0, false⟩) (.lit ⟨1, false⟩))) (.lit ⟨1, false⟩))
    = true := by native_decide
example : BoolDef.taut
    (.or (.and (.lit ⟨0, false⟩) (.lit ⟨1, false⟩))
      (.or (.neg (.lit ⟨0, false⟩)) (.neg (.lit ⟨1, false⟩))))
    = true := by native_decide
-- disjunction proxy: p ⇔ (l0 ∨ l1), def clause ¬p ∨ l0 ∨ l1
example : BoolDef.taut
    (.or (.neg (.or (.lit ⟨0, false⟩) (.lit ⟨1, false⟩)))
      (.or (.lit ⟨0, false⟩) (.lit ⟨1, false⟩)))
    = true := by native_decide

-- non-tautologies are rejected (the sound direction)
example : BoolDef.taut (.or (.lit ⟨0, false⟩) (.lit ⟨1, false⟩)) = false := by
  native_decide
example : BoolDef.taut (.neg (.and (.lit ⟨0, false⟩) (.lit ⟨1, false⟩))) = false := by
  native_decide

-- conseq: root-clause bridge shapes (the clause follows from the source hyp)
example : BoolDef.conseq (.and (.lit ⟨0, false⟩) (.lit ⟨1, false⟩)) (.lit ⟨0, false⟩)
    = true := by native_decide
example : BoolDef.conseq
    (.or (.lit ⟨0, false⟩) (.lit ⟨1, false⟩))
    (.or (.lit ⟨1, false⟩) (.lit ⟨0, false⟩)) = true := by native_decide
example : BoolDef.conseq (.lit ⟨0, false⟩) (.lit ⟨1, false⟩) = false := by
  native_decide

-- end-to-end: with b1 ⇔ b0 in the table, the definitional clause
-- {¬b1, b0} holds at every ρ — proved by `taut_sound` alone
example (ρ : Nat → ℝ) : clauseHolds ρ pinAtoms [⟨1, true⟩, ⟨0, false⟩] := by
  have ht : BoolDef.taut (.or (.neg (.lit ⟨0, false⟩)) (.lit ⟨0, false⟩)) = true := by
    native_decide
  have h := BoolDef.taut_sound ht (arithLitHolds ρ pinAtoms)
  rcases h with h | h
  · exact ⟨⟨1, true⟩, by decide, h⟩
  · exact ⟨⟨0, false⟩, by decide, h⟩

end LeanNonlinearArith.Nlsat
