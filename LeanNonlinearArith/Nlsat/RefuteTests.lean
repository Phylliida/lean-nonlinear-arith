import LeanNonlinearArith.Nlsat.Refute

/-!
# nla-19a F2 skeleton tests — the x0²+x1²<0 refutation's arith lemmas

The snapshot data is the live dump reproduced through the F2 seam
(`Solver.run'` on the unit clause `x0²+x1² < 0`; the dump is recorded
in BOARD's F2-groundwork block). Atom table:

  0: none (true bvar)   1: `x0²+x1² < 0`   2: `x0 = 0`   3: `x0 > 0`   4: `x0 < 0`

One test per `.arith` marker of the refutation (bundles 2, 3, 4, final)
plus a negative probe (an invalid clause must be rejected).
-/

namespace LeanNonlinearArith.Nlsat.Tests.Refute

open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.Check

/- NOTE (kernel-reduction trap, pinned in BOARD): `Monomial.cmp`/
`Monomial.mul`/`MPoly.add`/`MPoly.mul` are well-founded-compiled and
do NOT reduce under kernel whnf/rfl/decide. The atom table is therefore
written in literal-list form (the same form the nla-14 tactic will
quote from the native snapshot) — never via `MPoly` ops on consts. -/
private def x0 : MPoly := [(1, [(0, 1)])]
private def x1 : MPoly := [(1, [(1, 1)])]
private def p01 : MPoly := [(1, [(1, 2)]), (1, [(0, 2)])]

private def dumpAtoms : Array (Option Atom) :=
  #[none,
    some (.ineq ⟨.lt, [(p01, false)]⟩),
    some (.ineq ⟨.eq, [(x0, false)]⟩),
    some (.ineq ⟨.gt, [(x0, false)]⟩),
    some (.ineq ⟨.lt, [(x0, false)]⟩)]

/-- Bundle 2's arith marker (core `x0²+x1²<0`, proj `¬(x0=0)`):
`¬(x0=0) ∨ ¬(x0²+x1²<0)`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ dumpAtoms)
      (arithClause [⟨1, false⟩] [⟨2, true⟩]) := by
  nlsat_arith_valid

/-- Bundle 3's arith marker (proj `x0 > 0`):
`(x0>0) ∨ ¬(x0²+x1²<0)`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ dumpAtoms)
      (arithClause [⟨1, false⟩] [⟨3, false⟩]) := by
  nlsat_arith_valid

/-- Bundle 4's arith marker (proj `x0 < 0`):
`(x0<0) ∨ ¬(x0²+x1²<0)`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ dumpAtoms)
      (arithClause [⟨1, false⟩] [⟨4, false⟩]) := by
  nlsat_arith_valid

/-- The final bundle's arith marker (leafNumeric glue):
`¬(x0>0) ∨ ¬(x0<0)`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ dumpAtoms)
      (arithClause [⟨3, false⟩, ⟨4, false⟩] []) := by
  nlsat_arith_valid

/- Negative probe: `(x0=0) ∨ ¬(x0²+x1²<0)` is NOT valid (ρ 0 = 1,
ρ 1 = 2 falsifies both), so the elaborator must reject. -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ dumpAtoms)
      (arithClause [⟨1, false⟩] [⟨2, false⟩]) := by
  nlsat_arith_valid

/-! ## The 2-var acceptance driver's arith lemmas (design review 5, F-i)

The dump data verbatim from BOARD's F2 dump analysis (post-renameVars-
fix), goal `x0²+x1² ≥ 2 ∧ x0 ≤ 1 ∧ x1 < 1 ∧ x0 > 0 ∧ x1 > 0`. Review 5's
probe showed ALL of these close from literal-failure facts alone (no
step-fact collection): bundles 6/7 and final cores 1/3 directly, final
core 2 via one disequality trichotomy split (its `¬(x0−1=0)` fact is
invisible to linarith). -/

private def qx0 : MPoly := [(1, [(0, 1)])]
private def qx1 : MPoly := [(1, [(1, 1)])]
private def qx0sqx1sqm2 : MPoly := [(1, [(1, 2)]), (1, [(0, 2)]), (-2, [])]
private def qx0m1 : MPoly := [(1, [(0, 1)]), (-1, [])]
private def qx1m1 : MPoly := [(1, [(1, 1)]), (-1, [])]
private def qx0p1 : MPoly := [(1, [(0, 1)]), (1, [])]
private def qx0sqm2 : MPoly := [(1, [(0, 2)]), (-2, [])]

/-- Atom table verbatim from the acceptance dump: 1 `x0²+x1²<2`,
2 `x0>1`, 3 `x1<1`, 4 `x0>0`, 5 `x1>0`, 6 `x0+1>0`, 7 `x0<1`,
8 `x0=1`, 9 `x0²<2`. -/
private def drvAtoms : Array (Option Atom) :=
  #[none,
    some (.ineq ⟨.lt, [(qx0sqx1sqm2, false)]⟩),
    some (.ineq ⟨.gt, [(qx0m1, false)]⟩),
    some (.ineq ⟨.lt, [(qx1m1, false)]⟩),
    some (.ineq ⟨.gt, [(qx0, false)]⟩),
    some (.ineq ⟨.gt, [(qx1, false)]⟩),
    some (.ineq ⟨.gt, [(qx0p1, false)]⟩),
    some (.ineq ⟨.lt, [(qx0m1, false)]⟩),
    some (.ineq ⟨.eq, [(qx0m1, false)]⟩),
    some (.ineq ⟨.lt, [(qx0sqm2, false)]⟩)]

/-- Bundle 6's arith marker (core `[⟨5,false⟩,⟨1,true⟩,⟨3,false⟩]`,
proj `[⟨6,true⟩,⟨7,true⟩]`). -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ drvAtoms)
      (arithClause [⟨5, false⟩, ⟨1, true⟩, ⟨3, false⟩] [⟨6, true⟩, ⟨7, true⟩]) := by
  nlsat_arith_valid

/-- Bundle 7's arith marker (same core, proj `[⟨8,true⟩,⟨4,true⟩,⟨9,true⟩]`
— the thomQuadratic pair on both roots of x0²−2). -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ drvAtoms)
      (arithClause [⟨5, false⟩, ⟨1, true⟩, ⟨3, false⟩]
        [⟨8, true⟩, ⟨4, true⟩, ⟨9, true⟩]) := by
  nlsat_arith_valid

/-- Final bundle, arith core 1: `[⟨7,true⟩,⟨9,true⟩,⟨2,true⟩]`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ drvAtoms)
      (arithClause [⟨7, true⟩, ⟨9, true⟩, ⟨2, true⟩] []) := by
  nlsat_arith_valid

/-- Final bundle, arith core 2: `[⟨7,true⟩,⟨8,true⟩,⟨2,true⟩]` — the
disequality case: needs one `lt_or_gt_of_ne` split of the `¬(x0−1=0)`
fact before linarith closes each branch. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ drvAtoms)
      (arithClause [⟨7, true⟩, ⟨8, true⟩, ⟨2, true⟩] []) := by
  nlsat_arith_valid

/-- Final bundle, arith core 3: `[⟨4,false⟩,⟨6,true⟩]`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ drvAtoms)
      (arithClause [⟨4, false⟩, ⟨6, true⟩] []) := by
  nlsat_arith_valid

/- Negative probe on the driver table: bundle 6 with one proj polarity
flipped is not valid and must be rejected. -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ drvAtoms)
      (arithClause [⟨5, false⟩, ⟨1, true⟩, ⟨3, false⟩] [⟨6, false⟩, ⟨7, true⟩]) := by
  nlsat_arith_valid

/-! ## G2/G3 — multi-factor + even-parity extraction (design review 7)

The G2 target shape (z3 `add_zero_assumption`, nlsat_explain.cpp:261-283):
a composite `∏ pᵢ ≠ 0` as ONE multi-factor eq atom in the core, whose
per-factor diseqs feed the zero-product close of the main eq atom.
G3: even-parity-marked factors (sign-absorbed for lt/gt, parity-blind
for eq). -/

-- x0²-3x0+2 = (x0-1)(x0-2); the composite `¬(x0-1)(x0-2)=0` atom
private def gQuad : MPoly := [(1, [(0, 2)]), (-3, [(0, 1)]), (2, [])]
private def gXm1 : MPoly := [(1, [(0, 1)]), (-1, [])]
private def gXm2 : MPoly := [(1, [(0, 1)]), (-2, [])]
private def gXp1 : MPoly := [(1, [(0, 1)]), (1, [])]

private def gAtoms : Array (Option Atom) :=
  #[none,
    some (.ineq ⟨.eq, [(gQuad, false)]⟩),                 -- 1: p = 0
    some (.ineq ⟨.eq, [(gXm1, false), (gXm2, false)]⟩),   -- 2: composite eq (G2)
    some (.ineq ⟨.lt, [(gXp1, true), (qx0, false)]⟩),     -- 3: even-marked lt (G3)
    some (.ineq ⟨.gt, [(qx0, false)]⟩)]                   -- 4: x0 > 0

/-- G2: core [p=0, composite] — the arith clause `p ≠ 0 ∨ composite`,
i.e. `x0²-3x0+2 = 0 → (x0-1)(x0-2) = 0`. The composite's per-factor
diseqs (x0-1 ≠ 0, x0-2 ≠ 0) feed `zeroProductClose` on p. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ gAtoms)
      (arithClause [⟨1, false⟩, ⟨2, true⟩] []) := by
  nlsat_arith_valid

/-- G3 (eq is parity-blind): core [p=0, even-marked x0+1=0] — the
arith clause `x0²+2x0+1 ≠ 0 ∨ x0+1 = 0` where the x0+1 atom carries the
even parity bit (as z3's factorization would mark `(x0+1)²`). -/
private def gAtoms3 : Array (Option Atom) :=
  #[none,
    some (.ineq ⟨.eq, [([(1, [(0, 2)]), (2, [(0, 1)]), (1, [])], false)]⟩),
    some (.ineq ⟨.eq, [(gXp1, true)]⟩)]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ gAtoms3)
      (arithClause [⟨1, false⟩, ⟨2, true⟩] []) := by
  nlsat_arith_valid

/-- G3 (lt/gt sign extraction with an even factor): core [lt-atom,
gt-atom] — the arith clause `¬holds(3) ∨ ¬(x0 > 0)`, i.e.
`(x0+1 ≠ 0 ∧ x0 < 0) → x0 ≤ 0`: the even factor x0+1 is sign-absorbed,
the odd factor's sign is extracted via `oddProd`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ gAtoms)
      (arithClause [⟨3, false⟩, ⟨4, false⟩] []) := by
  nlsat_arith_valid

/- Negative probe: composite with a WRONG factor (x0-3 for x0-2) —
the clause is invalid (x0 = 2 falsifies it). The per-factor diseqs
extract fine but the zero-product gate finds x0-2 unmatched and the
glue must fail. -/
private def gAtomsBad : Array (Option Atom) :=
  #[none,
    some (.ineq ⟨.eq, [(gQuad, false)]⟩),
    some (.ineq ⟨.eq, [(gXm1, false), ([(1, [(0, 1)]), (-3, [])], false)]⟩)]

#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ gAtomsBad)
      (arithClause [⟨1, false⟩, ⟨2, true⟩] []) := by
  nlsat_arith_valid

/-- Sign-flipped composite factor (audit fix): the composite carries
`2-x0` where the factorizer has `x0-2`. The clause is still valid; the
close converts via `evalP_neg` + `neg_ne_zero`. -/
private def gAtomsFlip : Array (Option Atom) :=
  #[none,
    some (.ineq ⟨.eq, [(gQuad, false)]⟩),
    some (.ineq ⟨.eq, [(gXm1, false), ([(-1, [(0, 1)]), (2, [])], false)]⟩)]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ gAtomsFlip)
      (arithClause [⟨1, false⟩, ⟨2, true⟩] []) := by
  nlsat_arith_valid

/-! ## R-b/R-a (review 9) — multi-eq-positive zero-product + conditional
sign-collapse -/

private def rXm1 : MPoly := [(1, [(0, 1)]), (-1, [])]
private def rXp1 : MPoly := [(1, [(0, 1)]), (1, [])]
private def rQuad : MPoly := [(1, [(0, 2)]), (-1, [])]   -- x0²-1

private def rAtoms : Array (Option Atom) :=
  #[none,
    some (.ineq ⟨.eq, [(rXm1, false), (rXp1, false)]⟩),   -- 1: multi eq
    some (.ineq ⟨.eq, [(rXm1, false)]⟩),                  -- 2: x0-1 = 0
    some (.ineq ⟨.eq, [(rXp1, false)]⟩),                  -- 3: x0+1 = 0
    some (.ineq ⟨.lt, [(rXm1, false), (rXp1, false)]⟩),   -- 4: multi lt
    some (.ineq ⟨.lt, [(rQuad, false)]⟩)]                 -- 5: x0²-1 < 0

/-- R-b: `¬(x0=1 ∨ x0=-1) ∨ x0-1 = 0 ∨ x0+1 = 0` — the multi-eq-POSITIVE
fact (`List.prod` of values = 0) + per-factor diseqs close via
`listEvalProd_ne_zero` — no factorization needed (the factors are
given). -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ rAtoms) [⟨1, true⟩, ⟨2, false⟩, ⟨3, false⟩] := by
  nlsat_arith_valid

/-- R-a: the negative multi-factor lt literal collapses to
`¬((x0-1)(x0+1) < 0)` (both factors known nonzero via literals 2/3),
contradicting the `x0²-1 < 0` fact from literal 5. Clause:
`holds(4) ∨ x0-1=0 ∨ x0+1=0 ∨ ¬(x0²-1 < 0)`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ rAtoms)
      [⟨4, false⟩, ⟨2, false⟩, ⟨3, false⟩, ⟨5, true⟩] := by
  nlsat_arith_valid

private def rXm2 : MPoly := [(1, [(0, 1)]), (-2, [])]

private def rAtoms3 : Array (Option Atom) :=
  #[none,
    some (.ineq ⟨.eq, [(rXm1, false), (rXp1, false), (rXm2, false)]⟩),
    some (.ineq ⟨.eq, [(rXm1, false)]⟩),
    some (.ineq ⟨.eq, [(rXp1, false)]⟩),
    some (.ineq ⟨.eq, [(rXm2, false)]⟩)]

/-- R-b at degree 3 — glue-UNREACHABLE (the product is degree 3,
beyond nlinarith's pairwise round), so this green pin exercises the
`listEvalProd_ne_zero` branch necessarily. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ rAtoms3)
      [⟨1, true⟩, ⟨2, false⟩, ⟨3, false⟩, ⟨4, false⟩] := by
  nlsat_arith_valid

/-- R-a FULL (review 10): the negative multi-factor lt literal with NO
diseq facts anywhere (review 9's conditional collapse would skip this).
The `negChain` expansion splits: `x0-1=0 ∨ (x0+1=0 ∨ ¬((x0-1)(x0+1) < 0))`;
each branch contradicts the `x0²-1 < 0` fact. Clause:
`holds(4) ∨ ¬(x0²-1 < 0)` — valid: |x0|<1 with x0≠±1 ⟹ literal 4;
|x0|≥1 ⟹ literal 5. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ rAtoms) [⟨4, false⟩, ⟨5, true⟩] := by
  nlsat_arith_valid

/-! ## Degenerate shapes (review 11) -/

private def dAtoms : Array (Option Atom) :=
  #[none,
    some (.ineq ⟨.eq, []⟩),                  -- 1: empty-factor eq (⟺ False)
    some (.ineq ⟨.lt, [(rXp1, true)]⟩),      -- 2: all-EVEN lt (oddProd = 1)
    some (.ineq ⟨.lt, []⟩)]                  -- 3: empty-factor lt (⟺ False)

/-- Empty-factor eq atom, negated in the clause: `¬(∃ f ∈ [], f = 0)`
is trivially true; the extracted fact is `1 = 0` (from the False
hypothesis), which the glue closes. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ dAtoms) [⟨1, true⟩] := by
  nlsat_arith_valid

/-- All-even lt atom, negated in the clause: `¬(x0+1 ≠ 0 ∧ 1 < 0)` is
trivially true; the sign fact is `1 < 0`, closed by the glue. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ dAtoms) [⟨2, true⟩] := by
  nlsat_arith_valid

/- Empty-factor lt atom UNnegated: `Holds(lt []) ⟺ 1 < 0` — the clause
is INVALID and must reject. -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ dAtoms) [⟨3, false⟩] := by
  nlsat_arith_valid

/-! ## R-e (review 12) — zero-product close inside an Or-split branch -/

private def eP : MPoly := [(1, [(0, 3)]), (-6, [(0, 2)]), (11, [(0, 1)]), (-6, [])]
  -- x0³-6x0²+11x0-6 = (x0-1)(x0-2)(x0-3)
private def eS : MPoly := [(1, [(1, 1)])]   -- x1
private def eF3 : MPoly := [(1, [(0, 1)]), (-3, [])]   -- x0-3

private def eAtoms : Array (Option Atom) :=
  #[none,
    some (.ineq ⟨.lt, [(eP, true), (eS, false)]⟩),   -- 1: p EVEN-marked
    some (.ineq ⟨.eq, [(gXm1, false), (rXm2, false), (eF3, false)]⟩),  -- 2
    some (.ineq ⟨.lt, [(eS, false)]⟩)]               -- 3: x1 < 0

/-- R-e: the negChain split of literal 1 (`p` even-marked, so the
odd-product is just `x1`) yields `p = 0 ∨ (x1 = 0 ∨ ¬(x1 < 0))`.
Branches `x1 = 0` and `¬(x1 < 0)` close against literal 3 by plain
glue. The `p = 0` branch contradicts the per-factor diseqs from
literal 2 ONLY via factorization: the sole sign fact (`x1 < 0`) is in
a DIFFERENT variable, so nlinarith's one-round pairwise products can't
reach the cubic (glue-unreachable; PRE-FIX this rejects). Clause:
`(p≠0 ∧ x1<0) ∨ x0∈{1,2,3} ∨ x1≥0` — valid by cases on `x1 < 0` and
`p = 0`. Post-fix the per-branch zero-product close handles it. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ eAtoms) [⟨1, false⟩, ⟨2, false⟩, ⟨3, true⟩] := by
  nlsat_arith_valid

/-! ## Review-13 audit pins: multi-chain clause + degenerate chains -/

/-- TWO negChain literals in one clause (the chainLoop multi-chain
recursion): literal 4's chain is `x1 = 0 ∨ (x1 = 0 ∨ ¬(x1² < 0))`
(duplicate factors — the same disjunct twice). The R-e clause plus a
literal can only get more true. -/
private def eAtoms2 : Array (Option Atom) :=
  eAtoms.push (some (.ineq ⟨.lt, [(eS, false), (eS, false)]⟩))

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ eAtoms2)
      [⟨1, false⟩, ⟨2, false⟩, ⟨3, true⟩, ⟨4, false⟩] := by
  nlsat_arith_valid

/-- Single-factor EVEN-marked negative lt: `Holds(lt [(x1,true)]) ⟺
x1≠0 ∧ 1<0` is never true, so its negChain is `x1 = 0 ∨ ¬(1 < 0)` —
a length-1 chain with a trivially-true tail. The clause is valid by
the complementary literal-2 pair; the chain split must not disturb the
close. -/
private def eAtoms3 : Array (Option Atom) :=
  #[none,
    some (.ineq ⟨.lt, [(eS, true)]⟩),
    some (.ineq ⟨.lt, [(eS, false)]⟩)]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ eAtoms3) [⟨1, false⟩, ⟨2, false⟩, ⟨2, true⟩] := by
  nlsat_arith_valid

/-- G4 (census slice): rootGeneric-definite-disc — the clause
`¬(x0 = root₁(x0²+1))` (a negated root atom on a quadratic with disc
= −4 < 0) is valid: the atom's root count is 0, so `i = 1 ≤ rootCount`
is false at every ρ. The close goes through the root-atom extraction
(`.rootPair` fact) plus the definite-disc lane of `rootDefiniteClose`
on lattice-reduced concrete coefficients (the G4 reduction bridges —
the identified kernel-non-reducibility of wf-compiled `MPoly.add`
means `coeffsOf` computation rides the `MPoly.add_cons_cons_*`/
`coeffsOf_go_cons` equation-lemma chain). -/
private def g4Atoms : Array (Option Atom) :=
  #[none,
    some (.root ⟨.eq, 0, 1, [(1, [(0, 2)]), (1, [])]⟩)]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ g4Atoms) (arithClause [⟨1, false⟩] []) := by
  nlsat_arith_valid

/-- The `i == 0` guard (negative probe): with index 0 the count bound
`0 ≤ rootCount` is vacuous and `rootCmp .eq` needs only `ρ 0` coinciding
with the degenerate-root value — so the clause is NOT valid (at
`ρ 0 = 0` the atom holds: count part `0 ≤ 0` ✓, `rootCmp .eq (ρ 0) 0`
— with disc < 0 the square-root convention gives root 0 — ✓). The
close lane must stay `i ≥ 1`-gated; rejection is sound. -/
private def g4AtomsBad : Array (Option Atom) :=
  #[none,
    some (.root ⟨.eq, 0, 0, [(1, [(0, 2)]), (1, [])]⟩)]

/- Negative probe: see above — `0 ≤ rootCount` is always true, so no
count contradiction exists; the glue would have to reject. -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ g4AtomsBad) (arithClause [⟨1, false⟩] []) := by
  nlsat_arith_valid

/-! ## G4 census item 3 — step-fact collection (the cross-links member)

Synthetic fixtures for the one census member that is NOT literal-local:
an arith clause whose contradiction needs `rootVal`-vs-`ρ y` orderings
connected to ineq-atom signs. Root literals `¬⟨k, y, i, p⟩` failing
give opaque `rootCmp k (ρ y) (rootVal ρ y i p)` comparisons (item 2);
the bundle's `thomQuadratic` steps convert them into the evaluated Thom
region formulas — Or/And of comparisons over `evalP ρ p` and the
`2Ay+B` value data, consumed by the Or-splitting glue.

Fixture 1 (const lane): p = x0²−2. The two cell bounds
`ρ 0 > root₁(p) ∧ ρ 0 < root₂(p)` force `ρ 0 ∈ (−√2, √2)`, where
`p(ρ 0) < 0` — contradicting the `p ≥ 0` literal. A and disc are
constants (1 and 8), so z3's `ensure_sign` adds NO literals for them
(the :845 is_const skip): no sign atoms in the table — the numeric lane
supplies `hAm`/`hdm`. -/

private def tsPm2 : MPoly := [(1, [(0, 2)]), (-2, [])]

private def tsAtoms : Array (Option Atom) :=
  #[none,
    some (.root ⟨.gt, 0, 1, tsPm2⟩),        -- 1: ρ 0 > root₁(p)
    some (.root ⟨.lt, 0, 2, tsPm2⟩),        -- 2: ρ 0 < root₂(p)
    some (.ineq ⟨.lt, [(tsPm2, false)]⟩)]   -- 3: p < 0

private def tsSteps : Array TraceStep :=
  #[.cellBound .lower .gt 0 1 tsPm2, .thomQuadratic .gt 0 1 tsPm2 1 1 1 (-1),
    .cellBound .upper .lt 0 2 tsPm2, .thomQuadratic .lt 0 2 tsPm2 1 1 0 (-1)]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tsAtoms)
      (arithClause [] [⟨1, true⟩, ⟨2, true⟩, ⟨3, false⟩]) := by
  nlsat_arith_valid_steps tsSteps

/- The steps are LOAD-BEARING: without them the clause has only opaque
`rootVal` comparisons — no first-order cross-link — so the glue must
fail and the elaborator reject. (Also the corrupted-payload probe
vehicle for item 4's F-w checks.) -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tsAtoms)
      (arithClause [] [⟨1, true⟩, ⟨2, true⟩, ⟨3, false⟩]) := by
  nlsat_arith_valid

/-- Fixture 2 (clause-literal lane): p = x1·x0² − 2 — A = x1 and
disc = 8·x1 are non-constant, so z3's `ensure_sign` emits sign literals
for them: atoms 4 (`A > 0`) and 5 (`disc > 0`), natively the by-value
reconstructed `discPolyOf p` (the R-ii reconstruction). -/

private def tnP : MPoly := [(1, [(0, 2), (1, 1)]), (-2, [])]
private def tnA : MPoly := [(1, [(1, 1)])]
private def tnD : MPoly := [(8, [(1, 1)])]

private def tnAtoms : Array (Option Atom) :=
  #[none,
    some (.root ⟨.gt, 0, 1, tnP⟩),
    some (.root ⟨.lt, 0, 2, tnP⟩),
    some (.ineq ⟨.lt, [(tnP, false)]⟩),
    some (.ineq ⟨.gt, [(tnA, false)]⟩),     -- 4: A > 0 (ensure_sign)
    some (.ineq ⟨.gt, [(tnD, false)]⟩)]     -- 5: disc > 0 (ensure_sign)

private def tnSteps : Array TraceStep :=
  #[.cellBound .lower .gt 0 1 tnP, .thomQuadratic .gt 0 1 tnP 1 1 1 (-1),
    .cellBound .upper .lt 0 2 tnP, .thomQuadratic .lt 0 2 tnP 1 1 0 (-1)]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tnAtoms)
      (arithClause [] [⟨1, true⟩, ⟨2, true⟩, ⟨3, false⟩, ⟨4, true⟩, ⟨5, true⟩]) := by
  nlsat_arith_valid_steps tnSteps

/- Fixture 2 without the steps also must reject (same load-bearing
argument). -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tnAtoms)
      (arithClause [] [⟨1, true⟩, ⟨2, true⟩, ⟨3, false⟩, ⟨4, true⟩, ⟨5, true⟩]) := by
  nlsat_arith_valid

/-! ## G4 item 3 — the linearRoot family + item-4 F-w probes -/

/-- Fixture 3 (linear family): q = x0 − 1. The cell upper bound
`ρ 0 < root₁(q)` (the root is 1) contradicts `¬(q < 0)`. The
`linearRoot` step converts the opaque bound through
`coverage_linearRoot` into the emitted-literal comparison
`evalP ρ q < 0`. Const-lc (`1`), `mkNeg = false`, `lcFact = none`. -/
private def tlQ : MPoly := [(1, [(0, 1)]), (-1, [])]

private def tlAtoms : Array (Option Atom) :=
  #[none,
    some (.root ⟨.lt, 0, 1, tlQ⟩),          -- 1: ρ 0 < root₁(q)
    some (.ineq ⟨.lt, [(tlQ, false)]⟩)]     -- 2: q < 0

private def tlSteps : Array TraceStep :=
  #[.cellBound .upper .lt 0 1 tlQ, .linearRoot .lt 0 tlQ false none]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tlAtoms) (arithClause [] [⟨1, true⟩, ⟨2, false⟩]) := by
  nlsat_arith_valid_steps tlSteps

/- Load-bearing: without the step the bound is opaque `rootVal` data. -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tlAtoms) (arithClause [] [⟨1, true⟩, ⟨2, false⟩]) := by
  nlsat_arith_valid

/- F-w probe (mkNeg corrupt, const-lc): `mkNeg = true` contradicts the
grammar's `mkNeg = decide (1 < 0)` (`tlSteps` at index 1) — the
production's grammar reconstruction throws, the step skips, and the
load-bearing clause rejects. -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tlAtoms) (arithClause [] [⟨1, true⟩, ⟨2, false⟩]) := by
  nlsat_arith_valid_steps
    #[.cellBound .upper .lt 0 1 tlQ, .linearRoot .lt 0 tlQ true none]

/- F-w probe (sq corrupt, semantic): `sq = 0` keeps the grammar but
fights the constant disc = 8 — the production's disc lane skips the
step and the load-bearing clause rejects. -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tsAtoms)
      (arithClause [] [⟨1, true⟩, ⟨2, true⟩, ⟨3, false⟩]) := by
  nlsat_arith_valid_steps
    #[.cellBound .lower .gt 0 1 tsPm2, .thomQuadratic .gt 0 1 tsPm2 0 1 1 (-1),
      .cellBound .upper .lt 0 2 tsPm2, .thomQuadratic .lt 0 2 tsPm2 0 1 0 (-1)]

/- F-w probe (sq=0 placeholder corrupt, grammar-BREAKING): the E1-pinned
`sq = 0 → sp = 0` rule is violated (`sp = −1`) — the grammar ticket
throws on the first step; semantic invisibility of sp itself is pinned
below. Rejected via the same load-bearing argument. -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tsAtoms)
      (arithClause [] [⟨1, true⟩, ⟨2, true⟩, ⟨3, false⟩]) := by
  nlsat_arith_valid_steps
    #[.cellBound .lower .gt 0 1 tsPm2, .thomQuadratic .gt 0 1 tsPm2 0 1 1 (-1),
      .cellBound .upper .lt 0 2 tsPm2, .thomQuadratic .lt 0 2 tsPm2 0 1 (-1) (-1)]

/- Corrupting sq to 0 AND restoring sp := 0 makes the payload
grammar-clean again; the disc-lane mismatch still rejects the step —
so an sq-corruption visible only semantically stays rejected. sp ITSELF
(when sq > 0, everything in range) is not consumed by the
discharge certificates: the accepted trace then still carries
kernel-checked TRUE cross-links (review-6 F-w superset contract,
documented — the walk accepts a superset of grammar-admitted traces). -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tsAtoms)
      (arithClause [] [⟨1, true⟩, ⟨2, true⟩, ⟨3, false⟩]) := by
  nlsat_arith_valid_steps
    #[.cellBound .lower .gt 0 1 tsPm2, .thomQuadratic .gt 0 1 tsPm2 1 1 1 0,
      .cellBound .upper .lt 0 2 tsPm2, .thomQuadratic .lt 0 2 tsPm2 1 1 0 0]

/-! ## G4 item 3 — remaining linear kinds/polarities -/

/-- The `mt` polarity route (`ge` maps to an `lt`-atom at polarity
`false`): q = x0 − 1 with a `ge` lower bound (`ρ 0 ≥ 1` ⟺ `¬(q < 0)`)
against the plain-variable upper bound `le` on x0 (`ρ 0 ≤ 0`). The kind
`.ge` is reachable via `cellBound .lower` with kind `ge` (the
full_dimensional openness family). -/
private def tgX0 : MPoly := [(1, [(0, 1)])]

private def tgAtoms : Array (Option Atom) :=
  #[none,
    some (.root ⟨.ge, 0, 1, tlQ⟩),           -- 1: ρ 0 ≥ root₁(q) = 1
    some (.root ⟨.le, 0, 1, tgX0⟩)]          -- 2: ρ 0 ≤ root₁(x0) = 0

private def tgSteps : Array TraceStep :=
  #[.cellBound .lower .ge 0 1 tlQ, .linearRoot .ge 0 tlQ false none,
    .cellBound .upper .le 0 1 tgX0, .linearRoot .le 0 tgX0 false none]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tgAtoms) (arithClause [] [⟨1, true⟩, ⟨2, true⟩]) := by
  nlsat_arith_valid_steps tgSteps

/-- The `.eq` kind (emitted polarity `true`): q = x0 − 1's unique root
forces `ρ 0 = 1`, contradicted by the `q > 0` fact from the negated
sign literal. -/
private def teAtoms : Array (Option Atom) :=
  #[none,
    some (.root ⟨.eq, 0, 1, tlQ⟩),           -- 1: ρ 0 = root₁(q)
    some (.ineq ⟨.gt, [(tlQ, false)]⟩)]      -- 2: q > 0

private def teSteps : Array TraceStep :=
  #[.cellBound .exact .eq 0 1 tlQ, .linearRoot .eq 0 tlQ false none]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ teAtoms) (arithClause [] [⟨1, true⟩, ⟨2, true⟩]) := by
  nlsat_arith_valid_steps teSteps

/-- The sa = 0 degenerate reroute (z3 :811-812, E1): the clause's root
atom is on the deg-2 parent `tdP = x1·x0² + x0 − 1`; `A = x1` vanishes
at the sample (the `A = 0` sign literal), so the emission reroutes to
`mk_plinear_root` on the reduct `q = x0 − 1` with `lcFact = some (1, 1)`
(the const-lc E1 case — no lc literal needed). The production
transports the root comparison across
`rootVal ρ 0 1 tdP = rootVal ρ 0 1 q` (`rootVal_eq_degenerate` + the
coefficient links). -/
private def tdP : MPoly := [(1, [(0, 2), (1, 1)]), (1, [(0, 1)]), (-1, [])]

private def tdAtoms : Array (Option Atom) :=
  #[none,
    some (.root ⟨.lt, 0, 1, tdP⟩),           -- 1: ρ 0 < root₁(tdP)
    some (.ineq ⟨.eq, [(tnA, false)]⟩),      -- 2: A = x1  (= 0 at the sample)
    some (.ineq ⟨.lt, [(tlQ, false)]⟩)]      -- 3: q < 0

private def tnA2 : MPoly := [(1, [])]

private def tdSteps : Array TraceStep :=
  #[.cellBound .upper .lt 0 1 tdP, .linearRoot .lt 0 tlQ false (some (tnA2, 1))]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tdAtoms)
      (arithClause [] [⟨1, true⟩, ⟨2, true⟩, ⟨3, false⟩]) := by
  nlsat_arith_valid_steps tdSteps

/- The vanishing-A fact is load-bearing for the transport: without the
`A = 0` literal the step skips (sound) and the clause rejects. -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tdAtoms)
      (arithClause [] [⟨1, true⟩, ⟨3, false⟩]) := by
  nlsat_arith_valid_steps tdSteps

/-- The encoding-free lane (foreign traces): `p = 2·x0 − 4`, root 2 — a
`rootGeneric`-shaped clause with NO encoding step: deg-1 const-lc
converts unconditionally. `ρ 0 > root₁(p) = 2` contradicts
`p ≤ 0` (the `gt` literal failing). -/
private def fxP : MPoly := [(2, [(0, 1)]), (-4, [])]

private def fxAtoms : Array (Option Atom) :=
  #[none,
    some (.root ⟨.gt, 0, 1, fxP⟩),           -- 1: ρ 0 > root₁(p)
    some (.ineq ⟨.gt, [(fxP, false)]⟩)]      -- 2: p > 0

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ fxAtoms) (arithClause [] [⟨1, true⟩, ⟨2, false⟩]) := by
  nlsat_arith_valid

end LeanNonlinearArith.Nlsat.Tests.Refute
