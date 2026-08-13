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

/-- The non-const lc clause lane: parent `tdP2 = x1·x0² + x2·x0 − 1`,
`A = x1` vanishing at the sample (atom 2), and the reduct
`q = x2·x0 − 1` with NON-CONST lc `x2` of sign −1 at the sample — the
lc sign literal (atom 3). `mkNeg = decide (−1 < 0) = true`: the
produced fact is `evalP ρ (1 − x2·x0) < 0`; with the `ρ 0 > 0` fact
(atom 4), `ρ2·ρ0 < 0 < 1` closes. -/
private def tdP2 : MPoly :=
  [(1, [(0, 2), (1, 1)]), (1, [(0, 1), (2, 1)]), (-1, [])]
private def tdQ2 : MPoly := [(1, [(0, 1), (2, 1)]), (-1, [])]
private def tnX2 : MPoly := [(1, [(2, 1)])]

private def td2Atoms : Array (Option Atom) :=
  #[none,
    some (.root ⟨.lt, 0, 1, tdP2⟩),          -- 1: ρ 0 < root₁(tdP2) < 0
    some (.ineq ⟨.eq, [(tnA, false)]⟩),      -- 2: A = x1  (= 0 at the sample)
    some (.ineq ⟨.lt, [(tnX2, false)]⟩),     -- 3: lc = x2  (< 0, ensure_sign)
    some (.ineq ⟨.gt, [(tgX0, false)]⟩)]     -- 4: ρ 0 > 0

private def td2Steps : Array TraceStep :=
  #[.cellBound .upper .lt 0 1 tdP2, .linearRoot .lt 0 tdQ2 true (some (tnX2, -1))]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ td2Atoms)
      (arithClause [] [⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩, ⟨4, true⟩]) := by
  nlsat_arith_valid_steps td2Steps

/- The lc sign literal is load-bearing: without it the clause lane
finds no `hlc` evidence, the step skips, and the clause rejects
(sound). -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ td2Atoms)
      (arithClause [] [⟨1, true⟩, ⟨2, true⟩, ⟨4, true⟩]) := by
  nlsat_arith_valid_steps td2Steps

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

/-- The nonstrict Thom cells (kind coverage for the Thom production):
`p = x0²−2` with BOTH bounds on the greater root. `ge 2` formula is
conjunctive (`0 ≤ pv ∧ 0 ≤ pdv` ⟹ `2·y ≥ 0`), `le 2` is disjunctive
(`pv ≤ 0 ∨ (0 ≤ pv ∧ pdv ≤ 0)` — exactly the split-fuel cell verified
against `Semantics.thomFormula`): the `pv ≤ 0` branch dies against
`0 ≤ pv` + the `p < 0` literal, the `pdv ≤ 0` branch (`2y ≤ 0`)
dies against the `y > 0` literal. -/
private def tqAtoms : Array (Option Atom) :=
  #[none,
    some (.root ⟨.ge, 0, 2, tsPm2⟩),         -- 1: ρ 0 ≥ root₂(p)
    some (.root ⟨.le, 0, 2, tsPm2⟩),         -- 2: ρ 0 ≤ root₂(p)
    some (.ineq ⟨.lt, [(tsPm2, false)]⟩),    -- 3: p < 0
    some (.ineq ⟨.gt, [(tgX0, false)]⟩)]     -- 4: 0 < ρ 0

private def tqSteps : Array TraceStep :=
  #[.cellBound .lower .ge 0 2 tsPm2, .thomQuadratic .ge 0 2 tsPm2 1 1 1 0,
    .cellBound .upper .le 0 2 tsPm2, .thomQuadratic .le 0 2 tsPm2 1 1 1 0]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ tqAtoms)
      (arithClause [] [⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩, ⟨4, true⟩]) := by
  nlsat_arith_valid_steps tqSteps

/-! ## G11 — the o139 production lanes (rootGeneric deg-1 non-const-lc)

Fixtures from the ordering_139 refutation's walk (the WalkTests o139
snapshot, post-writeback-fix): cid 7 is the FIRST live case of the
production `rootGeneric` lane at deg 1 with a non-const lead (the
census's "production-unreachable" claim falsified); cid 9 is the
negative-side sibling — a positive-in-clause root literal (`negRoot`
fact, `¬ Holds`) converted semantically by `negRootDeg1Produce` into
the `(A = 0) ∨ ¬rootCmp` disjunction, no step consumed. -/

/-- The o139 atom table (transitivity-of-fractions, internal order). -/
private def g11Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.gt, [([((-1), [(0, 1), (4, 1)]), (1, [(1, 1), (3, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([((-1), [(1, 1), (5, 1)]), (1, [(2, 1), (4, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(0, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(1, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(2, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([((-1), [(0, 1), (5, 1)]), (1, [(2, 1), (3, 1)])], false)]⟩),
   some (.root ⟨.gt, 4, 1, [(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])], false)]⟩)]

/-- cid 7's pre-arith steps (bundle 7 of the o139 trace). -/
private def g11Cid7Steps : Array TraceStep :=
  #[.factorSplit [((-1), [(1, 1)])] #[[((-1), [(1, 1)])]] #[],
    .factorSplit [((-1), [(0, 1)])] #[[((-1), [(0, 1)])]] #[],
    .factorSplit [(1, [(0, 1), (2, 1), (4, 1)]), ((-1), [(1, 1), (2, 1), (3, 1)])]
      #[[(1, [(2, 1)])], [(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])]] #[],
    .rootGeneric .gt 4 1 [(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])],
    .cellBound .lower .gt 4 1 [(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])],
    .factorSplit [(1, [(0, 1)])] #[[(1, [(0, 1)])]] #[],
    .linearRoot .gt 2 [(1, [(2, 1)])] false none,
    .cellBound .lower .gt 2 1 [(1, [(2, 1)])],
    .linearRoot .gt 1 [((-1), [(1, 1)])] true none,
    .cellBound .lower .gt 1 1 [((-1), [(1, 1)])],
    .linearRoot .gt 0 [((-1), [(0, 1)])] true none,
    .cellBound .lower .gt 0 1 [((-1), [(0, 1)])]]

/-- cid 7's arith member — the `rootGeneric .gt 4 1` step's cross-link
through `linearRootNonconstPos_discharge` carries the close (the lead
`A = x0`'s sign fact comes from the clause's own `⟨3, true⟩`). -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ g11Atoms)
      (arithClause [] [⟨7, true⟩, ⟨5, true⟩, ⟨4, true⟩, ⟨3, true⟩,
        ⟨2, false⟩, ⟨6, true⟩]) := by
  nlsat_arith_valid_steps g11Cid7Steps

/- Load-bearing: dropping the steps leaves the rootPair fact opaque
(`rootVal` comparisons the glue can't use) — the discharge fails. -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ g11Atoms)
      (arithClause [] [⟨7, true⟩, ⟨5, true⟩, ⟨4, true⟩, ⟨3, true⟩,
        ⟨2, false⟩, ⟨6, true⟩]) := by
  nlsat_arith_valid_steps #[]

/-- cid 8's pre-arith steps (bundle 8 of the o139 trace). -/
private def g11Cid8Steps : Array TraceStep :=
  #[.factorSplit [((-1), [(1, 1)])] #[[((-1), [(1, 1)])]] #[],
    .factorSplit [((-1), [(0, 1)])] #[[((-1), [(0, 1)])]] #[],
    .factorSplit [(1, [(0, 1), (2, 1), (4, 1)]), ((-1), [(1, 1), (2, 1), (3, 1)])]
      #[[(1, [(2, 1)])], [(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])]]
      #[[(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])]],
    .linearRoot .gt 1 [((-1), [(1, 1)])] true none,
    .cellBound .lower .gt 1 1 [((-1), [(1, 1)])],
    .linearRoot .gt 0 [((-1), [(0, 1)])] true none,
    .cellBound .lower .gt 0 1 [((-1), [(0, 1)])]]

/-- cid 8's arith member — the eq × bare-var lift's home: the `eq` fact
`x0·x4 − x1·x3 = 0` must be multiplied through free variables for the
contradiction (nlinarith can't). No root literals, so the steps are
inert here (step-free also closes — pinned as documentation). -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ g11Atoms)
      (arithClause [] [⟨8, true⟩, ⟨4, true⟩, ⟨3, true⟩, ⟨2, false⟩,
        ⟨6, true⟩]) := by
  nlsat_arith_valid_steps g11Cid8Steps

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ g11Atoms)
      (arithClause [] [⟨8, true⟩, ⟨4, true⟩, ⟨3, true⟩, ⟨2, false⟩,
        ⟨6, true⟩]) := by
  nlsat_arith_valid_steps #[]

/-- cid 9's arith member — the negRoot lane: `⟨7, false⟩` extracts
`¬ Holds` for the deg-1 root atom on `p = x0·x4 − x1·x3` (lead `A = x0`,
non-const); `negRootDeg1Produce` converts it to
`(evalP ρ x0 = 0) ∨ ¬rootCmp .gt (evalP ρ p) 0` — the `A = 0` branch
dies on the clause's `x0 > 0` sign fact, the comparison branch
contradicts the other literals' `x1·x3 − x0·x4 < 0` (from `≤ 0` + `≠ 0`).
Step-independent (semantic conversion), so step-free also closes. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ g11Atoms)
      (arithClause [] [⟨3, true⟩, ⟨1, false⟩, ⟨8, false⟩, ⟨7, false⟩]) := by
  nlsat_arith_valid_steps g11Cid8Steps

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ g11Atoms)
      (arithClause [] [⟨3, true⟩, ⟨1, false⟩, ⟨8, false⟩, ⟨7, false⟩]) := by
  nlsat_arith_valid_steps #[]

/- Load-bearing: dropping the root literal leaves a SATISFIABLE ineq
core (`x0 = 1`, `x1·x3 − x0·x4 = −1`) — the negRoot lane's conversion
is what carries the close, so the discharge must fail. -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ g11Atoms)
      (arithClause [] [⟨3, true⟩, ⟨1, false⟩, ⟨8, false⟩]) := by
  nlsat_arith_valid_steps #[]

/-! ### G11 close-out review (F-i/F-ii) — the sign-fact-free corners

z3 emits the deg-1 non-const-lc root atom with NO lc guard
(`add_root_literal` falls through both `mk_linear_root`'s const check
and `mk_quadratic_root`, then adds the bare atom,
nlsat_explain.cpp:725-737), so the lead's sign is not structurally
present in the clause. The next three pins cover the corners that
inspection found under-covered: the positive side with a clause
`A = 0` fact (F-i: the diseq is materialized as the findOr-consumable
trichotomy), and both sides with NO sign fact at all (F-ii: the
negative side's `negHolds_deg1_trichotomy`; the positive side's
pre-existing `linearRootNonconst_disjunction`, previously unpinned). -/

/-- `pZ = x1·x0 + 1` (root in var 0: `−1/x1`, non-const lead `A = x1`). -/
private def g11zP : MPoly := [(1, [(0, 1), (1, 1)]), (1, [])]
private def g11zA : MPoly := [(1, [(1, 1)])]                -- the lead x1
private def g11zX0 : MPoly := [(1, [(0, 1)])]               -- x0
private def g11zX0p1 : MPoly := [(1, [(0, 1)]), (1, [])]    -- x0 + 1
private def g11zX1m1 : MPoly := [(1, [(1, 1)]), (-1, [])]   -- x1 − 1
private def g11zPm1 : MPoly := [(1, [(0, 1), (1, 1)]), ((-1), [])]  -- x1·x0 − 1

/-- F-i: positive root literal (deg-1 non-const lead) + a clause
`A = 0` fact. Holds forces `1 ≤ rootCount`, hence `A ≠ 0` — the lane
notes the concrete-spelled `< 0 ∨ > 0` trichotomy and both branches
die on the `A = 0` fact. -/
private def g11zAtoms : Array (Option Atom) :=
  #[none,
    some (.root ⟨.gt, 0, 1, g11zPm1⟩),          -- 1: ρ 0 > root₁(x1·x0 − 1)
    some (.ineq ⟨.eq, [(g11zA, false)]⟩)]                          -- 2: x1 = 0

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ g11zAtoms) (arithClause [] [⟨1, true⟩, ⟨2, true⟩]) := by
  nlsat_arith_valid_steps #[.rootGeneric .gt 0 1 g11zPm1]

/-- F-ii (negative side): the negRoot literal with NO clause sign fact
for the lead. All-fail gives `¬Holds ∧ x0 > 0 ∧ x1 > 1`; the
`negHolds_deg1_trichotomy` fallback splits
`A = 0 ∨ (0 < A ∧ ¬rootCmp (evalP p) 0) ∨ (A < 0 ∧ …)`: the `A = 0`
and `A < 0` leaves die on `x1 > 1`, the `0 < A` leaf's converted
`¬(x1·x0 + 1 > 0)` dies on the product bound (`x0 > 0 ∧ x1 > 1 ⟹
x1·x0 + 1 > 1`). Pre-F-ii the opaque fallback rejected this. -/
private def g11tAtoms : Array (Option Atom) :=
  #[none,
    some (.root ⟨.gt, 0, 1, g11zP⟩),            -- 1: ρ 0 > root₁(x1·x0 + 1)
    some (.ineq ⟨.gt, [(g11zX0, false)]⟩),      -- 2: x0 > 0
    some (.ineq ⟨.gt, [(g11zX1m1, false)]⟩)]    -- 3: x1 − 1 > 0

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ g11tAtoms)
      (arithClause [] [⟨1, false⟩, ⟨2, true⟩, ⟨3, true⟩]) := by
  nlsat_arith_valid_steps #[]

/-- The positive-side sibling (the `linearRootNonconst_disjunction`
two-sign fallback, previously unpinned): all-fail gives
`Holds ∧ x0 < −1 ∧ x1 > 1`; the `0 < A` disjunct's converted
`x1·x0 + 1 > 0` dies on the product bound (`x0 < −1 ∧ x1 > 1 ⟹
x1·x0 + 1 < 0`), the `A < 0` disjunct on `x1 > 1`. -/
private def g11uAtoms : Array (Option Atom) :=
  #[none,
    some (.root ⟨.gt, 0, 1, g11zP⟩),            -- 1: ρ 0 > root₁(x1·x0 + 1)
    some (.ineq ⟨.lt, [(g11zX0p1, false)]⟩),    -- 2: x0 + 1 < 0
    some (.ineq ⟨.gt, [(g11zX1m1, false)]⟩)]    -- 3: x1 − 1 > 0

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ g11uAtoms)
      (arithClause [] [⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩]) := by
  nlsat_arith_valid_steps #[.rootGeneric .gt 0 1 g11zP]

/-! ## 19b Slice 1 — pseudoDivision grammar + identity + sign transfer

The pd1/pd6 payloads come from the Slice-0 live census (BOARD): pd1
`(x1, x1−x0², 1, 1, x0², 1, false)` — const lc, d odd, no flip; pd6
`(2x1²−1, x0x1−1, 1, 2, 2−x0², −1, false)` — non-const lc, d even, no
flip. The identity is re-proved per-instance (decision 1); the
grammar is structural-only. -/

private def pd1F : MPoly := [(1, [(1, 1)])]                          -- x1
private def pd1Eq : MPoly := [(1, [(1, 1)]), ((-1), [(0, 2)])]       -- x1 − x0²
private def pd1R : MPoly := [(1, [(0, 2)])]                          -- x0²
private def pd1Rbad : MPoly := [(1, [(0, 2)]), (1, [])]              -- x0² + 1
private def pd6F : MPoly := [(2, [(1, 2)]), ((-1), [])]              -- 2x1² − 1
private def pd6Eq : MPoly := [(1, [(0, 1), (1, 1)]), ((-1), [])]     -- x0·x1 − 1
private def pd6R : MPoly := [(2, []), ((-1), [(0, 2)])]              -- 2 − x0²
private def pd6Q : MPoly := [(2, [(0, 1), (1, 1)]), (2, [])]         -- 2x0·x1 + 2

-- grammar: genuine payloads pass; corruptions reject (native eval,
-- the precheck's own evaluation grade)
#guard grammarOK (.pseudoDivision pd1F pd1Eq 1 1 pd1R 1 false) == true
#guard grammarOK (.pseudoDivision pd6F pd6Eq 1 2 pd6R (-1) false) == true
-- lcSign outside {−1, 0, 1}
#guard grammarOK (.pseudoDivision pd1F pd1Eq 1 1 pd1R 2 false) == false
-- const lc = 1 but lcSign = −1 (sign agreement violated)
#guard grammarOK (.pseudoDivision pd1F pd1Eq 1 1 pd1R (-1) false) == false
-- r = eq: the degree did not drop
#guard grammarOK (.pseudoDivision pd1F pd1Eq 1 1 pd1Eq 1 false) == false
-- non-const lc: any in-range lcSign passes (untrusted hint)
#guard grammarOK (.pseudoDivision pd6F pd6Eq 1 2 pd6R 0 false) == true
-- r = [] (the path-(b) const-zero remainder, pd2/pd4's family): pass
#guard grammarOK (.pseudoDivision pd1F pd1Eq 1 1 [] 1 false) == true

/-- The per-instance identity close (the Slice-2 consumption idiom):
pd1's genuine payload, pd6's non-const-lc one, the decision-1
perturbation witness (d = 2 with lc = 1 — the same identity), and a
corrupt remainder that must throw. -/
example : ∀ ρ : Nat → ℝ, True := by
  run_tac unsafe (do
    let (ρFv, m1) ← (← Lean.Elab.Tactic.getMainGoal).intro `ρ
    m1.withContext do
      let ρE := Lean.mkFVar ρFv
      -- probe: closeAlgRefl on a FALSE equation must throw (the
      -- hole-in-term regression — ring's failed close left an
      -- unassigned sub-mvar behind an assigned normalization chain)
      let one ← Lean.Meta.mkAppM ``Check.evalP #[ρE, Lean.toExpr ([(1, [])] : MPoly)]
      let tgt ← Lean.Meta.mkAppM ``Eq #[one, ← Lean.Meta.mkAppM ``HAdd.hAdd #[one, one]]
      let mut thrown := false
      try
        let _ ← Refute.closeAlgRefl tgt
      catch _ => thrown := true
      unless thrown do throwError "closeAlgRefl accepted a FALSE equation"
      -- pd1: 1·x1 = 1·(x1−x0²) + x0²
      let (lc1, _) ← Refute.pseudoDivisionIdentity ρE pd1F pd1Eq 1 1 pd1R
      unless lc1 == [(1, [])] do throwError "pd1 lc mismatch: {repr lc1}"
      -- pd6: x0²·(2x1²−1) = (2x0x1+2)·(x0x1−1) + (2−x0²)
      let (lc6, _) ← Refute.pseudoDivisionIdentity ρE pd6F pd6Eq 1 2 pd6R
      unless lc6 == [(1, [(0, 1)])] do throwError "pd6 lc mismatch: {repr lc6}"
      -- decision-1 perturbation: (d+1, lc·Q, lc·r) — pd1 with d = 2
      -- (lc = 1, so Q/r are unchanged) witnesses the same identity
      let _ ← Refute.pseudoDivisionIdentity ρE pd1F pd1Eq 1 2 pd1R
      -- corrupt remainder: x0² + 1 falsifies the identity — must throw
      let mut accepted := false
      try
        let _ ← Refute.pseudoDivisionIdentity ρE pd1F pd1Eq 1 1 pd1Rbad
        accepted := true
      catch _ => pure ()
      if accepted then throwError "corrupt remainder accepted"
    Lean.Elab.Tactic.replaceMainGoal [m1])
  trivial

/-- The sign-transfer lemmas fire on the Slice-2 instantiation shapes:
pd1 (d odd, lc = 1 > 0 — no flip) and pd6 (d even, non-const lc — no
flip). The identities are closed by the same simp+ring idiom
`pseudoDivisionIdentity` wraps. -/
example (ρ : Nat → ℝ) (hE : evalP ρ pd1Eq = (0 : ℝ)) :
    0 < evalP ρ pd1F ↔ 0 < evalP ρ pd1R := by
  have hId : (evalP ρ [(1, [])]) ^ (2 * 0 + 1) * evalP ρ pd1F =
      evalP ρ [(1, [])] * evalP ρ pd1Eq + evalP ρ pd1R := by
    simp only [pd1F, pd1Eq, pd1R, evalP, evalM, evalP_add, evalP_mul,
      evalP_neg, evalP_smulTerm, evalP_ofInt, evalP_ofVar, Int.cast_one,
      Int.cast_ofNat, one_mul, mul_one, add_zero, zero_add]
    ring
  exact pdSign_odd_pos_gt (m := 0) (by
    simp only [evalP, evalM, evalP_smulTerm, evalP_ofInt]; norm_num) hE hId

example (ρ : Nat → ℝ) (hL : evalP ρ [(1, [(0, 1)])] ≠ (0 : ℝ))
    (hE : evalP ρ pd6Eq = (0 : ℝ)) :
    evalP ρ pd6F < 0 ↔ evalP ρ pd6R < 0 := by
  have hId : (evalP ρ [(1, [(0, 1)])]) ^ (2 * 1) * evalP ρ pd6F =
      evalP ρ pd6Q * evalP ρ pd6Eq + evalP ρ pd6R := by
    simp only [pd6F, pd6Eq, pd6R, pd6Q, evalP, evalM, evalP_add, evalP_mul,
      evalP_neg, evalP_smulTerm, evalP_ofInt, evalP_ofVar, Int.cast_one,
      Int.cast_ofNat, one_mul, mul_one, add_zero, zero_add]
    ring
  exact pdSign_even_lt (m := 1) hL hE hId

/-- The flip case (pd4's rule, d odd ∧ lc < 0): pd4's own payload
`(x1, x0x1−1, 1, 1, const 1, −1, false)` — the const-remainder fold;
the comparison flips. -/
example (ρ : Nat → ℝ) (hL : evalP ρ [(1, [(0, 1)])] < (0 : ℝ))
    (hE : evalP ρ pd6Eq = (0 : ℝ)) :
    0 < evalP ρ [(1, [(1, 1)])] ↔ evalP ρ [(1, [])] < 0 := by
  have hId : (evalP ρ [(1, [(0, 1)])]) ^ (2 * 0 + 1) * evalP ρ [(1, [(1, 1)])] =
      evalP ρ [(1, [])] * evalP ρ pd6Eq + evalP ρ [(1, [])] := by
    simp only [pd6Eq, evalP, evalM, evalP_add, evalP_mul, evalP_neg,
      evalP_smulTerm, evalP_ofInt, evalP_ofVar, Int.cast_one, Int.cast_ofNat,
      one_mul, mul_one, add_zero, zero_add]
    ring
  exact pdSign_odd_neg_gt (m := 0) hL hE hId

/-! ## 19b Slice 2 — pseudoDivision consumption (`pdRewriteLane`)

The atoms/clauses/steps below are the REAL Slice-0 driver dumps
(2026-08-13, `scratch_dump.lean` pd1/pd2/pd3/pd4/pd6). During
development the lane was instrumented (temporary `logInfo`, reverted)
to confirm: the transport FIRES on the rebuilt literals of pd1/pd3/pd6
(with the lc evidence found from the clause's own A4/A5 literals —
R-h's `⟨6,false⟩` unnegated-EQ convention for the pd6 diseq), the drop
lane notes the definite signs on pd2/pd4, and the corruption probes
skip soundly.

**Glue-subsumption finding:** every Slice-0 driver's arith member also
closes STEP-FREE (the F2 glue — nlinarith with the eq×var lift,
ineq×ineq pairing, and `sq_nonneg` hints — subsumes the transport on
these small cores). The with-steps examples pin the lane's
construction; the step-free variants pin the subsumption (guards fail
loudly if either side regresses). -/

-- pd1: const lc, d odd, no flip; rebuilt `lt [x0²]` in proj as ⟨3,false⟩
private def s2pd1Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.eq, [([(1, [(1, 1)]), ((-1), [(0, 2)])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(1, 1)])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 2)])], false)]⟩)]
private def s2pd1F : MPoly := [(1, [(1, 1)])]
private def s2pd1Eq : MPoly := [(1, [(1, 1)]), ((-1), [(0, 2)])]
private def s2pd1R : MPoly := [(1, [(0, 2)])]
private def s2pd1Fbad : MPoly := [(1, [(1, 1)]), (1, [])]
private def s2pd1R4 : MPoly := [(1, [(0, 4)])]
private def s2pd1Steps : Array TraceStep :=
  #[.resolution (.clause 2), .pseudoDivision s2pd1F s2pd1Eq 1 1 s2pd1R 1 false]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd1Atoms)
      (arithClause [⟨1, false⟩, ⟨2, false⟩] [⟨3, false⟩]) := by
  nlsat_arith_valid_steps s2pd1Steps

-- step-free: the glue subsumes (sq_nonneg + eq substitution)
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd1Atoms)
      (arithClause [⟨1, false⟩, ⟨2, false⟩] [⟨3, false⟩]) := by
  nlsat_arith_valid_steps #[]

-- corrupt f: the identity close throws (the closeAlgRefl hole-guard +
-- the withoutModifyingState rollback) — the step is skipped soundly
-- and the clause still closes (glue)
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd1Atoms)
      (arithClause [⟨1, false⟩, ⟨2, false⟩] [⟨3, false⟩]) := by
  nlsat_arith_valid_steps #[.pseudoDivision s2pd1Fbad s2pd1Eq 1 1 s2pd1R 1 false]

-- path-(c) tolerance: the extra step (d = 2, r = x0⁴ — matches no
-- clause factor; its identity is also false) contributes nothing
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd1Atoms)
      (arithClause [⟨1, false⟩, ⟨2, false⟩] [⟨3, false⟩]) := by
  nlsat_arith_valid_steps
    #[.pseudoDivision s2pd1F s2pd1Eq 1 1 s2pd1R 1 false,
      .pseudoDivision s2pd1F s2pd1Eq 1 2 s2pd1R4 1 false]

-- an INVALID clause carrying the genuine step must reject even with
-- the transport's facts (F-w negative probe)
#guard_msgs (drop error) in
/- -/ example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd1Atoms)
      (arithClause [⟨1, false⟩] [⟨3, false⟩]) := by
  nlsat_arith_valid_steps s2pd1Steps

-- pd3: REORDER live (internal variable order), the lc is a SQUARE
-- (v0²), the A4-GT literal carries its sign, and the rewrite target is
-- the x0-BOUND literal (R-c), not the "main" ineq
private def s2pd3Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.lt, [([(1, [(1, 1)])], false)]⟩),
   some (.ineq ⟨.lt, [([((-2), [(1, 1)]), (1, [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 2), (1, 1)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 2)]), (1, [(0, 1)])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 2)]), ((-2), [])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(0, 2)])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 1)])], false)]⟩)]
private def s2pd3F : MPoly := [((-2), [(1, 1)]), (1, [])]
private def s2pd3Eq : MPoly := [(1, [(0, 2), (1, 1)]), ((-1), [])]
private def s2pd3R : MPoly := [(1, [(0, 2)]), ((-2), [])]
private def s2pd3Steps : Array TraceStep :=
  #[.resolution (.clause 3),
    .pseudoDivision s2pd3F s2pd3Eq 1 1 s2pd3R 1 false,
    .factorSplit [(1, [(0, 2)])] #[[(1, [(0, 1)])]] #[],
    .linearRoot .lt 0 [(1, [(0, 1)])] false none,
    .cellBound .upper .lt 0 1 [(1, [(0, 1)])]]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd3Atoms)
      (arithClause [⟨3, false⟩, ⟨2, true⟩] [⟨5, true⟩, ⟨6, true⟩, ⟨7, true⟩]) := by
  nlsat_arith_valid_steps s2pd3Steps

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd3Atoms)
      (arithClause [⟨3, false⟩, ⟨2, true⟩] [⟨5, true⟩, ⟨6, true⟩, ⟨7, true⟩]) := by
  nlsat_arith_valid_steps #[]

-- pd6: d even + non-const lc + the A5 DISEQ assumption (R-h: enters
-- proj as ⟨6,false⟩, the EQ atom unnegated — the lane's `lc ≠ 0`
-- evidence comes from its extraction)
private def s2pd6Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.gt, [([(1, [(0, 1)]), (1, [])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(0, 2)]), ((-2), [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1), (1, 1)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.lt, [([(2, [(1, 2)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.lt, [([((-1), [(0, 2)]), (2, [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1)])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 1)])], false)]⟩),
   some (.ineq ⟨.gt, []⟩)]
private def s2pd6F : MPoly := [(2, [(1, 2)]), ((-1), [])]
private def s2pd6Eq : MPoly := [(1, [(0, 1), (1, 1)]), ((-1), [])]
private def s2pd6R : MPoly := [((-1), [(0, 2)]), (2, [])]
private def s2pd6Steps : Array TraceStep :=
  #[.resolution (.clause 4),
    .pseudoDivision s2pd6F s2pd6Eq 1 2 s2pd6R (-1) false,
    .factorSplit [(1, [(0, 1)])] #[[(1, [(0, 1)])]] #[],
    .linearRoot .lt 0 [(1, [(0, 1)])] false none,
    .cellBound .upper .lt 0 1 [(1, [(0, 1)])]]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd6Atoms)
      (arithClause [⟨4, false⟩, ⟨3, false⟩] [⟨5, false⟩, ⟨6, false⟩, ⟨7, true⟩]) := by
  nlsat_arith_valid_steps s2pd6Steps

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd6Atoms)
      (arithClause [⟨4, false⟩, ⟨3, false⟩] [⟨5, false⟩, ⟨6, false⟩, ⟨7, true⟩]) := by
  nlsat_arith_valid_steps #[]

-- decision-1: the lcSign payload is an untrusted HINT — flipping it
-- (−1 → 1) changes nothing (d is even; the evidence is the A5 diseq)
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd6Atoms)
      (arithClause [⟨4, false⟩, ⟨3, false⟩] [⟨5, false⟩, ⟨6, false⟩, ⟨7, true⟩]) := by
  nlsat_arith_valid_steps #[.pseudoDivision s2pd6F s2pd6Eq 1 2 s2pd6R 1 false]

private def s2pd6StepsEven : Array TraceStep :=
  #[.pseudoDivision s2pd6F s2pd6Eq 1 2 s2pd6R (-1) true]

-- the isEven payload is likewise a hint — the marks come from the
-- CLAUSE ATOM's factor list, never from the payload
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd6Atoms)
      (arithClause [⟨4, false⟩, ⟨3, false⟩] [⟨5, false⟩, ⟨6, false⟩, ⟨7, true⟩]) := by
  nlsat_arith_valid_steps s2pd6StepsEven

-- R-h polarity: with the diseq literal's polarity flipped (⟨6,true⟩ —
-- asserting x0 = 0), the lc evidence is gone and the transport is
-- inert; the (valid) clause still closes through the glue
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd6Atoms)
      (arithClause [⟨4, false⟩, ⟨3, false⟩] [⟨5, false⟩, ⟨6, true⟩]) := by
  nlsat_arith_valid_steps s2pd6Steps

-- pd2: const-nonzero remainder (the DROP lane), A4-GT lc — the lane
-- notes `0 < x1` from the eq + lc-sign + r = 1
private def s2pd2Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.lt, [([(1, [(0, 1)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1), (1, 1)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(1, 1)])], false)]⟩),
   some (.ineq ⟨.lt, []⟩),
   some (.ineq ⟨.gt, [([(1, [(0, 1)])], false)]⟩)]
private def s2pd2Steps : Array TraceStep :=
  #[.resolution (.clause 3),
    .pseudoDivision s2pd1F s2pd6Eq 1 1 [(1, [])] 1 false]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd2Atoms)
      (arithClause [⟨2, false⟩, ⟨3, false⟩] [⟨5, true⟩]) := by
  nlsat_arith_valid_steps s2pd2Steps

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd2Atoms)
      (arithClause [⟨2, false⟩, ⟨3, false⟩] [⟨5, true⟩]) := by
  nlsat_arith_valid_steps #[]

-- pd4: const remainder with lcSign −1 (A4-LT): the flipped family —
-- the lane notes `x1 < 0`
private def s2pd4Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.gt, [([(1, [(0, 1)]), (1, [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1), (1, 1)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(1, 1)])], false)]⟩),
   some (.ineq ⟨.lt, []⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 1)])], false)]⟩)]
private def s2pd4Steps : Array TraceStep :=
  #[.resolution (.clause 3),
    .pseudoDivision s2pd1F s2pd6Eq 1 1 [(1, [])] (-1) false]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd4Atoms)
      (arithClause [⟨3, false⟩, ⟨2, false⟩] [⟨5, true⟩]) := by
  nlsat_arith_valid_steps s2pd4Steps

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2pd4Atoms)
      (arithClause [⟨3, false⟩, ⟨2, false⟩] [⟨5, true⟩]) := by
  nlsat_arith_valid_steps #[]

-- ZeroRel (eq-kind rebuilt literal, synthetic): f = x1²−2,
-- eq = x1−x0², d = 2, r = x0⁴−2; z3 adds only `add_lc_diseq` for EQ
-- (:1181-1184) — the ZeroRel transport needs just the zero-status
private def s2zrAtoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.eq, [([(1, [(1, 1)]), ((-1), [(0, 2)])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(1, 2)]), ((-2), [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 4)]), ((-2), [])], false)]⟩)]
private def s2zrF : MPoly := [(1, [(1, 2)]), ((-2), [])]
private def s2zrR : MPoly := [(1, [(0, 4)]), ((-2), [])]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2zrAtoms)
      (arithClause [⟨1, false⟩, ⟨2, false⟩] [⟨3, false⟩]) := by
  nlsat_arith_valid_steps #[.pseudoDivision s2zrF s2pd1Eq 1 2 s2zrR 1 false]

-- kind-flip + d = 3 (synthetic): f = x1⁴+x1³, eq = x0x1²−1 (lc x0 < 0
-- via the A4-LT literal), r = x0²x1+x0; σ = −1 ⟹ the original kind is
-- flip(lt) = gt
private def s2kfAtoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.eq, [([(1, [(0, 1), (1, 2)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(1, 4)]), (1, [(1, 3)])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 2), (1, 1)]), (1, [(0, 1)])], false)]⟩)]
private def s2kfF : MPoly := [(1, [(1, 4)]), (1, [(1, 3)])]
private def s2kfEq : MPoly := [(1, [(0, 1), (1, 2)]), ((-1), [])]
private def s2kfR : MPoly := [(1, [(0, 2), (1, 1)]), (1, [(0, 1)])]
private def s2kfSteps : Array TraceStep :=
  #[.pseudoDivision s2kfF s2kfEq 1 3 s2kfR (-1) false]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2kfAtoms)
      (arithClause [⟨1, false⟩, ⟨3, false⟩] [⟨4, false⟩, ⟨2, true⟩]) := by
  nlsat_arith_valid_steps s2kfSteps

-- consEven (synthetic): the rebuilt atom lt [(x0, false), (x0⁴+1, true)]
-- carries an even-marked replaced factor — zero-status only, no sign
-- relation (:1133 sign absorption)
private def s2evAtoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.eq, [([(1, [(1, 1)]), ((-1), [(0, 2)])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 1)])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 1)])], false), ([(1, [(0, 4)]), (1, [])], true)]⟩)]
private def s2evF : MPoly := [(1, [(1, 2)]), (1, [])]
private def s2evR : MPoly := [(1, [(0, 4)]), (1, [])]

example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ s2evAtoms)
      (arithClause [⟨1, false⟩, ⟨2, false⟩] [⟨3, false⟩]) := by
  nlsat_arith_valid_steps #[.pseudoDivision s2evF s2pd1Eq 1 2 s2evR 1 false]

end LeanNonlinearArith.Nlsat.Tests.Refute

