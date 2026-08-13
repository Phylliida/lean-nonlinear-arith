import LeanNonlinearArith.Nlsat.Refute
import LeanNonlinearArith.Nlsat.Solver
import LeanNonlinearArith.Nlsat.Explain

/-! Scratch: dump solver refutations as paste-ready Lean literal defs
(for WalkTests pin data). NOT part of the library build. -/

open LeanNonlinearArith.Nlsat

namespace DumpPP

def ppInt (i : Int) : String := if i < 0 then s!"({i})" else s!"{i}"

def ppBool (b : Bool) : String := if b then "true" else "false"

def ppMonomial (m : Monomial) : String :=
  "[" ++ String.intercalate ", " (m.map fun (v, e) => s!"({v}, {e})") ++ "]"

def ppMPoly (p : MPoly) : String :=
  "[" ++ String.intercalate ", " (p.map fun (c, m) => s!"({ppInt c}, {ppMonomial m})") ++ "]"

def ppMPolyArr (a : Array MPoly) : String :=
  "#[" ++ String.intercalate ", " (a.toList.map ppMPoly) ++ "]"

def ppLit (l : Literal) : String := s!"⟨{l.bvar}, {ppBool l.neg}⟩"

def ppLitArr (a : Array Literal) : String :=
  "#[" ++ String.intercalate ", " (a.toList.map ppLit) ++ "]"

def ppIneqKind : IneqKind → String
  | .eq => ".eq" | .lt => ".lt" | .gt => ".gt"

def ppRootKind : RootKind → String
  | .eq => ".eq" | .lt => ".lt" | .gt => ".gt" | .le => ".le" | .ge => ".ge"

def ppCellSide : CellSide → String
  | .exact => ".exact" | .lower => ".lower" | .upper => ".upper"

def ppAtom : Atom → String
  | .ineq a =>
    let fs := String.intercalate ", " (a.factors.map fun (p, ev) =>
      s!"({ppMPoly p}, {ppBool ev})")
    s!".ineq ⟨{ppIneqKind a.kind}, [{fs}]⟩"
  | .root a =>
    s!".root ⟨{ppRootKind a.kind}, {a.x}, {a.i}, {ppMPoly a.p}⟩"

def ppAtoms (a : Array (Option Atom)) : String :=
  "#[" ++ String.intercalate ",\n   " (a.toList.map fun
    | none => "none"
    | some a => s!"some ({ppAtom a})") ++ "]"

def ppAnt : ResolutionAntecedent → String
  | .clause cid => s!".clause {cid}"
  | .arith core proj =>
    s!".arith {ppLitArr core} {ppLitArr proj}"
  | .decision l => s!".decision {ppLit l}"

def ppStep : TraceStep → String
  | .leafNumeric x => s!".leafNumeric {x}"
  | .linearRoot k y p mkNeg lcFact =>
    let lc := match lcFact with
      | none => "none"
      | some (c, s) => s!"some ({ppMPoly c}, {ppInt s})"
    s!".linearRoot {ppRootKind k} {y} {ppMPoly p} {ppBool mkNeg} {lc}"
  | .thomQuadratic k y i p sq sa spd sp =>
    s!".thomQuadratic {ppRootKind k} {y} {i} {ppMPoly p} {ppInt sq} {ppInt sa} {ppInt spd} {ppInt sp}"
  | .rootGeneric k y i p =>
    s!".rootGeneric {ppRootKind k} {y} {i} {ppMPoly p}"
  | .cellBound side k y i p =>
    s!".cellBound {ppCellSide side} {ppRootKind k} {y} {i} {ppMPoly p}"
  | .pseudoDivision f eq x d r lcSign isEven =>
    s!".pseudoDivision {ppMPoly f} {ppMPoly eq} {x} {d} {ppMPoly r} {ppInt lcSign} {ppBool isEven}"
  | .factorSplit p fs vanished =>
    s!".factorSplit {ppMPoly p} {ppMPolyArr fs} {ppMPolyArr vanished}"
  | .intBranch x lo => s!".intBranch {x} {ppInt lo}"
  | .resolution ant => s!".resolution ({ppAnt ant})"

def ppSteps (a : Array TraceStep) : String :=
  "#[" ++ String.intercalate ",\n      " (a.toList.map ppStep) ++ "]"

def ppBundle (b : TraceBundle) : String :=
  s!"some ⟨{ppSteps b.steps}, {ppLitArr b.lemma}⟩"

def ppBundleFinal (b : TraceBundle) : String :=
  s!"⟨{ppSteps b.steps}, {ppLitArr b.lemma}⟩"

def ppClauses (a : Array Clause) : String :=
  "#[" ++ String.intercalate ",\n   " (a.toList.map fun c =>
    s!"\{ lits := {ppLitArr c.lits}, learned := {ppBool c.learned}, deleted := {ppBool c.deleted} }") ++ "]"

def ppBundles (a : Array (Option TraceBundle)) : String :=
  "#[" ++ String.intercalate ",\n   " (a.toList.map fun
    | none => "none"
    | some b => ppBundle b) ++ "]"

end DumpPP

namespace DumpDriver

def x0 : MPoly := [(1, [(0, 1)])]
def x1 : MPoly := [(1, [(1, 1)])]
def pSum : MPoly := [(1, [(1, 2)]), (1, [(0, 2)]), (-2, [])]
def pXm1 : MPoly := [(1, [(0, 1)]), (-1, [])]
def pYm1 : MPoly := [(1, [(1, 1)]), (-1, [])]
def pSq : MPoly := [(1, [(1, 2)]), (1, [(0, 2)])]

def go : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let _ ← Solver.mkVar false
  let l1 ← Solver.mkIneqLiteral ⟨.lt, [(pSum, false)]⟩
  let l2 ← Solver.mkIneqLiteral ⟨.gt, [(pXm1, false)]⟩
  let l3 ← Solver.mkIneqLiteral ⟨.lt, [(pYm1, false)]⟩
  let l4 ← Solver.mkIneqLiteral ⟨.gt, [(x0, false)]⟩
  let l5 ← Solver.mkIneqLiteral ⟨.gt, [(x1, false)]⟩
  let _ ← Solver.mkClause #[l1.negate] false
  let _ ← Solver.mkClause #[l2.negate] false
  let _ ← Solver.mkClause #[l3] false
  let _ ← Solver.mkClause #[l4] false
  let _ ← Solver.mkClause #[l5] false
  Solver.check (Solver.resolve Explain.explain)

-- the x0^2+x1^2<0 refutation (F2-groundwork recipe)
def go2 : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let _ ← Solver.mkVar false
  let l1 ← Solver.mkIneqLiteral ⟨.lt, [(pSq, false)]⟩
  let _ ← Solver.mkClause #[l1] false
  Solver.check (Solver.resolve Explain.explain)

-- F4 factorSplit case 1: x0^2+2*x0+1 = 0 ∧ x0+1 ≠ 0 (repeated factor)
def pSq2x1 : MPoly := [(1, [(0, 2)]), (2, [(0, 1)]), (1, [])]
def pXp1 : MPoly := [(1, [(0, 1)]), (1, [])]

def go3 : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let l1 ← Solver.mkIneqLiteral ⟨.eq, [(pSq2x1, false)]⟩
  let l2 ← Solver.mkIneqLiteral ⟨.eq, [(pXp1, false)]⟩
  let _ ← Solver.mkClause #[l1] false
  let _ ← Solver.mkClause #[l2.negate] false
  Solver.check (Solver.resolve Explain.explain)

-- F4 factorSplit case 2: x0^2-3x0+2 = 0 ∧ x0-1 ≠ 0 ∧ x0-2 ≠ 0
-- (two distinct factors — the zero-product case split)
def pQuad : MPoly := [(1, [(0, 2)]), ((-3), [(0, 1)]), (2, [])]
def pXm2 : MPoly := [(1, [(0, 1)]), ((-2), [])]

def go4 : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let l1 ← Solver.mkIneqLiteral ⟨.eq, [(pQuad, false)]⟩
  let l2 ← Solver.mkIneqLiteral ⟨.eq, [(pXm1, false)]⟩
  let l3 ← Solver.mkIneqLiteral ⟨.eq, [(pXm2, false)]⟩
  let _ ← Solver.mkClause #[l1] false
  let _ ← Solver.mkClause #[l2.negate] false
  let _ ← Solver.mkClause #[l3.negate] false
  Solver.check (Solver.resolve Explain.explain)

-- review-7 probe: THREE distinct factors — x0^3-6x0^2+11x0-6 = 0
-- with x0-1, x0-2, x0-3 all ≠ 0. Does the solver refute at stage 0,
-- and if so can the checker discharge the arith lemma (nlinarith
-- multiplies hypothesis PAIRS once — a triple product may be beyond it)?
def pCubic : MPoly := [(1, [(0, 3)]), ((-6), [(0, 2)]), (11, [(0, 1)]), ((-6), [])]
def pXm3 : MPoly := [(1, [(0, 1)]), ((-3), [])]

def go5 : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let l1 ← Solver.mkIneqLiteral ⟨.eq, [(pCubic, false)]⟩
  let l2 ← Solver.mkIneqLiteral ⟨.eq, [(pXm1, false)]⟩
  let l3 ← Solver.mkIneqLiteral ⟨.eq, [(pXm2, false)]⟩
  let l4 ← Solver.mkIneqLiteral ⟨.eq, [(pXm3, false)]⟩
  let _ ← Solver.mkClause #[l1] false
  let _ ← Solver.mkClause #[l2.negate] false
  let _ ← Solver.mkClause #[l3.negate] false
  let _ ← Solver.mkClause #[l4.negate] false
  Solver.check (Solver.resolve Explain.explain)

-- the √2-grade acceptance goal: x0 ≥ 0 ∧ x0² ≥ 2 ∧ x0 ≤ 1 (UNSAT)
def pX0sqM2 : MPoly := [(1, [(0, 2)]), ((-2), [])]

def goSqrt2 : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let lx ← Solver.mkIneqLiteral ⟨.lt, [(x0, false)]⟩      -- x0 ≥ 0   ⇔ ¬(x0 < 0)
  let l2 ← Solver.mkIneqLiteral ⟨.lt, [(pX0sqM2, false)]⟩ -- x0² ≥ 2  ⇔ ¬(x0² − 2 < 0)
  let l1 ← Solver.mkIneqLiteral ⟨.gt, [(pXm1, false)]⟩    -- x0 ≤ 1   ⇔ ¬(x0 − 1 > 0)
  let _ ← Solver.mkClause #[lx.negate] false
  let _ ← Solver.mkClause #[l2.negate] false
  let _ ← Solver.mkClause #[l1.negate] false
  Solver.check (Solver.resolve Explain.explain)

-- census probe: x0² + 1 < 0 — negative definiteness at stage 0?
-- (disc = −4 < 0 ⇒ no real roots; expect rootGeneric/definite-disc emission)
def pX0sqP1 : MPoly := [(1, [(0, 2)]), (1, [])]

def goDefinite : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let l1 ← Solver.mkIneqLiteral ⟨.lt, [(pX0sqP1, false)]⟩
  let _ ← Solver.mkClause #[l1] false
  Solver.check (Solver.resolve Explain.explain)

-- census probe: x0² + x0 + 1 < 0 — again definite-negative
def pDef2 : MPoly := [(1, [(0, 2)]), (1, [(0, 1)]), (1, [])]

def goDefinite2 : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let l1 ← Solver.mkIneqLiteral ⟨.lt, [(pDef2, false)]⟩
  let _ ← Solver.mkClause #[l1] false
  Solver.check (Solver.resolve Explain.explain)

-- census probe: x0² + x1 < 0 ∧ x1 > 1 — at the stage-1 sample the
-- quadratic x0²+c in x0 has disc = −4·c < 0 ⇒ generic root-atom fallback
-- (rootGeneric, definite-disc) — the census's known non-literal-local member.
def pX0sqX1 : MPoly := [(1, [(0, 2)]), (1, [(1, 1)])]
def pX1m1 : MPoly := [(1, [(1, 1)]), ((-1), [])]

def goRootGen : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let _ ← Solver.mkVar false
  let l1 ← Solver.mkIneqLiteral ⟨.lt, [(pX0sqX1, false)]⟩
  let l2 ← Solver.mkIneqLiteral ⟨.gt, [(pX1m1, false)]⟩
  let _ ← Solver.mkClause #[l1] false
  let _ ← Solver.mkClause #[l2] false
  Solver.check (Solver.resolve Explain.explain)

end DumpDriver

/-! ## nla-19b Slice 0 — simplify-cluster recon drivers

pd1: canonical Jovanović core `{x1 − x0² = 0, x1 < 0}` — const lc,
non-const remainder (expect `pseudoDivision x1 (x1−x0²) 1 1 x0² 1 false`,
path (e) rebuilt literal `x0² < 0`).
pd2: lc non-const + const-remainder path (b) + A4 (lc ineq):
`{x0 ≥ 1, x0·x1 − 1 = 0, x1 < 0}` — pseudo-remaind `x0·x1 = 1·(x0·x1−1)+1`,
factor dropped, d odd & kind lt & !isEven ⇒ add_lc_ineq (x0 > 0).
pd3: lc non-const quadratic eq + non-const remainder path (e):
`{x0 > 0, x0 ≤ 1/2, x0·x1² − 1 = 0, x1²+x1 < 0}` (1/x0 ≥ 2 vs x1∈(−1,0)).
pd4: kind flip (lcSign < 0): `{x0 ≤ −1, x0·x1 − 1 = 0, x1 > 0}` —
d=1 odd, factor odd, lcSign = −1 ⇒ atomSign −1, const remainder drop,
A4 with LT. -/

namespace DumpDriverPD

def x0 : MPoly := [(1, [(0, 1)])]
def x1 : MPoly := [(1, [(1, 1)])]
def pXm1 : MPoly := [(1, [(0, 1)]), (-1, [])]
def pXp1 : MPoly := [(1, [(0, 1)]), (1, [])]
def pEqLin : MPoly := [(1, [(1, 1)]), (-1, [(0, 2)])]        -- x1 − x0²
def pEqMul : MPoly := [(1, [(1, 1), (0, 1)]), (-1, [])]     -- x0·x1 − 1
def pEqMul2 : MPoly := [(1, [(1, 2), (0, 1)]), (-1, [])]    -- x0·x1² − 1
def pX1sqX1 : MPoly := [(1, [(1, 2)]), (1, [(1, 1)])]       -- x1² + x1
def pOm2 : MPoly := [(1, []), (-2, [(0, 1)])]               -- 1 − 2·x0

def goPd1 : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let _ ← Solver.mkVar false
  let le ← Solver.mkIneqLiteral ⟨.eq, [(pEqLin, false)]⟩
  let lc ← Solver.mkIneqLiteral ⟨.lt, [(x1, false)]⟩
  let _ ← Solver.mkClause #[le] false
  let _ ← Solver.mkClause #[lc] false
  Solver.check (Solver.resolve Explain.explain)

def goPd2 : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let _ ← Solver.mkVar false
  let lb ← Solver.mkIneqLiteral ⟨.lt, [(pXm1, false)]⟩   -- x0 ≥ 1
  let le ← Solver.mkIneqLiteral ⟨.eq, [(pEqMul, false)]⟩
  let lc ← Solver.mkIneqLiteral ⟨.lt, [(x1, false)]⟩
  let _ ← Solver.mkClause #[lb.negate] false
  let _ ← Solver.mkClause #[le] false
  let _ ← Solver.mkClause #[lc] false
  Solver.check (Solver.resolve Explain.explain)

def goPd3 : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let _ ← Solver.mkVar false
  let llo ← Solver.mkIneqLiteral ⟨.lt, [(x0, false)]⟩     -- x0 > 0
  let lhi ← Solver.mkIneqLiteral ⟨.lt, [(pOm2, false)]⟩   -- x0 ≤ 1/2 (negated below)
  let le ← Solver.mkIneqLiteral ⟨.eq, [(pEqMul2, false)]⟩
  let lc ← Solver.mkIneqLiteral ⟨.lt, [(pX1sqX1, false)]⟩
  let _ ← Solver.mkClause #[llo.negate] false
  let _ ← Solver.mkClause #[lhi.negate] false   -- ¬(1−2x0 < 0) ⟺ 2·x0 ≤ 1
  let _ ← Solver.mkClause #[le] false
  let _ ← Solver.mkClause #[lc] false
  Solver.check (Solver.resolve Explain.explain)

def goPd4 : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let _ ← Solver.mkVar false
  let lhi ← Solver.mkIneqLiteral ⟨.gt, [(pXp1, false)]⟩   -- x0 ≤ −1
  let le ← Solver.mkIneqLiteral ⟨.eq, [(pEqMul, false)]⟩
  let lc ← Solver.mkIneqLiteral ⟨.gt, [(x1, false)]⟩
  let _ ← Solver.mkClause #[lhi.negate] false
  let _ ← Solver.mkClause #[le] false
  let _ ← Solver.mkClause #[lc] false
  Solver.check (Solver.resolve Explain.explain)

/-- Even-d parity witness (d = 2, lcSign = −1, NO kind flip — the
discriminating cell of the :1132-1137 table): `{x0 ≤ −1, x0² ≤ 2,
x0·x1 − 1 = 0, 2·x1² − 1 < 0}`. f = 2x1²−1 (deg 2), eq deg 1 ⟹ d = 2;
identity x0²(2x1²−1) = Q·(x0·x1−1) + (2 − x0²): UNSAT since
x0² ∈ [1,2] forces x1² = 1/x0² ≥ 1/2. -/
def pTwoX1sqM1 : MPoly := [(2, [(1, 2)]), (-1, [])]         -- 2·x1² − 1
def pX0sqM2 : MPoly := [(1, [(0, 2)]), (-2, [])]            -- x0² − 2

def goPd6 : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let _ ← Solver.mkVar false
  let llo ← Solver.mkIneqLiteral ⟨.gt, [(pXp1, false)]⟩     -- x0 ≤ −1
  let lhi ← Solver.mkIneqLiteral ⟨.gt, [(pX0sqM2, false)]⟩  -- x0² ≤ 2
  let le ← Solver.mkIneqLiteral ⟨.eq, [(pEqMul, false)]⟩
  let lc ← Solver.mkIneqLiteral ⟨.lt, [(pTwoX1sqM1, false)]⟩
  let _ ← Solver.mkClause #[llo.negate] false
  let _ ← Solver.mkClause #[lhi.negate] false
  let _ ← Solver.mkClause #[le] false
  let _ ← Solver.mkClause #[lc] false
  Solver.check (Solver.resolve Explain.explain)

/-- 12e integer B&B driver: `{x0² = 2}` over one INTEGER var — UNSAT
over ℤ, SAT over ℝ (x = ±√2). Expect: search SAT with an irrational
witness, one B&B round (lo = 1, branch clause `{x0 ≤ 1, x0 ≥ 2}`),
restart, refutation. -/
def goInt1 : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar true
  let le ← Solver.mkIneqLiteral ⟨.eq, [(pX0sqM2, false)]⟩
  let _ ← Solver.mkClause #[le] false
  Solver.check (Solver.resolve Explain.explain)

/-- ordering_139 as a real nlsat problem (6 vars, x0..x5 =
a,b,c,da,db,dc): hypotheses hab: a·db ≤ b·da, hbc: b·dc ≤ c·db,
da/db/dc > 0, negated goal a·dc − c·da > 0. Polls: multilinear input,
but projection cross-products are the L1-open case — the Slice 0
standing-target fragment check. -/
def pA : MPoly := [(1, [(0, 1)])]def pB : MPoly := [(1, [(1, 1)])]
def pC : MPoly := [(1, [(2, 1)])]
def pDa : MPoly := [(1, [(3, 1)])]
def pDb : MPoly := [(1, [(4, 1)])]
def pDc : MPoly := [(1, [(5, 1)])]
def pHab : MPoly := [(1, [(4, 1), (0, 1)]), (-1, [(3, 1), (1, 1)])] -- a·db − b·da
def pHbc : MPoly := [(1, [(5, 1), (1, 1)]), (-1, [(4, 1), (2, 1)])] -- b·dc − c·db
def pNeg : MPoly := [(1, [(5, 1), (0, 1)]), (-1, [(3, 1), (2, 1)])] -- a·dc − c·da

def goO139 : SolverM (Option LBool) := do
  Solver.init
  let _ ← Solver.mkVar false
  let _ ← Solver.mkVar false
  let _ ← Solver.mkVar false
  let _ ← Solver.mkVar false
  let _ ← Solver.mkVar false
  let _ ← Solver.mkVar false
  let lhab ← Solver.mkIneqLiteral ⟨.gt, [(pHab, false)]⟩  -- hab: a·db − b·da ≤ 0
  let lhbc ← Solver.mkIneqLiteral ⟨.gt, [(pHbc, false)]⟩  -- hbc: b·dc − c·db ≤ 0
  let lda ← Solver.mkIneqLiteral ⟨.gt, [(pDa, false)]⟩
  let ldb ← Solver.mkIneqLiteral ⟨.gt, [(pDb, false)]⟩
  let ldc ← Solver.mkIneqLiteral ⟨.gt, [(pDc, false)]⟩
  let lneg ← Solver.mkIneqLiteral ⟨.gt, [(pNeg, false)]⟩  -- negated goal
  let _ ← Solver.mkClause #[lhab.negate] false
  let _ ← Solver.mkClause #[lhbc.negate] false
  let _ ← Solver.mkClause #[lda] false
  let _ ← Solver.mkClause #[ldb] false
  let _ ← Solver.mkClause #[ldc] false
  let _ ← Solver.mkClause #[lneg] false
  Solver.check (Solver.resolve Explain.explain)

end DumpDriverPD

def printSnap (name : String) (s : Solver) : IO Unit := do
  match s.refutation with
  | none => IO.println s!"{name}: NO refutation"
  | some (atoms, clauses, bundles, final) =>
    IO.println s!"private def {name}Atoms : Array (Option Atom) :=\n  {DumpPP.ppAtoms atoms}\n"
    IO.println s!"private def {name}Clauses : Array Clause :=\n  {DumpPP.ppClauses clauses}\n"
    IO.println s!"private def {name}Bundles : Array (Option TraceBundle) :=\n  {DumpPP.ppBundles bundles}\n"
    IO.println s!"private def {name}Final : TraceBundle :=\n  {DumpPP.ppBundleFinal final}\n"

def main : IO Unit := do
  let (r, s) := (DumpDriver.go.run Solver.empty : Option LBool × Solver)
  IO.println s!"driver result: {repr r}"
  printSnap "drv" s
  let (r2, s2) := (DumpDriver.go2.run Solver.empty : Option LBool × Solver)
  IO.println s!"sq result: {repr r2}"
  printSnap "sq" s2
  let (r3, s3) := (DumpDriver.go3.run Solver.empty : Option LBool × Solver)
  IO.println s!"fs1 result: {repr r3}"
  printSnap "fs1" s3
  let (r4, s4) := (DumpDriver.go4.run Solver.empty : Option LBool × Solver)
  IO.println s!"fs2 result: {repr r4}"
  printSnap "fs2" s4
  let (r5, s5) := (DumpDriver.go5.run Solver.empty : Option LBool × Solver)
  IO.println s!"fs3 result: {repr r5}"
  printSnap "fs3" s5
  let (r6, s6) := (DumpDriver.goSqrt2.run Solver.empty : Option LBool × Solver)
  IO.println s!"sqrt2 result: {repr r6}"
  printSnap "sqrt2" s6
  let (r7, s7) := (DumpDriver.goDefinite.run Solver.empty : Option LBool × Solver)
  IO.println s!"def1 result: {repr r7}"
  printSnap "def1" s7
  let (r8, s8) := (DumpDriver.goDefinite2.run Solver.empty : Option LBool × Solver)
  IO.println s!"def2 result: {repr r8}"
  printSnap "def2" s8
  let (r9, s9) := (DumpDriver.goRootGen.run Solver.empty : Option LBool × Solver)
  IO.println s!"rg result: {repr r9}"
  printSnap "rg" s9
  let (r10, s10) := (DumpDriverPD.goPd1.run Solver.empty : Option LBool × Solver)
  IO.println s!"pd1 result: {repr r10}"
  printSnap "pd1" s10
  let (r11, s11) := (DumpDriverPD.goPd2.run Solver.empty : Option LBool × Solver)
  IO.println s!"pd2 result: {repr r11}"
  printSnap "pd2" s11
  let (r12, s12) := (DumpDriverPD.goPd3.run Solver.empty : Option LBool × Solver)
  IO.println s!"pd3 result: {repr r12}"
  printSnap "pd3" s12
  let (r13, s13) := (DumpDriverPD.goPd4.run Solver.empty : Option LBool × Solver)
  IO.println s!"pd4 result: {repr r13}"
  printSnap "pd4" s13
  let (r15, s15) := (DumpDriverPD.goPd6.run Solver.empty : Option LBool × Solver)
  IO.println s!"pd6 result: {repr r15}"
  printSnap "pd6" s15
  let (r17, s17) := (DumpDriverPD.goInt1.run Solver.empty : Option LBool × Solver)
  IO.println s!"int1 result: {repr r17}"
  printSnap "int1" s17
  let (r16, s16) := (DumpDriverPD.goO139.run Solver.empty : Option LBool × Solver)
  IO.println s!"o139 result: {repr r16}"
  printSnap "o139" s16
  (← IO.getStdout).flush
  -- o139 (6-var CAD search) moved to scratch_o139.lean — it is the
  -- long pole, run separately.

