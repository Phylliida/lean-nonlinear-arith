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
  | .intBranch x v => s!".intBranch {x} {repr v}"
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

end DumpDriver

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
