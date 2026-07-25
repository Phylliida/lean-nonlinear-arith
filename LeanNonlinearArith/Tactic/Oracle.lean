import Mathlib

/-!
# Oracle v1 — untrusted integer bound propagation over the linear hypotheses

DESIGN-discharge-oracle §2b/§3: syntactic bound mining is *structurally*
incomplete for derived bounds (`a ≤ b - 2` and `5 ≤ a` imply `7 ≤ b`, which
is written nowhere, so no anchor lands at 7). This module computes the
implied-bound closure the way Z3 does: parse every ℤ-linear hypothesis into
a constraint over atoms, then run interval bound propagation to a fixpoint
(the `lp_bound_propagator` / `dep_intervals` analogue — Z3's nla reads its
anchors from the LRA solver's *propagated* column bounds, not from the
asserted formulas, so this is parity-restoring for anchor selection).

Everything is exact `Int` arithmetic: constraints have integer coefficients
and division by a coefficient rounds with floor/ceil (the ℤ-tightening Z3's
propagate_bound applies). No ℚ is needed until the simplex *model* (nla-06).

Trust: the oracle is entirely untrusted — it only *suggests* anchor
constants. Every suggested bound is discharged through the sandboxed
`tryDischarge` (omega) before a rule instantiates with it, so a wrong bound
can only waste one cached probe, never note a false fact.
-/

namespace LeanNonlinearArith.Tactic

open Lean Meta

/-- Sparse linear form `Σ coeffs[i].2 · atom_{coeffs[i].1} + k`. Coefficient
entries are merged and zero-free by construction (`addTerm`). -/
structure LinForm where
  coeffs : Array (Nat × Int) := #[]
  k : Int := 0
  deriving Repr

namespace LinForm

/-- Add `c · atom_i`, merging with an existing entry and dropping zeros. -/
def addTerm (f : LinForm) (i : Nat) (c : Int) : LinForm :=
  if c == 0 then f
  else match f.coeffs.findIdx? (·.1 == i) with
    | some j =>
      let c' := f.coeffs[j]!.2 + c
      if c' == 0 then { f with coeffs := f.coeffs.eraseIdx! j }
      else { f with coeffs := f.coeffs.set! j (i, c') }
    | none => { f with coeffs := f.coeffs.push (i, c) }

def add (f g : LinForm) : LinForm :=
  g.coeffs.foldl (fun acc (i, c) => acc.addTerm i c) { f with k := f.k + g.k }

def scale (c : Int) (f : LinForm) : LinForm :=
  if c == 0 then {} else { coeffs := f.coeffs.map fun (i, ci) => (i, c * ci), k := c * f.k }

def sub (f g : LinForm) : LinForm := f.add (g.scale (-1))

end LinForm

/-- Atom registry built during hypothesis parsing. -/
structure OracleParse where
  atoms : Array Expr := #[]
  index : Std.HashMap Expr Nat := {}
  /-- Constraints, each meaning `form ≥ 0` (strict already ℤ-tightened). -/
  cons : Array LinForm := #[]

/-- The propagated result: per-atom tightest derived bounds. -/
structure OracleCtx where
  atoms : Array Expr := #[]
  index : Std.HashMap Expr Nat := {}
  lb : Array (Option Int) := #[]
  ub : Array (Option Int) := #[]

private def atomIdx (e : Expr) : StateRefT OracleParse MetaM Nat := do
  let s ← get
  match s.index.get? e with
  | some i => return i
  | none =>
    let i := s.atoms.size
    set { s with atoms := s.atoms.push e, index := s.index.insert e i }
    return i

/-- Linearize a closed ℤ term over the atom registry. Total: any subterm the
walker cannot decompose becomes an atom, so the result is always faithful. -/
private partial def linOf (e : Expr) : StateRefT OracleParse MetaM LinForm := do
  let e := e.consumeMData
  if let some v := e.int? then return { k := v }
  let asAtom : StateRefT OracleParse MetaM LinForm := do
    return { coeffs := #[(← atomIdx e, 1)] }
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[t, _, _, _, a, b]) =>
    if t.isConstOf ``Int then return (← linOf a).add (← linOf b) else asAtom
  | (``HSub.hSub, #[t, _, _, _, a, b]) =>
    if t.isConstOf ``Int then return (← linOf a).sub (← linOf b) else asAtom
  | (``Neg.neg, #[t, _, a]) =>
    if t.isConstOf ``Int then return (← linOf a).scale (-1) else asAtom
  | (``HMul.hMul, #[t, _, _, _, a, b]) =>
    if t.isConstOf ``Int then
      if let some c := a.int? then return (← linOf b).scale c
      else if let some c := b.int? then return (← linOf a).scale c
      else asAtom
    else asAtom
  | _ => asAtom

/-- Parse one hypothesis type into `≥ 0` constraints. Recognizes the same
fact classes as the miner (slice-5/review-2 lessons): plain comparisons,
`Eq` both ways, and `¬`-wrapped comparisons. Strict ℤ bounds tighten by one
at parse time. -/
private def consOfHyp (ty : Expr) : StateRefT OracleParse MetaM (Array LinForm) := do
  let intCmp (t : Expr) : Bool := t.isConstOf ``Int
  -- (l, r, strict) meaning l ≤ r (strict: l < r)
  let facts : Array (Expr × Expr × Bool) ←
    match ty.getAppFnArgs with
    | (``LE.le, #[t, _, l, r]) => pure (if intCmp t then #[(l, r, false)] else #[])
    | (``LT.lt, #[t, _, l, r]) => pure (if intCmp t then #[(l, r, true)] else #[])
    | (``GE.ge, #[t, _, l, r]) => pure (if intCmp t then #[(r, l, false)] else #[])
    | (``GT.gt, #[t, _, l, r]) => pure (if intCmp t then #[(r, l, true)] else #[])
    | (``Eq, #[t, l, r]) =>
      pure (if intCmp t then #[(l, r, false), (r, l, false)] else #[])
    | (``Not, #[p]) =>
      match p.getAppFnArgs with
      | (``LT.lt, #[t, _, l, r]) => pure (if intCmp t then #[(r, l, false)] else #[])
      | (``LE.le, #[t, _, l, r]) => pure (if intCmp t then #[(r, l, true)] else #[])
      | (``GT.gt, #[t, _, l, r]) => pure (if intCmp t then #[(l, r, false)] else #[])
      | (``GE.ge, #[t, _, l, r]) => pure (if intCmp t then #[(l, r, true)] else #[])
      | _ => pure #[]
    | _ => pure #[]
  let mut out : Array LinForm := #[]
  for (l, r, strict) in facts do
    if l.hasLooseBVars || r.hasLooseBVars then continue
    -- l ≤ r  ⟹  r - l ≥ 0;  l < r  ⟹  r - l - 1 ≥ 0
    let f := (← linOf r).sub (← linOf l)
    out := out.push (if strict then { f with k := f.k - 1 } else f)
  return out

/-- `ceil(x / y)` for `y > 0`. -/
private def cdivPos (x y : Int) : Int := -((-x).fdiv y)

/-- Interval bound propagation to a fixpoint, capped rounds. For each
constraint `Σ cᵢxᵢ + k ≥ 0` and target term `cⱼxⱼ`: the residual sup of the
other terms bounds `cⱼxⱼ` from below, which floor/ceil-rounds to a bound on
`xⱼ`. A constraint with one unbounded term still propagates to that term
(standard one-unbounded trick); with two or more, it is silent this round.
Gauss–Seidel within a round is fine — updates are monotone. -/
private def propagate (n : Nat) (cons : Array LinForm) :
    Array (Option Int) × Array (Option Int) := Id.run do
  let mut lb : Array (Option Int) := Array.replicate n none
  let mut ub : Array (Option Int) := Array.replicate n none
  -- cap: generous and deterministic; cyclic tightening chains (infeasible
  -- contexts) terminate here and the omega leaf refutes instead
  for _ in [0 : 4 * n + 8] do
    let mut changed := false
    for c in cons do
      if c.coeffs.isEmpty then continue
      -- sup of Σ cᵢxᵢ over bounded terms + bookkeeping for unbounded ones
      let mut sup : Int := 0
      let mut unb : Nat := 0
      let mut unbIdx : Nat := 0
      for (i, ci) in c.coeffs do
        match (if ci > 0 then ub[i]! else lb[i]!) with
        | some b => sup := sup + ci * b
        | none => unb := unb + 1; unbIdx := i
      if unb ≥ 2 then continue
      for (i, ci) in c.coeffs do
        if unb == 1 && i != unbIdx then continue
        -- residual sup excluding this term's own contribution
        let supRest ←
          if unb == 1 then pure sup
          else match (if ci > 0 then ub[i]! else lb[i]!) with
            | some b => pure (sup - ci * b)
            | none => pure sup  -- unreachable (unb = 0)
        -- cᵢxᵢ ≥ -(k + supRest)
        let r := -(c.k + supRest)
        if ci > 0 then
          let cand := cdivPos r ci
          if lb[i]!.all (· < cand) then
            lb := lb.set! i (some cand); changed := true
        else
          let cand := r.fdiv ci
          if ub[i]!.all (cand < ·) then
            ub := ub.set! i (some cand); changed := true
    if !changed then break
  return (lb, ub)

/-- Build the oracle from the current local context. Call inside the goal's
context. Untrusted throughout — results only steer anchor selection. -/
def runOracle : MetaM OracleCtx := do
  let act : StateRefT OracleParse MetaM Unit := do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      let cs ← consOfHyp ty
      modify fun s => { s with cons := s.cons ++ cs }
  let ((), s) ← act.run {}
  let (lb, ub) := propagate s.atoms.size s.cons
  return { atoms := s.atoms, index := s.index, lb, ub }

/-- Derived bounds for an expr, `(lb?, ub?)`. -/
def OracleCtx.boundsOf (oc : OracleCtx) (e : Expr) : Option Int × Option Int :=
  match oc.index.get? e.consumeMData with
  | some i => (oc.lb[i]!, oc.ub[i]!)
  | none => (none, none)

/-- Union the oracle's derived bounds into a mined-anchor pair. Purely
additive (containment-safe): never removes a mined anchor. -/
def OracleCtx.augment (oc : OracleCtx) (e : Expr) :
    Array Int × Array Int → Array Int × Array Int := fun (los, his) =>
  let (lo?, hi?) := oc.boundsOf e
  let los := match lo? with
    | some v => if los.contains v then los else los.push v
    | none => los
  let his := match hi? with
    | some v => if his.contains v then his else his.push v
    | none => his
  (los, his)

end LeanNonlinearArith.Tactic
