import Mathlib
import LeanNonlinearArith.Templates.Intervals

/-!
# nla-05 slice 1: the saturation tactic, smallest end-to-end version

Pipeline (deterministic, model-free — see BOARD.md nla-05 design sketch):
1. **collect** — walk hypotheses + goal for `ℤ` products with two non-literal
   sides; postorder, so nested monomials are processed inner-first;
2. **generate** — for each monomial `a * b`, instantiate the sign/zero rule
   vocabulary below; premises are discharged by `assumption <|> omega`
   (assumption picks up facts noted for inner monomials, omega closes linear
   consequences of the hypotheses);
3. **abstract** — revert propositional hypotheses, `generalize` each monomial
   (inner-first) to a fresh variable, reintroduce: the context is now linear;
4. **leaf** — `omega`.

v0 scope: `ℤ` only, products only (`^` handled in a later slice), sign/zero
rules only (order/monotonicity/tangent generation follow the same skeleton).
-/

namespace LeanNonlinearArith.Tactic

open Lean Meta Elab Tactic

/-! ## Rule vocabulary (fixed names, fixed premise order) -/

section Rules
variable {a b : ℤ}

theorem sr_nonneg_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := mul_nonneg ha hb
theorem sr_pos_pos (ha : 0 < a) (hb : 0 < b) : 0 < a * b := mul_pos ha hb
theorem sr_nonpos_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by nlinarith
theorem sr_neg_neg (ha : a < 0) (hb : b < 0) : 0 < a * b := mul_pos_of_neg_of_neg ha hb
theorem sr_nonneg_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by nlinarith
theorem sr_nonpos_nonneg (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by nlinarith
theorem sr_pos_neg (ha : 0 < a) (hb : b < 0) : a * b < 0 := by nlinarith
theorem sr_neg_pos (ha : a < 0) (hb : 0 < b) : a * b < 0 := by nlinarith
theorem sr_zero_left (b : ℤ) (ha : a = 0) : a * b = 0 := by rw [ha, zero_mul]
theorem sr_zero_right (a : ℤ) (hb : b = 0) : a * b = 0 := by rw [hb, mul_zero]
theorem sr_sq (a : ℤ) : 0 ≤ a * a := mul_self_nonneg a

/- Order rules with mined constants (RULES rows O1/M1-style bound
propagation). Premise order: a-bound, b-bound, then side conditions. -/
variable {la lb ha' hb' : ℤ}

theorem sr_lb_mul (h₁ : la ≤ a) (h₂ : lb ≤ b) (h₃ : 0 ≤ la) (h₄ : 0 ≤ lb) :
    la * lb ≤ a * b := by nlinarith

theorem sr_ub_mul (h₁ : a ≤ ha') (h₂ : b ≤ hb') (h₃ : 0 ≤ a) (h₄ : 0 ≤ b) :
    a * b ≤ ha' * hb' := by nlinarith

theorem sr_ub_neg_mul (h₁ : a ≤ ha') (h₂ : b ≤ hb') (h₃ : ha' ≤ 0) (h₄ : hb' ≤ 0) :
    ha' * hb' ≤ a * b := by nlinarith

end Rules

/-- Premise/conclusion shapes for the binary sign rules. -/
inductive Shape | nonneg | pos | nonpos | neg
  deriving BEq, Repr

/-- `shapeProp s x` builds the `ℤ` proposition for shape `s` about `x`. -/
def shapeProp (s : Shape) (x : Expr) : MetaM Expr := do
  let zero := mkIntLit 0
  match s with
  | .nonneg => mkAppM ``LE.le #[zero, x]
  | .pos    => mkAppM ``LT.lt #[zero, x]
  | .nonpos => mkAppM ``LE.le #[x, zero]
  | .neg    => mkAppM ``LT.lt #[x, zero]

/-- Binary sign rules: (lemma, shape of `a`-premise, shape of `b`-premise). -/
def signRules : List (Name × Shape × Shape) :=
  [(``sr_pos_pos,        .pos,    .pos),
   (``sr_neg_neg,        .neg,    .neg),
   (``sr_pos_neg,        .pos,    .neg),
   (``sr_neg_pos,        .neg,    .pos),
   (``sr_nonneg_nonneg,  .nonneg, .nonneg),
   (``sr_nonpos_nonpos,  .nonpos, .nonpos),
   (``sr_nonneg_nonpos,  .nonneg, .nonpos),
   (``sr_nonpos_nonneg,  .nonpos, .nonneg)]

/-- Destructure an `ℤ` multiplication. -/
def isIntMul? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``HMul.hMul, #[ty, _, _, _, a, b]) =>
    if ty.isConstOf ``Int then some (a, b) else none
  | _ => none

/-- Integer literal test (numerals and their negations). -/
def isIntLit (e : Expr) : Bool :=
  (e.int?).isSome

/-- Collect monomials (ℤ products with two non-literal sides) in postorder:
inner products before the products containing them. -/
partial def collectMonomials (e : Expr) : StateRefT (Array Expr) MetaM Unit := do
  match e with
  | .app .. => do
    for arg in e.getAppArgs do
      collectMonomials arg
    if let some (a, b) := isIntMul? e then
      if !isIntLit a && !isIntLit b then
        let acc ← get
        if !acc.contains e then
          modify (·.push e)
  | .mdata _ b => collectMonomials b
  | .forallE _ d b _ => collectMonomials d; collectMonomials b
  | .lam _ d b _ => collectMonomials d; collectMonomials b
  | .letE _ t v b _ => collectMonomials t; collectMonomials v; collectMonomials b
  | _ => pure ()

/-- Mine literal bounds for `factor` from the propositional hypotheses:
returns (lower-bound literals, upper-bound literals). Strict bounds count —
premise discharge (omega) absorbs the strictness. Call inside the goal ctx. -/
def mineBounds (factor : Expr) : MetaM (Array Int × Array Int) := do
  let mut los : Array Int := #[]
  let mut his : Array Int := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty := decl.type
    -- (l ⋈ r, strict); GE/GT normalized by swapping
    let (lhs?, rhs?, strict) :=
      match ty.getAppFnArgs with
      | (``LE.le, #[_, _, l, r]) => (some l, some r, false)
      | (``LT.lt, #[_, _, l, r]) => (some l, some r, true)
      | (``GE.ge, #[_, _, l, r]) => (some r, some l, false)
      | (``GT.gt, #[_, _, l, r]) => (some r, some l, true)
      | _ => (none, none, false)
    match lhs?, rhs? with
    | some l, some r =>
      -- lit ⋈ factor: lower bound (strict ℤ bound tightens by one)
      if let some v := l.int? then
        if r == factor then
          let v := if strict then v + 1 else v
          if !los.contains v then los := los.push v
      -- factor ⋈ lit: upper bound
      if let some v := r.int? then
        if l == factor then
          let v := if strict then v - 1 else v
          if !his.contains v then his := his.push v
    | _, _ => pure ()
  return (los, his)

/-- Try to prove `ty` in the current goal's context by `assumption <|> omega`.
Returns the proof term on success. -/
def tryDischarge (ty : Expr) : TacticM (Option Expr) := do
  let mvar ← mkFreshExprMVar ty
  let s ← saveState
  try
    let gs ← Lean.Elab.runTactic mvar.mvarId!
      (← `(tactic| first | assumption | omega))
    if gs.1.isEmpty then
      return some (← instantiateMVars mvar)
    else
      restoreState s
      return none
  catch _ =>
    restoreState s
    return none

/-- Discharge every premise or fail. -/
def dischargeAll (tys : Array Expr) : TacticM (Option (Array Expr)) := do
  let mut pfs : Array Expr := #[]
  for ty in tys do
    match ← tryDischarge ty with
    | some pf => pfs := pfs.push pf
    | none => return none
  return some pfs

/-- Note a fact into the goal context. -/
def noteFact (name : Name) (concl proof : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let (_, g') ← g.note name proof (some concl)
  replaceMainGoal [g']

/-- Facts derived for one monomial, computed inside the current goal's
context so premise discharge sees previously noted facts. -/
def factsFor (m : Expr) (idx : Nat) : TacticM (Array (Name × Expr × Expr)) := do
  let g ← getMainGoal
  g.withContext do
    let some (a, b) := isIntMul? m | return #[]
    let mut out : Array (Name × Expr × Expr) := #[]
    -- squares: unconditional
    if a == b then
      let pf ← mkAppM ``sr_sq #[a]
      out := out.push (.mkSimple s!"nla_sq_{idx}", ← inferType pf, pf)
    -- zero rules
    let aZero ← mkAppM ``Eq #[a, mkIntLit 0]
    if let some pa := ← tryDischarge aZero then
      let pf ← mkAppM ``sr_zero_left #[b, pa]
      out := out.push (.mkSimple s!"nla_zero_{idx}", ← inferType pf, pf)
    else
      let bZero ← mkAppM ``Eq #[b, mkIntLit 0]
      if let some pb := ← tryDischarge bZero then
        let pf ← mkAppM ``sr_zero_right #[a, pb]
        out := out.push (.mkSimple s!"nla_zero_{idx}", ← inferType pf, pf)
    -- binary sign rules: first rule whose premises both discharge wins
    for (lem, sa, sb) in signRules do
      let tya ← shapeProp sa a
      let some pa := ← tryDischarge tya | continue
      let tyb ← shapeProp sb b
      let some pb := ← tryDischarge tyb | continue
      let pf ← mkAppM lem #[pa, pb]
      out := out.push (.mkSimple s!"nla_sign_{idx}", ← inferType pf, pf)
      break
    -- order rules with mined constants (O1/M1-style bound propagation)
    let (losA, hisA) ← mineBounds a
    let (losB, hisB) ← mineBounds b
    let zero := mkIntLit 0
    let le (x y : Expr) : MetaM Expr := mkAppM ``LE.le #[x, y]
    for lav in losA do
      for lbv in losB do
        let la := mkIntLit lav
        let lb := mkIntLit lbv
        let prems := #[← le la a, ← le lb b, ← le zero la, ← le zero lb]
        if let some pfs := ← dischargeAll prems then
          let pf ← mkAppM ``sr_lb_mul pfs
          out := out.push (.mkSimple s!"nla_lb_{idx}_{out.size}", ← inferType pf, pf)
    for hiav in hisA do
      for hibv in hisB do
        let hia := mkIntLit hiav
        let hib := mkIntLit hibv
        let premsN := #[← le a hia, ← le b hib, ← le zero a, ← le zero b]
        if let some pfs := ← dischargeAll premsN then
          let pf ← mkAppM ``sr_ub_mul pfs
          out := out.push (.mkSimple s!"nla_ub_{idx}_{out.size}", ← inferType pf, pf)
        let premsP := #[← le a hia, ← le b hib, ← le hia zero, ← le hib zero]
        if let some pfs := ← dischargeAll premsP then
          let pf ← mkAppM ``sr_ub_neg_mul pfs
          out := out.push (.mkSimple s!"nla_ubn_{idx}_{out.size}", ← inferType pf, pf)
    -- full intervals: corner-product bounds (Templates.Intervals)
    for lav in losA do
      for hiav in hisA do
        for lbv in losB do
          for hibv in hisB do
            let la := mkIntLit lav
            let hia := mkIntLit hiav
            let lb := mkIntLit lbv
            let hib := mkIntLit hibv
            let prems := #[← le la a, ← le a hia, ← le lb b, ← le b hib]
            if let some pfs := ← dischargeAll prems then
              let pfHi ← mkAppM ``Templates.Intervals.mul_le_max_corners pfs
              out := out.push
                (.mkSimple s!"nla_chi_{idx}_{out.size}", ← inferType pfHi, pfHi)
              let pfLo ← mkAppM ``Templates.Intervals.min_corners_le_mul pfs
              out := out.push
                (.mkSimple s!"nla_clo_{idx}_{out.size}", ← inferType pfLo, pfLo)
    return out

/-- Generation round: instantiate the rule vocabulary for every monomial,
inner monomials first so their facts feed outer premises. -/
def generate (ms : Array Expr) : TacticM Unit := do
  let mut idx := 0
  for m in ms do
    for (nm, ty, pf) in ← factsFor m idx do
      noteFact nm ty pf
    idx := idx + 1

/-- Abstract every monomial to a fresh variable: revert propositional
hypotheses, generalize (inner-first), reintroduce. -/
def abstractMonomials (ms : Array Expr) : TacticM Unit := do
  let g ← getMainGoal
  let props ← g.getNondepPropHyps
  let (_, g) ← g.revert props
  let args : Array GeneralizeArg := ms.map fun m =>
    { expr := m, xName? := none, hName? := none }
  let (_, g) ← g.generalize args
  let (_, g) ← g.intros
  replaceMainGoal [g]

elab "nla_saturate" : tactic => do
  -- 1. collect from hypotheses and goal
  let g ← getMainGoal
  let ms ← g.withContext do
    let act : StateRefT (Array Expr) MetaM Unit := do
      for fv in ← g.getNondepPropHyps do
        collectMonomials (← fv.getType)
      collectMonomials (← g.getType)
    let ((), ms) ← act.run #[]
    pure ms
  -- 2. generate
  generate ms
  -- 3. abstract + 4. leaf
  abstractMonomials ms
  evalTactic (← `(tactic| omega))

end LeanNonlinearArith.Tactic
