import Mathlib
import LeanNonlinearArith.Templates.Intervals
import LeanNonlinearArith.Templates.Divisions
import LeanNonlinearArith.Templates.Tangent

/-!
# nla-05 slice 1: the saturation tactic, smallest end-to-end version

Pipeline (deterministic, model-free — see BOARD.md nla-05 design sketch):
1. **collect** — walk hypotheses + goal for `ℤ` products with two non-literal
   sides; postorder, so nested monomials are processed inner-first;
2. **generate** — for each monomial `a * b`, instantiate the sign/zero rule
   vocabulary below; premises are discharged by `assumption <|> omega`
   (assumption picks up facts noted for inner monomials, omega closes linear
   consequences of the hypotheses) through a sandboxed, memoized discharge
   oracle with a per-factor sign lattice and a meta-level fast path for
   literal-vs-literal side conditions (DESIGN-discharge-oracle.md §1 + §3
   v0.5);
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

/- Tangent-plane rules at mined constant points (RULES row T2; Z3 anchors at
model points, we anchor at hypothesis constants). Conclusions are linear in
`a`, `b` once `a*b` is abstracted. `c`/`d` are the anchor constants. -/
variable {c d : ℤ}

theorem sr_tan_ll (h₁ : c ≤ a) (h₂ : d ≤ b) : c * b + d * a - c * d ≤ a * b := by
  have := LeanNonlinearArith.Templates.Tangent.plane_ge a b c d
    (mul_nonneg (by linarith) (by linarith))
  linarith
theorem sr_tan_hh (h₁ : a ≤ c) (h₂ : b ≤ d) : c * b + d * a - c * d ≤ a * b := by
  have := LeanNonlinearArith.Templates.Tangent.plane_ge a b c d
    (sr_nonpos_nonpos (by linarith) (by linarith))
  linarith
theorem sr_tan_lh (h₁ : c ≤ a) (h₂ : b ≤ d) : a * b ≤ c * b + d * a - c * d := by
  have := LeanNonlinearArith.Templates.Tangent.plane_le a b c d
    (sr_nonneg_nonpos (by linarith) (by linarith))
  linarith
theorem sr_tan_hl (h₁ : a ≤ c) (h₂ : d ≤ b) : a * b ≤ c * b + d * a - c * d := by
  have := LeanNonlinearArith.Templates.Tangent.plane_le a b c d
    (sr_nonpos_nonneg (by linarith) (by linarith))
  linarith

/- Power rules (ring_nf normalizes repeated factors to `^`). Parity/nonzero
side conditions on the literal exponent are discharged by `decide` at
generation time. -/
variable {k : ℕ}

theorem sr_pow_even_nonneg (hk : Even k) (a : ℤ) : 0 ≤ a ^ k :=
  LeanNonlinearArith.Templates.MonomialBounds.even_pow_nonneg a k hk
theorem sr_pow_pos (k : ℕ) (ha : 0 < a) : 0 < a ^ k := pow_pos ha k
theorem sr_pow_nonneg (k : ℕ) (ha : 0 ≤ a) : 0 ≤ a ^ k := pow_nonneg ha k
theorem sr_pow_odd_neg (hk : Odd k) (ha : a < 0) : a ^ k < 0 := hk.pow_neg ha
theorem sr_pow_odd_nonpos (hk : Odd k) (ha : a ≤ 0) : a ^ k ≤ 0 := hk.pow_nonpos ha
theorem sr_pow_zero (hk : k ≠ 0) (ha : a = 0) : a ^ k = 0 := by
  rw [ha]; exact zero_pow hk

/- Const-substitution (RULES rows B9/PL1/T1/MB6): a factor mined to a point
collapses the product to an omega-linear term. -/
theorem sr_subst_left (b : ℤ) (ha : a = la) : a * b = la * b := by rw [ha]
theorem sr_subst_right (a : ℤ) (hb : b = lb) : a * b = a * lb := by rw [hb]

/- Zero-product split (RULES row B5): genuinely disjunctive conclusion; the
omega leaf case-splits on noted `∨` hypotheses. -/
theorem sr_zero_split (h : a * b = 0) : a = 0 ∨ b = 0 := mul_eq_zero.mp h

/- Square envelopes (RULES squares row): secant chord above the parabola on
a mined interval, tangent line below at a mined anchor. `s`/`p`/`t`/`q` are
pre-evaluated literals (parity: Z3 bakes evaluated constants; unevaluated
ground terms in noted facts are a leaf hazard — see the corner-fold rule). -/
theorem sr_sq_secant {lo hi s p : ℤ} (h₁ : lo ≤ a) (h₂ : a ≤ hi)
    (hs : s = lo + hi) (hp : p = lo * hi) : a ^ 2 ≤ s * a - p := by
  subst hs; subst hp
  nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)]

theorem sr_sq_tangent (a : ℤ) {t q : ℤ} (ht : t = 2 * c) (hq : q = c * c) :
    t * a - q ≤ a ^ 2 := by
  subst ht; subst hq
  nlinarith [sq_nonneg (a - c)]

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

/-- Destructure `base ^ k` with `base : ℤ` non-literal and `k` a `ℕ` literal
`≥ 2` (lower exponents are linear). -/
def isIntPow? (e : Expr) : Option (Expr × Nat) :=
  match e.getAppFnArgs with
  | (``HPow.hPow, #[tyB, tyE, _, _, a, n]) =>
    if tyB.isConstOf ``Int && tyE.isConstOf ``Nat then
      match n.nat? with
      | some k => if k ≥ 2 && !(e.int?).isSome then some (a, k) else none
      | none => none
    else none
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
    -- terms under binders have loose bvars: not generalizable, skip
    if !e.hasLooseBVars then
      if let some (a, b) := isIntMul? e then
        if !isIntLit a && !isIntLit b then
          let acc ← get
          if !acc.contains e then
            modify (·.push e)
      if let some (a, _) := isIntPow? e then
        if !isIntLit a then
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
  let factor := factor.consumeMData
  let mut los : Array Int := #[]
  let mut his : Array Int := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
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
        if r.consumeMData == factor then
          let v := if strict then v + 1 else v
          if !los.contains v then los := los.push v
      -- factor ⋈ lit: upper bound
      if let some v := r.int? then
        if l.consumeMData == factor then
          let v := if strict then v - 1 else v
          if !his.contains v then his := his.push v
    | _, _ => pure ()
  return (los, his)

/-- Evaluate an `ℤ` comparison whose both sides are integer literals, in meta
code. Returns `none` when the proposition is not of that shape. -/
def evalIntLitCmp? (ty : Expr) : Option Bool :=
  match ty.getAppFnArgs with
  | (``LE.le, #[t, _, l, r]) => do
    guard (t.isConstOf ``Int); return decide ((← l.int?) ≤ (← r.int?))
  | (``LT.lt, #[t, _, l, r]) => do
    guard (t.isConstOf ``Int); return decide ((← l.int?) < (← r.int?))
  | (``GE.ge, #[t, _, l, r]) => do
    guard (t.isConstOf ``Int); return decide ((← r.int?) ≤ (← l.int?))
  | (``GT.gt, #[t, _, l, r]) => do
    guard (t.isConstOf ``Int); return decide ((← r.int?) < (← l.int?))
  | (``Eq, #[t, l, r]) => do
    guard (t.isConstOf ``Int); return (← l.int?) == (← r.int?)
  | _ => none

/-- Discharge cache: premise type ↦ proof term (`none` = attempt failed).
Positive entries stay valid as the goal context grows — proof terms reference
fvars, and noting only adds hypotheses. Negative entries can go stale (a newly
noted fact may unblock them), so `generate` drops them after each noting
round. -/
abbrev DCache := IO.Ref (Std.HashMap Expr (Option Expr))

/-! Instrumentation counters, reported by `nla_saturate_stats`. -/
initialize nlaLitFast : IO.Ref Nat ← IO.mkRef 0
initialize nlaCacheHit : IO.Ref Nat ← IO.mkRef 0
initialize nlaTacticCall : IO.Ref Nat ← IO.mkRef 0

/-- Try to prove `ty` in the current goal's context (DESIGN-discharge-oracle
§1/§3). Three layers:
1. literal-vs-literal comparisons are decided in meta code — false ones cost
   nothing, true ones a `decide` proof, no tactic either way;
2. results are memoized in `cache` (`0 ≤ a` was previously re-proved by every
   rule that wanted it);
3. the tactic attempt (`assumption <|> omega`) is fully sandboxed: the
   instantiated proof term is extracted inside the sandbox and the elaboration
   state rolled back on both success and failure, so metavariable-context and
   info-tree growth never persist. -/
def tryDischarge (cache : DCache) (ty : Expr) : TacticM (Option Expr) := do
  if let some b := evalIntLitCmp? ty then
    nlaLitFast.modify (· + 1)
    if !b then return none
    let pf? ← try some <$> mkDecideProof ty catch _ => pure none
    if pf?.isSome then return pf?
    -- fall through to the tactic path if `decide` unexpectedly fails
  if let some r := (← cache.get).get? ty then
    nlaCacheHit.modify (· + 1)
    return r
  nlaTacticCall.modify (· + 1)
  let r ← do
    let s ← saveState
    try
      let mvar ← mkFreshExprMVar ty
      let gs ← Lean.Elab.runTactic mvar.mvarId!
        (← `(tactic| first | assumption | omega))
      if gs.1.isEmpty then
        let pf ← instantiateMVars mvar
        -- omega may have minted auxiliary env constants the proof term
        -- references; keep the environment (monotone, benign) while rolling
        -- back metavariable context and info trees
        let env ← getEnv
        restoreState s
        setEnv env
        -- the proof's syntactic type can differ from `ty` (e.g. `assumption`
        -- closes `0 < a` with `1 ≤ a` by ℤ defeq); ascribe `ty` so meta-level
        -- weakenings see the probed shape
        if pf.hasExprMVar then pure none
        else pure (some (← mkExpectedTypeHint pf ty))
      else
        restoreState s
        pure none
    catch _ =>
      restoreState s
      pure none
  cache.modify (·.insert ty r)
  return r

/-- Discharge every premise or fail. -/
def dischargeAll (cache : DCache) (tys : Array Expr) : TacticM (Option (Array Expr)) := do
  let mut pfs : Array Expr := #[]
  for ty in tys do
    match ← tryDischarge cache ty with
    | some pf => pfs := pfs.push pf
    | none => return none
  return some pfs

/-- Position of a factor in the sign lattice, with the strongest proved
fact. -/
inductive SignFacts where
  | zero (pf : Expr)     -- x = 0
  | pos (pf : Expr)      -- 0 < x
  | neg (pf : Expr)      -- x < 0
  | nonneg (pf : Expr)   -- 0 ≤ x
  | nonpos (pf : Expr)   -- x ≤ 0
  | unknown

/-- Weaken a lattice fact to the requested premise shape in meta code (zero
tactic calls): `pos → nonneg` and `neg → nonpos` by `le_of_lt`, `zero → both`
by `le_of_eq`. -/
def SignFacts.shapePf? (si : SignFacts) (s : Shape) : MetaM (Option Expr) := do
  match s, si with
  | .pos,    .pos pf    => return some pf
  | .neg,    .neg pf    => return some pf
  | .nonneg, .pos pf    => return some (← mkAppM ``le_of_lt #[pf])
  | .nonneg, .nonneg pf => return some pf
  | .nonneg, .zero pf   => return some (← mkAppM ``le_of_eq #[← mkAppM ``Eq.symm #[pf]])
  | .nonpos, .neg pf    => return some (← mkAppM ``le_of_lt #[pf])
  | .nonpos, .nonpos pf => return some pf
  | .nonpos, .zero pf   => return some (← mkAppM ``le_of_eq #[pf])
  | _, _ => return none

/-- Locate `x` in the sign lattice with ≤ 3 discharge calls (DESIGN §3 v0.5):
probe `0 ≤ x` and refine to pos/zero, else probe `x ≤ 0` and refine to neg.
All sign/zero/pow rules then instantiate from the result with no further
tactic calls. Recomputation for a repeated factor costs only cache lookups. -/
def signFactsFor (cache : DCache) (x : Expr) : TacticM SignFacts := do
  let zero := mkIntLit 0
  if let some pf := ← tryDischarge cache (← mkAppM ``LE.le #[zero, x]) then
    if let some pfp := ← tryDischarge cache (← mkAppM ``LT.lt #[zero, x]) then
      return .pos pfp
    if let some pfz := ← tryDischarge cache (← mkAppM ``Eq #[x, zero]) then
      return .zero pfz
    return .nonneg pf
  if let some pf := ← tryDischarge cache (← mkAppM ``LE.le #[x, zero]) then
    if let some pfn := ← tryDischarge cache (← mkAppM ``LT.lt #[x, zero]) then
      return .neg pfn
    return .nonpos pf
  return .unknown

/-- Note a fact into the goal context. The name is freshened so generated
hypotheses can never capture or collide with user hypotheses. -/
def noteFact (name : Name) (concl proof : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let (_, g') ← g.note (← mkFreshUserName name) proof (some concl)
  replaceMainGoal [g']

/-- Facts derived for one monomial, computed inside the current goal's
context so premise discharge sees previously noted facts. -/
def factsFor (cache : DCache) (m : Expr) (idx : Nat) :
    TacticM (Array (Name × Expr × Expr)) := do
  let g ← getMainGoal
  g.withContext do
    let some (a, b) := isIntMul? m | return #[]
    let mut out : Array (Name × Expr × Expr) := #[]
    -- squares: unconditional
    if a == b then
      let pf ← mkAppM ``sr_sq #[a]
      out := out.push (.mkSimple s!"nla_sq_{idx}", ← inferType pf, pf)
    -- sign lattice per factor, once; zero/sign rules read it with no
    -- further tactic calls
    let siA ← signFactsFor cache a
    let siB ← signFactsFor cache b
    -- zero rules
    if let .zero pa := siA then
      let pf ← mkAppM ``sr_zero_left #[b, pa]
      out := out.push (.mkSimple s!"nla_zero_{idx}", ← inferType pf, pf)
    else if let .zero pb := siB then
      let pf ← mkAppM ``sr_zero_right #[a, pb]
      out := out.push (.mkSimple s!"nla_zero_{idx}", ← inferType pf, pf)
    else
      -- B5 zero-product split: m provably zero with neither factor's zero
      -- known — note the disjunction; the omega leaf splits on `∨` hyps
      if let some pm := ← tryDischarge cache (← mkAppM ``Eq #[m, mkIntLit 0]) then
        let pf ← mkAppM ``sr_zero_split #[pm]
        out := out.push (.mkSimple s!"nla_zsplit_{idx}", ← inferType pf, pf)
    -- binary sign rules: first rule both of whose premise shapes the
    -- lattice can serve wins
    for (lem, sa, sb) in signRules do
      let some pa ← siA.shapePf? sa | continue
      let some pb ← siB.shapePf? sb | continue
      let pf ← mkAppM lem #[pa, pb]
      out := out.push (.mkSimple s!"nla_sign_{idx}", ← inferType pf, pf)
      break
    -- order rules with mined constants (O1/M1-style bound propagation)
    let (losA, hisA) ← mineBounds a
    let (losB, hisB) ← mineBounds b
    let zero := mkIntLit 0
    let le (x y : Expr) : MetaM Expr := mkAppM ``LE.le #[x, y]
    -- const-substitution (RULES B9/PL1/T1/MB6): factor mined to a point →
    -- product collapses to an omega-linear term (unlike the tangent pairs,
    -- this needs nothing about the other factor)
    for c in losA do
      if hisA.contains c then
        if let some pfs := ← dischargeAll cache #[← le (mkIntLit c) a, ← le a (mkIntLit c)] then
          let pfEq ← mkAppM ``le_antisymm #[pfs[1]!, pfs[0]!]
          let pf ← mkAppM ``sr_subst_left #[b, pfEq]
          out := out.push (.mkSimple s!"nla_cst_{idx}_{out.size}", ← inferType pf, pf)
    for c in losB do
      if hisB.contains c then
        if let some pfs := ← dischargeAll cache #[← le (mkIntLit c) b, ← le b (mkIntLit c)] then
          let pfEq ← mkAppM ``le_antisymm #[pfs[1]!, pfs[0]!]
          let pf ← mkAppM ``sr_subst_right #[a, pfEq]
          out := out.push (.mkSimple s!"nla_cst_{idx}_{out.size}", ← inferType pf, pf)
    for lav in losA do
      for lbv in losB do
        let la := mkIntLit lav
        let lb := mkIntLit lbv
        let prems := #[← le la a, ← le lb b, ← le zero la, ← le zero lb]
        if let some pfs := ← dischargeAll cache prems then
          let pf ← mkAppM ``sr_lb_mul pfs
          out := out.push (.mkSimple s!"nla_lb_{idx}_{out.size}", ← inferType pf, pf)
    for hiav in hisA do
      for hibv in hisB do
        let hia := mkIntLit hiav
        let hib := mkIntLit hibv
        let premsN := #[← le a hia, ← le b hib, ← le zero a, ← le zero b]
        if let some pfs := ← dischargeAll cache premsN then
          let pf ← mkAppM ``sr_ub_mul pfs
          out := out.push (.mkSimple s!"nla_ub_{idx}_{out.size}", ← inferType pf, pf)
        let premsP := #[← le a hia, ← le b hib, ← le hia zero, ← le hib zero]
        if let some pfs := ← dischargeAll cache premsP then
          let pf ← mkAppM ``sr_ub_neg_mul pfs
          out := out.push (.mkSimple s!"nla_ubn_{idx}_{out.size}", ← inferType pf, pf)
    -- tangent planes anchored at mined constants (linear conclusions)
    let tangentCombos : List (Name × Array Int × Array Int × Bool × Bool) :=
      [(``sr_tan_ll, losA, losB, true,  true),
       (``sr_tan_hh, hisA, hisB, false, false),
       (``sr_tan_lh, losA, hisB, true,  false),
       (``sr_tan_hl, hisA, losB, false, true)]
    for (lem, csA, csB, aLower, bLower) in tangentCombos do
      for cv in csA do
        for dv in csB do
          let cE := mkIntLit cv
          let dE := mkIntLit dv
          let pA ← if aLower then le cE a else le a cE
          let pB ← if bLower then le dE b else le b dE
          if let some pfs := ← dischargeAll cache #[pA, pB] then
            let pf ← mkAppM lem pfs
            out := out.push
              (.mkSimple s!"nla_tan_{idx}_{out.size}", ← inferType pf, pf)
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
            if let some pfs := ← dischargeAll cache prems then
              -- fold the corner min/max to a single literal HERE: noted
              -- `min`/`max` facts make the omega leaf case-split per
              -- occurrence, which is exponential in the number of corner
              -- facts (measured: 168s leaf on an 8-monomial goal)
              let corners := #[lav * lbv, lav * hibv, hiav * lbv, hiav * hibv]
              let hiV := corners.foldl max corners[0]!
              let loV := corners.foldl min corners[0]!
              let pfHi ← mkAppM ``Templates.Intervals.mul_le_max_corners pfs
              if let (``LE.le, #[_, _, _, maxE]) := (← inferType pfHi).getAppFnArgs then
                let pfStep ← mkDecideProof (← le maxE (mkIntLit hiV))
                let pf ← mkAppM ``le_trans #[pfHi, pfStep]
                out := out.push
                  (.mkSimple s!"nla_chi_{idx}_{out.size}", ← inferType pf, pf)
              let pfLo ← mkAppM ``Templates.Intervals.min_corners_le_mul pfs
              if let (``LE.le, #[_, _, minE, _]) := (← inferType pfLo).getAppFnArgs then
                let pfStep ← mkDecideProof (← le (mkIntLit loV) minE)
                let pf ← mkAppM ``le_trans #[pfStep, pfLo]
                out := out.push
                  (.mkSimple s!"nla_clo_{idx}_{out.size}", ← inferType pf, pf)
    return out

/-- Facts for a power monomial `a ^ k` (literal `k ≥ 2`): parity/zero/sign
rules, side conditions on the exponent by `decide`. -/
def factsForPow (cache : DCache) (m : Expr) (idx : Nat) :
    TacticM (Array (Name × Expr × Expr)) := do
  let g ← getMainGoal
  g.withContext do
    let some (a, k) := isIntPow? m | return #[]
    let mut out : Array (Name × Expr × Expr) := #[]
    let kE := mkNatLit k
    -- even exponent: unconditionally nonnegative
    if k % 2 == 0 then
      let hk ← mkDecideProof (← mkAppM ``Even #[kE])
      let pf ← mkAppM ``sr_pow_even_nonneg #[hk, a]
      out := out.push (.mkSimple s!"nla_pow_{idx}", ← inferType pf, pf)
    -- zero/sign rules read the base's lattice position; strongest rule wins
    match ← signFactsFor cache a with
    | .zero pa =>
      let hk ← mkDecideProof (← mkAppM ``Ne #[kE, mkNatLit 0])
      let pf ← mkAppM ``sr_pow_zero #[hk, pa]
      out := out.push (.mkSimple s!"nla_pow_{idx}_z", ← inferType pf, pf)
    | .pos pa =>
      let pf ← mkAppM ``sr_pow_pos #[kE, pa]
      out := out.push (.mkSimple s!"nla_pow_{idx}_s", ← inferType pf, pf)
    | .nonneg pa =>
      let pf ← mkAppM ``sr_pow_nonneg #[kE, pa]
      out := out.push (.mkSimple s!"nla_pow_{idx}_s", ← inferType pf, pf)
    | .neg pa =>
      if k % 2 == 1 then
        let hk ← mkDecideProof (← mkAppM ``Odd #[kE])
        let pf ← mkAppM ``sr_pow_odd_neg #[hk, pa]
        out := out.push (.mkSimple s!"nla_pow_{idx}_s", ← inferType pf, pf)
    | .nonpos pa =>
      if k % 2 == 1 then
        let hk ← mkDecideProof (← mkAppM ``Odd #[kE])
        let pf ← mkAppM ``sr_pow_odd_nonpos #[hk, pa]
        out := out.push (.mkSimple s!"nla_pow_{idx}_s", ← inferType pf, pf)
    | .unknown => pure ()
    -- square envelopes (RULES squares row): secant above on each mined
    -- interval, tangent below at each mined anchor; `s`/`p`/`t`/`q`
    -- pre-evaluated to literals (corner-fold rule: no unevaluated ground
    -- terms in noted facts)
    if k == 2 then
      let (los, his) ← mineBounds a
      let le (x y : Expr) : MetaM Expr := mkAppM ``LE.le #[x, y]
      for lo in los do
        for hi in his do
          let prems := #[← le (mkIntLit lo) a, ← le a (mkIntLit hi)]
          if let some pfs := ← dischargeAll cache prems then
            let hs ← mkDecideProof (← mkAppM ``Eq
              #[mkIntLit (lo + hi), ← mkAppM ``HAdd.hAdd #[mkIntLit lo, mkIntLit hi]])
            let hp ← mkDecideProof (← mkAppM ``Eq
              #[mkIntLit (lo * hi), ← mkAppM ``HMul.hMul #[mkIntLit lo, mkIntLit hi]])
            let pf ← mkAppM ``sr_sq_secant #[pfs[0]!, pfs[1]!, hs, hp]
            out := out.push (.mkSimple s!"nla_sqs_{idx}_{out.size}", ← inferType pf, pf)
      for c in (los ++ his).toList.eraseDups do
        let ht ← mkDecideProof (← mkAppM ``Eq
          #[mkIntLit (2 * c), ← mkAppM ``HMul.hMul #[mkIntLit 2, mkIntLit c]])
        let hq ← mkDecideProof (← mkAppM ``Eq
          #[mkIntLit (c * c), ← mkAppM ``HMul.hMul #[mkIntLit c, mkIntLit c]])
        let pf ← mkAppM ``sr_sq_tangent #[a, ht, hq]
        out := out.push (.mkSimple s!"nla_sqt_{idx}_{out.size}", ← inferType pf, pf)
    return out

/-- Generation round: instantiate the rule vocabulary for every monomial,
inner monomials first so their facts feed outer premises. -/
def generate (ms : Array Expr) : TacticM Unit := do
  let cache : DCache ← IO.mkRef {}
  let mut idx := 0
  for m in ms do
    let facts ← if (isIntMul? m).isSome then factsFor cache m idx
                else factsForPow cache m idx
    for (nm, ty, pf) in facts do
      noteFact nm ty pf
    if !facts.isEmpty then
      -- the context grew: failed discharges may now succeed, so drop
      -- negative entries; positive proofs stay valid (fvars persist)
      cache.modify (·.filter fun _ v => v.isSome)
    idx := idx + 1

def saturateCore (stats : Bool := false) : TacticM Unit := do
  let t0 ← IO.monoMsNow
  -- 0. normalize: sum-of-monomials form; doubles as commutative canonization
  evalTactic (← `(tactic| try ring_nf at *))
  if (← getGoals).isEmpty then return
  let t1 ← IO.monoMsNow
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
  let t2 ← IO.monoMsNow
  -- 3. leaf: omega atomizes the (ring_nf-canonized) monomials natively —
  -- no explicit generalization needed; SaturateTests pins this assumption
  evalTactic (← `(tactic| omega))
  let t3 ← IO.monoMsNow
  if stats then
    logInfo s!"nla_saturate: ring_nf {t1 - t0}ms · generate {t2 - t1}ms \
      ({ms.size} monomials, {← nlaTacticCall.get} tactic calls, \
      {← nlaCacheHit.get} cache hits, {← nlaLitFast.get} literal fast) \
      · omega {t3 - t2}ms"

elab "nla_saturate" : tactic => saturateCore

/-- `nla_saturate` with phase timings and discharge-oracle counters. -/
elab "nla_saturate_stats" : tactic => do
  nlaLitFast.set 0; nlaCacheHit.set 0; nlaTacticCall.set 0
  saturateCore (stats := true)

end LeanNonlinearArith.Tactic
