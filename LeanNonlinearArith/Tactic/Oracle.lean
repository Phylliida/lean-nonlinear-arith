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
  /-- Unit ±-equalities `atom_i = ±atom_j` (`true` = same sign), the feed
  for the `evars` parity union-find. -/
  pmEqs : Array (Nat × Nat × Bool) := #[]

/-- The propagated result: per-atom tightest derived bounds plus the
±-equivalence classes (Z3's `evars`). `uf[i] = (parent, flip)` with
`value(i) = (flip ? -1 : 1) · value(parent)`. -/
structure OracleCtx where
  atoms : Array Expr := #[]
  index : Std.HashMap Expr Nat := {}
  lb : Array (Option Int) := #[]
  ub : Array (Option Int) := #[]
  uf : Array (Nat × Bool) := #[]

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
    -- unit ±-equality feed for the evars union-find: an `Eq` produces the
    -- same form twice with opposite signs, so inspect the first only.
    -- `g·x ∓ g·y = 0` (equal |coeffs|, zero constant) means `x = ±y`.
    if ty.isAppOf ``Eq && !strict && out.size == 1 then
      if f.k == 0 && f.coeffs.size == 2 then
        let (i, ci) := f.coeffs[0]!
        let (j, cj) := f.coeffs[1]!
        if ci.natAbs == cj.natAbs then
          -- ci·xi + cj·xj = 0: opposite coeffs ⟹ xi = xj (same sign);
          -- equal coeffs ⟹ xi = -xj (negated)
          modify fun s => { s with pmEqs := s.pmEqs.push (i, j, ci == cj) }
  return out

/-- `ceil(x / y)` for `y > 0`. -/
def cdivPos (x y : Int) : Int := -((-x).fdiv y)

/-! ### Rounding-formula correctness

The two tighten formulas in `propagate` are *fully characterized* by the
iffs below (2026-07-26 review): the forward direction is soundness (every
solution of the constraint satisfies the emitted bound — so the omega
discharge of an oracle suggestion can never fail for arithmetic reasons),
the backward direction is tightness (the bound is attained by an integer
satisfying the row inequality, i.e. no strictly better integer bound
exists from this row alone). The residual trust in `propagate` is the
sup-accumulation plumbing, tracked with the kernel-correctness follow-ons
on the board. -/

/-- Floor-division bound, positive divisor: `a ≤ ⌊b/c⌋ ↔ a·c ≤ b`. This is
verbatim the ub tighten step (`cand = (-r).fdiv (-ci)` with `b = -r`,
`c = -ci`). -/
theorem le_fdiv_iff_mul_le {b c : Int} (hc : 0 < c) (a : Int) :
    a ≤ b.fdiv c ↔ a * c ≤ b := by
  rw [Int.fdiv_eq_ediv_of_nonneg b hc.le]
  exact Int.le_ediv_iff_mul_le hc

/-- Ceiling-division bound, positive divisor: `⌈r/c⌉ ≤ x ↔ r ≤ c·x` —
verbatim the lb tighten step. -/
theorem cdivPos_le_iff {c r : Int} (hc : 0 < c) (x : Int) :
    cdivPos r c ≤ x ↔ r ≤ c * x := by
  unfold cdivPos
  constructor
  · intro h
    have h' : -x ≤ (-r).fdiv c := by omega
    have h'' : -x * c ≤ -r := (le_fdiv_iff_mul_le hc (-x)).mp h'
    linarith
  · intro h
    have h'' : -x * c ≤ -r := by linarith
    have := (le_fdiv_iff_mul_le hc (-x)).mpr h''
    omega

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
          -- xᵢ ≥ r/cᵢ: exact ℤ bound is `cdivPos r ci`, characterized by
          -- `cdivPos_le_iff` below (soundness AND tightness)
          let cand := cdivPos r ci
          if lb[i]!.all (· < cand) then
            lb := lb.set! i (some cand); changed := true
        else
          -- xᵢ ≤ r/cᵢ (cᵢ < 0): computed in positive-divisor form —
          -- `(-r).fdiv (-cᵢ)` equals `r.fdiv cᵢ` but is characterized
          -- verbatim by `le_fdiv_iff_mul_le` below
          let cand := (-r).fdiv (-ci)
          if ub[i]!.all (cand < ·) then
            ub := ub.set! i (some cand); changed := true
    if !changed then break
  return (lb, ub)

/-- Find with sign: returns `(root, flip)` where `value(i) = ±value(root)`.
Fueled — parent chains are strictly older indices only through unions, but
the fuel keeps a bookkeeping slip from hanging the tactic. -/
private def ufFind (uf : Array (Nat × Bool)) (i : Nat) : Nat × Bool := Id.run do
  let mut i := i
  let mut flip := false
  for _ in [0:uf.size + 1] do
    let (p, f) := uf[i]!
    if p == i then return (i, flip)
    flip := flip != f
    i := p
  return (i, flip)

/-- Parity union-find over unit ±-equalities — the `evars` analogue. -/
private def buildUF (n : Nat) (pmEqs : Array (Nat × Nat × Bool)) :
    Array (Nat × Bool) := Id.run do
  let mut uf : Array (Nat × Bool) := .ofFn (n := n) fun i => (i.1, false)
  for (i, j, neg) in pmEqs do
    let (ri, si) := ufFind uf i
    let (rj, sj) := ufFind uf j
    if ri != rj then
      -- value(i) = si·ri, value(j) = sj·rj, value(i) = (neg ? - : +)value(j)
      uf := uf.set! ri (rj, (si != sj) != neg)
    -- ri == rj with inconsistent signs ⟹ the context is infeasible; leave
    -- it to the omega leaf
  return uf

/-- The `collect_equivs` analogue (Z3 nla_core.cpp:516, exact mechanism):
octagon forms `±xᵢ ± xⱼ` (two entries, unit coefficients) whose derived
bounds pin them to zero yield ±-equalities. This is how Z3's `evars` sees
equalities asserted as inequality *pairs* (`x ≤ y` and `y ≤ x` never
produce an `Eq` hypothesis, but both bound the same octagon term). A
constraint `±T + k ≥ 0` contributes a lower/upper bound `∓k` on the term
`T`; best-lb ≥ 0 together with best-ub ≤ 0 forces `T = 0` in every model
(or infeasibility, where any merge is vacuously safe — every discharge
succeeds). Z3 restricts to unit coefficients; the direct-`Eq` feed in
`consOfHyp` additionally catches scaled forms, a strict superset in the
containment direction. -/
private def octagonEqs (cons : Array LinForm) : Array (Nat × Nat × Bool) := Id.run do
  -- key: (min var, max var, isSum); value: (best lb, best ub) of the term
  -- T = x_a - x_b (diff) or T = x_a + x_b (sum), a < b
  let mut bounds : Std.HashMap (Nat × Nat × Bool) (Option Int × Option Int) := {}
  for c in cons do
    if c.coeffs.size != 2 then continue
    let (i, ci) := c.coeffs[0]!
    let (j, cj) := c.coeffs[1]!
    if ci.natAbs != 1 || cj.natAbs != 1 then continue
    let a := min i j
    let b := max i j
    let ca := if i == a then ci else cj
    let cb := if i == a then cj else ci
    let isSum := ca == cb
    -- form = ca·x_a + cb·x_b + k ≥ 0. With T as above: coefficient of T is
    -- `ca` for diff (ca = -cb) and `ca` for sum (ca = cb) — both cases
    -- read `ca·T + k ≥ 0`.
    let key := (a, b, isSum)
    let (lo, hi) := bounds.getD key (none, none)
    if ca == 1 then
      -- T ≥ -k
      let v := -c.k
      if lo.all (· < v) then bounds := bounds.insert key (some v, hi)
    else
      -- T ≤ k
      let v := c.k
      if hi.all (v < ·) then bounds := bounds.insert key (lo, some v)
  let mut out : Array (Nat × Nat × Bool) := #[]
  for (key, lo, hi) in bounds.toList do
    if lo.any (0 ≤ ·) && hi.any (· ≤ 0) then
      -- diff pinned to 0 ⟹ x_a = x_b (neg = false); sum ⟹ x_a = -x_b
      out := out.push (key.1, key.2.1, key.2.2)
  return out

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
  return { atoms := s.atoms, index := s.index, lb, ub,
           uf := buildUF s.atoms.size (s.pmEqs ++ octagonEqs s.cons) }

/-- Derived bounds for an expr, `(lb?, ub?)`. -/
def OracleCtx.boundsOf (oc : OracleCtx) (e : Expr) : Option Int × Option Int :=
  match oc.index.get? e.consumeMData with
  | some i => (oc.lb[i]!, oc.ub[i]!)
  | none => (none, none)

/-- Derived ±-equivalence between two exprs (Z3's `evars`): `some true` when
`e = f` is derived, `some false` when `e = -f`, `none` otherwise. Syntactic
equality is the caller's fast path — this is for *distinct* spellings. -/
def OracleCtx.pmEquiv (oc : OracleCtx) (e f : Expr) : Option Bool := do
  let i ← oc.index.get? e.consumeMData
  let j ← oc.index.get? f.consumeMData
  let (ri, si) := ufFind oc.uf i
  let (rj, sj) := ufFind oc.uf j
  if ri != rj then none else some (si == sj)

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
