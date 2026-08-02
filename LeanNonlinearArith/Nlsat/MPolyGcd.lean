import LeanNonlinearArith.Nlsat.MPolyZp

/-!
# nla-12d.1b-ii/iv — the multivariate gcd cluster (z3 `polynomial.cpp` @ **4.12.5**)

One mutually-recursive cluster, mirroring z3's manager (all `partial`;
termination arguments — content/var-set decrease — registered with
nla-31):

* `iccpM` (:3496) — integer content + content + primitive part w.r.t.
  `x`, with z3's quick-filter optimization; the content is a `gcdM`
  chain over the coefficient polys.
* `gcdM` (:4395) — the top-level ladder: zero/eq/const cases →
  `gcdContentM` (a var occurring in only one side) → same-var-set:
  ℤ mode ⇒ `uniModGcd` (univariate) / `modGcd` (multivariate, falling
  back to `gcdPrsM` on `sparse_mgcd_failed`); Zp mode ⇒ `gcdPrsM`.
  (`m_use_prs_gcd = false` hardcoded at :2340 — the modular routes are
  the live ones.)
* `gcdContentM` (:3671), `gcdPrsM` (:3598) — subresultant PRS gcd
  (also the Zp-mode route and the universal fallback).
* `euclidGcdM` (:3693) — Zp-mode gcd (zero/eq/const preamble then
  `gcdPrsM`; z3's univariate SASSERT is documentation — mod_gcd_rec
  calls it on multivariate contents, and the body handles it).
* `uniModGcd` (:3812) — big-prime loop with Zp `euclidGcdM`,
  `mkGlexMonic`, CRA accumulation, `pp` candidate + trial `divides`;
  **quirk ported verbatim:** on a constant modular image it returns
  `q = lc_g` when `d_a = 1` (the "GCD is one" branch :3869-3873),
  even when `lc_g ≠ 1` — e.g. gcd(2x+1, 2x+3) yields 2. This is an
  upstream edge-case quirk (reachable only when the true gcd is 1 but
  the leading coefficients share a factor); ported as-is per the
  mechanism-fidelity rule, documented here.
* `modGcd` (:4300s) + `modGcdRec` (:4119) — the full multivariate
  modular gcd: bad-prime skips, min-degree-sorted var order, Zp
  evaluation with lc_g-val filtering, dense (Newton) or sparse
  (skeleton) interpolation, min_deg_q reset semantics, skeleton save
  on dense success, CRA accumulation with the glex-max discard rule,
  candidate normalize + lc divisibility + `divides` verification;
  prime exhaustion ⇒ `gcdPrsM`.
  **z3's per-manager interpolator/skeleton tables are per-`modGcd`
  state here** (z3 resets skeletons per mod_gcd call; the
  interpolators' first iteration always resets on `min_deg_q =
  UINT_MAX` — stale cross-call state is unobservable).
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

/-- Interpolator state for `modGcdRec`'s loop: dense Newton or sparse
(skeleton-driven) — fixed per call (the skeleton is looked up once). -/
inductive InterpState (c : ZpCtx)
  | dense (ni : NewtonInterpolator c)
  | sparse (si : SparseInterpolator c)

namespace InterpState

def inputs {c : ZpCtx} : InterpState c → Array Int
  | .dense ni => ni.inputs
  | .sparse si => si.inputs

end InterpState

/-- Candidate verification for `modGcdRec` (:4240-4259). -/
inductive CandCheck
  | accept (r : MPoly)          -- divides-verified: r = ci_g·c_g·C
  | fallbackContent (r : MPoly) -- min_deg_q == 0: r = ci_g·c_g
  | reject                      -- failed; dense loops on, sparse throws
deriving Inhabited

mutual

/-- z3 `iccp(p, x, i, c, pp)` (:3496). The quick filter: a monomial
that is purely `x^k` with no other `m·x^k` partner forces `c = 1`. -/
partial def iccpM (mode : NumMode) (p : MPoly) (x : Var) : Int × MPoly × MPoly :=
  match p with
  | [] => (0, MPoly.ofInt (mode.norm 1), [])
  | [(a, [])] => (a, MPoly.ofInt (mode.norm 1), MPoly.ofInt (mode.norm 1))
  | _ =>
    let d := p.degreeIn x
    if d == 0 then
      let (i, pp) := p.icStrip mode
      (i, MPoly.ofInt (mode.norm 1), pp)
    else
      -- filter pass: count pure-x^k monomials (+1) vs mixed (+2)
      let (filt, powers) := Id.run do
        let mut filt : Array Nat := Array.replicate (d + 1) 0
        let mut powers : Array Nat := #[]
        for (_, m) in p do
          let k := m.degreeIn x
          if filt[k]! == 0 then powers := powers.push k
          if m.length == (if k > 0 then 1 else 0) then
            filt := filt.set! k (filt[k]! + 1)
          else
            filt := filt.set! k (filt[k]! + 2)
        return (filt, powers)
      if powers.any (fun k => filt[k]! == 1) then
        let (i, pp) := p.icStrip mode
        (i, MPoly.ofInt (mode.norm 1), pp)
      else
        let (i, pp) := p.icStrip mode
        -- c := gcd of the coefficient polys of x^k
        let cs := (pp.coeffsIn x)
        let c0 := cs[powers[0]!]!
        let c := if powers.size == 1 then c0 else gcdChainCoeffs mode cs powers c0 1
        if c.asConst?.isSome then (i, MPoly.ofInt (mode.norm 1), pp)
        else
          let c := c.flipSignIfLmNeg
          (i, c, pp.exactDiv c mode)

/-- `iccpM`'s coefficient-gcd chain with z3's const early exit
(:3557-3563). -/
partial def gcdChainCoeffs (mode : NumMode) (cs : Array MPoly) (powers : Array Nat)
    (acc : MPoly) (j : Nat) : MPoly :=
  if j ≥ powers.size then acc
  else
    let acc' := gcdM mode acc cs[powers[j]!]!
    if acc'.asConst?.isSome then acc'
    else gcdChainCoeffs mode cs powers acc' (j + 1)

/-- z3 `gcd_content(u, x, v, r)` (:3671): `gcd(content(u,x)·i_u, v)`. -/
partial def gcdContentM (mode : NumMode) (u : MPoly) (x : Var) (v : MPoly) : MPoly :=
  let (i_u, c_u, _) := iccpM mode u x
  gcdM mode (MPoly.smulTermM mode i_u [] c_u) v

/-- z3 `gcd_prs(u, v, x, r)` (:3598): subresultant PRS gcd. -/
partial def gcdPrsM (mode : NumMode) (u v : MPoly) (x : Var) : MPoly :=
  let (u, v) := if u.degreeIn x < v.degreeIn x then (v, u) else (u, v)
  let (i_u, c_u, pp_u0) := iccpM mode u x
  let (i_v, c_v, pp_v0) := iccpM mode v x
  let d_r := gcdM mode c_u c_v
  let d_a := NumMode.gcd i_u i_v
  prsLoop mode x d_r d_a pp_u0 pp_v0 (MPoly.ofInt (mode.norm 1)) (MPoly.ofInt (mode.norm 1))

/-- `gcdPrsM`'s main loop (:3628-3670). -/
partial def prsLoop (mode : NumMode) (x : Var) (d_r : MPoly) (d_a : Int)
    (pp_u pp_v g h : MPoly) : MPoly :=
    let delta := pp_u.degreeIn x - pp_v.degreeIn x
    let rem := pp_u.exactPseudoRemainder pp_v x mode
    if rem.isZero then
      let pp_v' := pp_v.flipSignIfLmNeg
      let (_, _, r) := iccpM mode pp_v' x   -- pp(pp_v, x)
      MPoly.smulTermM mode d_a [] (MPoly.mulM mode d_r r)
    else if rem.asConst?.isSome then
      MPoly.smulTermM mode d_a [] d_r
    else
      let pp_u' := pp_v
      let pp_v1 := rem.exactDiv g mode
      let pp_v' := (List.range delta).foldl (fun acc _ => acc.exactDiv h mode) pp_v1
      let g' := (pp_u'.coeffsIn x)[pp_u'.degreeIn x]!
      let new_h0 := (List.range delta).foldl (fun acc _ => MPoly.mulM mode acc g')
        (MPoly.ofInt (mode.norm 1))
      let new_h := if delta > 1 then
        (List.range (delta - 1)).foldl (fun acc _ => acc.exactDiv h mode) new_h0
      else new_h0
      prsLoop mode x d_r d_a pp_u' pp_v' g' new_h

/-- z3 `euclid_gcd` (:3693): Zp-mode gcd — zero/eq/const preamble
(identical to `gcdM`'s) then `gcdPrsM` on the max var. -/
partial def euclidGcdM (c : ZpCtx) (u v : MPoly) : MPoly :=
  if u.isZero then v.flipSignIfLmNeg
  else if v.isZero then u.flipSignIfLmNeg
  else if u == v then u.flipSignIfLmNeg
  else if u.asConst?.isSome || v.asConst?.isSome then
    MPoly.ofInt (NumMode.norm (some c) (NumMode.gcd v.ic u.ic))
  else gcdPrsM (some c) u v (u.maxVar.get!)

/-- z3 `iccp_ZpX(p, x, ci, c, pp)` (:3919): content/pp viewed in
`Zp[y…][x]` — buckets of coefficient polys keyed by x-stripped
monomial, gcd via `euclidGcdM`. -/
partial def iccpZpXM (c : ZpCtx) (p : MPoly) (x : Var) : Int × MPoly × MPoly :=
  match p with
  | [] => (0, MPoly.ofInt 1, [])
  | [(a, [])] => (a, MPoly.ofInt 1, MPoly.ofInt 1)
  | _ =>
    let d := p.degreeIn x
    if d == 0 then
      let (ci, pp) := p.icStrip (some c)
      (ci, MPoly.ofInt 1, pp)
    else
      let minDeg := p.foldl (fun acc (_, m) => min acc (m.degreeIn x)) d
      if minDeg > 0 then
        -- every monomial contains x: divide out x^minDeg and recurse
        let xmin := MPoly.ofVarPow x minDeg
        let newP := p.exactDiv xmin (some c)
        let (ci, c', pp) := iccpZpXM c newP x
        (ci, MPoly.mulM (some c) xmin c', pp)
      else
        -- cheap check: some x-free monomial without an m·x^k partner ⇒ c = 1
        let noX : List Monomial := Id.run do
          let mut out : List Monomial := []
          for (_, m) in p do
            if m.degreeIn x == 0 && !out.contains m then
              out := out ++ [m]
          return out
        let numUnmarked := Id.run do
          let mut marks := noX
          let mut n := 0
          for (_, m) in p do
            if m.degreeIn x != 0 then
              let sm := m.erase x
              if marks.contains sm then
                n := n + 1
                marks := marks.erase sm
          return n
        if numUnmarked < noX.length then
          let (ci, pp) := p.icStrip (some c)
          (ci, MPoly.ofInt 1, pp)
        else
          -- expensive case: bucket coefficient polys by stripped monomial
          let (ci, pp) := p.icStrip (some c)
          let buckets : Array (Monomial × MPoly) := Id.run do
            let mut out : Array (Monomial × MPoly) := #[]
            for (a, m) in pp do
              let k := m.degreeIn x
              let key := m.erase x
              let term : MPoly := MPoly.smulTermM (some c) a [] (MPoly.ofVarPow x k)
              match out.findIdx? (·.1 == key) with
              | some i =>
                out := out.set! i (key, MPoly.addM (some c) out[i]!.2 term)
              | none =>
                out := out.push (key, term)
            return out
          let rec gcdChain (acc : MPoly) (i : Nat) : MPoly :=
            if i ≥ buckets.size then acc
            else
              let acc' := euclidGcdM c acc buckets[i]!.2
              if acc'.asConst?.isSome then acc'
              else gcdChain acc' (i + 1)
          let g := gcdChain buckets[0]!.2 1
          if g.asConst?.isSome then (ci, MPoly.ofInt 1, pp)
          else (ci, g, pp.exactDiv g (some c))

/-- z3 `primitive_ZpX` (:4090) wrapper. -/
partial def primitiveZpXM (c : ZpCtx) (p : MPoly) (x : Var) : MPoly :=
  (iccpZpXM c p x).2.2

/-- z3 `uni_mod_gcd` (:3812). ℤ mode. See the header for the
constant-image quirk (ported verbatim). -/
partial def uniModGcd (u v : MPoly) : MPoly := Id.run do
  let x := u.maxVar.get!
  let (c_u, pp_u) := u.icStrip
  let (c_v, pp_v) := v.icStrip
  let d_a := NumMode.gcd c_u c_v
  let d_u := pp_u.degreeIn x
  let d_v := pp_v.degreeIn x
  let lc_u := ((pp_u.coeffsIn x)[d_u]!.asConst?.getD 0)
  let lc_v := ((pp_v.coeffsIn x)[d_v]!.asConst?.getD 0)
  let lc_g := NumMode.gcd lc_u lc_v
  let mut cStar : MPoly := []
  let mut bound : Int := 0
  let mut haveStar := false
  for i in [:ZPoly.bigPrimes.size] do
    let p := ZPoly.bigPrimes[i]!
    let zp : ZpCtx := ⟨p⟩
    let uZp := MPoly.managerNormalize (some zp) pp_u
    let vZp := MPoly.managerNormalize (some zp) pp_v
    if uZp.degreeIn x < d_u || vZp.degreeIn x < d_v then
      continue   -- bad prime, leading coefficient vanished
    let q0 := euclidGcdM zp uZp vZp
    let q := MPoly.smulTermM (some zp) lc_g [] (MPoly.mkGlexMonic zp q0)
    if q.asConst?.isSome then
      -- "GCD is one" branch — quirk (see header): q = lc_g when d_a = 1
      return if d_a == 1 then q else MPoly.ofInt d_a
    if !haveStar then
      cStar := q
      bound := p
      haveStar := true
    else
      let mq := (q.glexMaxTerm.get!).2
      let mc := (cStar.glexMaxTerm.get!).2
      if Monomial.gradedLexCompare mq mc == .lt then
        cStar := q   -- discard image affected by unlucky primes
        bound := p
      else
        let (r, b) := craCombineImagesM q p cStar bound
        cStar := r
        bound := b
    let candidate := MPoly.managerNormalize none cStar
    let lcCandidate := (candidate.glexMaxTerm.get!).1
    if lc_g % lcCandidate == 0 &&
       candidate.divides pp_u && candidate.divides pp_v then
      return (MPoly.smulTerm d_a [] candidate).flipSignIfLmNeg
  -- not enough primes: fallback to prs
  return gcdPrsM none u v x

/-- z3's candidate block (:4240-4259): primitive/normalize, `divides`
verification, min_deg_q == 0 fallback. -/
partial def checkCandidate (c : ZpCtx) (x : Var) (ci_g : Int) (c_g pp_u pp_v : MPoly)
    (minDegQ : Nat) (h : MPoly) : CandCheck :=
  let cc := if h.degreeIn x > 0 then primitiveZpXM c h x
    else MPoly.managerNormalize (some c) h
  if cc.divides pp_u (some c) && cc.divides pp_v (some c) then
    .accept (MPoly.smulTermM (some c) ci_g [] (MPoly.mulM (some c) c_g cc))
  else if minDegQ == 0 then
    .fallbackContent (MPoly.smulTermM (some c) ci_g [] c_g)
  else .reject

/-- z3 `mod_gcd_rec` (:4119). Zp mode; `none` = `sparse_mgcd_failed`
(propagates to `gcdM`'s `gcdPrsM` fallback). The `peek_fresh` values
come from a deterministic upward scan (registered output-independence
argument — see MPolyZp.lean's header). -/
partial def modGcdRec (c : ZpCtx) (u v : MPoly) (idx : Nat) (vars : Array Var)
    (skeletons : Array (Option Skeleton)) : Option MPoly × Array (Option Skeleton) :=
  if idx == vars.size - 1 then
    (some (euclidGcdM c u v), skeletons)
  else
    let x := vars[idx]!
    let (ci_u, c_u, pp_u) := iccpZpXM c u x
    let (ci_v, c_v, pp_v) := iccpZpXM c v x
    let lc_u := MPoly.lcGlexZpX pp_u x
    let lc_v := MPoly.lcGlexZpX pp_v x
    let ci_g := NumMode.gcd ci_u ci_v
    let c_g := euclidGcdM c c_u c_v
    let lc_g := euclidGcdM c lc_u lc_v
    loop x ci_g c_g lc_g pp_u pp_v 4294967295 0
      (match skeletons[idx]! with
       | none => InterpState.dense (NewtonInterpolator.reset (c := c))
       | some sk => InterpState.sparse (SparseInterpolator.ofSkeleton (c := c) sk))
      skeletons
where
  /-- First value at or above `fromN`, not among the interpolator's
  inputs, with `lc_g(val) ≠ 0` (z3's inner peek loop :4174-4181). -/
  peek (st : InterpState c) (lc_g : MPoly) (x : Var) (fromN : Nat) : Int × Nat :=
    let v := Id.run do
      let mut v := (fromN : Int)
      while st.inputs.contains v do
        v := v + 1
      return v
    if MPoly.univEval (some c) lc_g x v != 0 then (v, v.natAbs + 1)
    else peek st lc_g x (v.natAbs + 1)
  /-- The sampling loop (:4172-4268). `minDegQ` starts at UINT_MAX. -/
  loop (x : Var) (ci_g : Int) (c_g lc_g pp_u pp_v : MPoly)
      (minDegQ freshFrom : Nat) (st : InterpState c)
      (sks : Array (Option Skeleton)) : Option MPoly × Array (Option Skeleton) :=
    let (val, freshFrom') := peek st lc_g x freshFrom
    let lc_g_val := MPoly.univEval (some c) lc_g x val
    let u1 := MPoly.substitute1 (some c) pp_u x val
    let v1 := MPoly.substitute1 (some c) pp_v x val
    match modGcdRec c u1 v1 (idx + 1) vars sks with
    | (none, sks1) => (none, sks1)
    | (some q0, sks1) =>
      let q := MPoly.smulTermM (some c) lc_g_val [] (MPoly.mkGlexMonic c q0)
      let degQ := match q.maxVar with
        | none => 0
        | some y => q.degreeIn y
      if degQ > minDegQ then
        loop x ci_g c_g lc_g pp_u pp_v minDegQ freshFrom' st sks1
      else
        match st with
        | .dense ni =>
          let (minDegQ', ni') :=
            if degQ < minDegQ then (degQ, NewtonInterpolator.reset.add val q)
            else (minDegQ, ni.add val q)
          let h := ni'.mkPoly x
          if MPoly.lcGlexZpX h x == lc_g then
            match checkCandidate c x ci_g c_g pp_u pp_v minDegQ' h with
            | .accept r =>
              -- save the skeleton on dense success (m_use_sparse_gcd)
              (some r, sks1.set! idx (some (Skeleton.build h x)))
            | .fallbackContent r => (some r, sks1)
            | .reject =>
              loop x ci_g c_g lc_g pp_u pp_v minDegQ' freshFrom' (.dense ni') sks1
          else
            loop x ci_g c_g lc_g pp_u pp_v minDegQ' freshFrom' (.dense ni') sks1
        | .sparse si =>
          let si0 := if degQ < minDegQ then si.reset else si
          match si0.add val q with
          | none => (none, sks1)   -- sparse_mgcd_failed
          | some si' =>
            let minDegQ' := min minDegQ degQ
            if !si'.ready then
              loop x ci_g c_g lc_g pp_u pp_v minDegQ' freshFrom' (.sparse si') sks1
            else
              match si'.mkPoly with
              | none => (none, sks1)   -- sparse_mgcd_failed
              | some h =>
                match checkCandidate c x ci_g c_g pp_u pp_v minDegQ' h with
                | .accept r => (some r, sks1)
                | .fallbackContent r => (some r, sks1)
                | .reject => (none, sks1)   -- sparse_mgcd_failed

/-- z3 `mod_gcd` (:4300s). ℤ-mode shell; `none` =
`sparse_mgcd_failed` from the recursion (the caller falls back to
`gcdPrsM`); prime exhaustion falls back to `gcdPrsM` internally. -/
partial def modGcd (u v : MPoly) : Option MPoly := Id.run do
  -- min-degree-sorted shared var list
  let uds := u.varDegrees
  let vds := v.varDegrees
  let vars : Array Var := (uds.mapIdx fun i (x, du) =>
      (x, min du vds[i]!.2)).qsort (fun (_, d1) (_, d2) => d1 < d2) |>.map (·.1)
  let (c_u, pp_u) := u.icStrip
  let (c_v, pp_v) := v.icStrip
  let d_a := NumMode.gcd c_u c_v
  let lc_u := (pp_u.glexMaxTerm.get!).1
  let lc_v := (pp_v.glexMaxTerm.get!).1
  let lc_g := NumMode.gcd lc_u lc_v
  let mut cStar : MPoly := []
  let mut bound : Int := 0
  let mut haveStar := false
  for i in [:ZPoly.bigPrimes.size] do
    let p := ZPoly.bigPrimes[i]!
    let zp : ZpCtx := ⟨p⟩
    let uZp := MPoly.managerNormalize (some zp) pp_u
    let vZp := MPoly.managerNormalize (some zp) pp_v
    if uZp.length != pp_u.length || vZp.length != pp_v.length then
      continue   -- bad prime, coefficient(s) vanished
    let skeletons : Array (Option Skeleton) := Array.replicate vars.size none
    let (q0?, _) := modGcdRec zp uZp vZp 0 vars skeletons
    match q0? with
    | none => return none
    | some q0 =>
      let q := MPoly.smulTermM (some zp) lc_g [] (MPoly.mkGlexMonic zp q0)
      if q.asConst?.isSome then
        return some (MPoly.ofInt d_a)   -- modular gcd is one
      if !haveStar then
        cStar := q
        bound := p
        haveStar := true
      else
        let mq := (q.glexMaxTerm.get!).2
        let mc := (cStar.glexMaxTerm.get!).2
        if Monomial.gradedLexCompare mq mc == .lt then
          cStar := q
          bound := p
        else
          let (r, b) := craCombineImagesM q p cStar bound
          cStar := r
          bound := b
      let candidate := MPoly.managerNormalize none cStar
      let lcCandidate := (candidate.glexMaxTerm.get!).1
      if lc_g % lcCandidate == 0 &&
         candidate.divides pp_u && candidate.divides pp_v then
        return some (MPoly.smulTerm d_a [] candidate).flipSignIfLmNeg
  -- not enough primes: fallback to prs
  return some (gcdPrsM none u v (u.maxVar.get!))

/-- z3 `gcd(u, v, r)` (:4395) — the top-level ladder. -/
partial def gcdM (mode : NumMode) (u v : MPoly) : MPoly :=
  if u.isZero then v.flipSignIfLmNeg
  else if v.isZero then u.flipSignIfLmNeg
  else if u == v then u.flipSignIfLmNeg
  else if u.asConst?.isSome || v.asConst?.isSome then
    MPoly.ofInt (mode.norm (NumMode.gcd v.ic u.ic))
  else
    let uds := u.varDegrees
    let vds := v.varDegrees
    let sz := min uds.size vds.size
    -- search for a var occurring in only one of u, v (:4430-4472)
    match (uds.toList.zip vds.toList).find? (fun (a, b) => a.1 != b.1) with
    | some (a, b) =>
      if a.1 < b.1 then gcdContentM mode u a.1 v else gcdContentM mode v b.1 u
    | none =>
      if uds.size > vds.size then gcdContentM mode u uds[sz]!.1 v
      else if vds.size > uds.size then gcdContentM mode v vds[sz]!.1 u
      else
        let x := uds[sz - 1]!.1   -- max var (same var set)
        match mode with
        | some c => gcdPrsM (some c) u v x
        | none =>
          if uds.size == 1 then uniModGcd u v
          else
            match modGcd u v with
            | some r => r
            | none => gcdPrsM none u v x

end

end LeanNonlinearArith.Nlsat
