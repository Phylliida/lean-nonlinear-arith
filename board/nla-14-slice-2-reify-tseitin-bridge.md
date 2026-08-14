## nla-14 Slice 2 `done` (2026-08-14) — reify + Tseitin + bridge

Build green (7614 jobs, full workspace), pins green, axioms
propext/choice/Quot.sound on the new trusted lemmas. Commits: the
Slice-1.5 trusted rework + this slice.

**Trusted additions (Assemble.lean, all reviewed against the design):**
- `BoolDef.tru`/`fls` (NNF/empty-clause support), `clauseForm` +
  `clauseHolds_iff_eval` (the or-chain bridge).
- The named one-step unfoldings of `boolDefHolds` (and/or/neg/tru/fls)
  + `litHolds_bool`/`interp_bool` (the boundary lemmas — WF-compiled
  `boolDefHolds` has NO kernel defeq, so bridges rewrite via these).
- `proxyLeavesLT` + `boolDefsOrdered(From)` (the emission-order
  invariant, decide-grade) + `boolDefHolds_irrel` (bound invisible when
  covering) + `boolDefHolds_evalLitHolds` (THE boundary bridge: at an
  ordered table, `boolDefHolds bound d ↔ BoolDef.eval (litHolds) d` —
  this is what lets per-proxy Iffs compose WITHOUT unfolding shared
  defs; R-i's Tseitin sharing survives into proof terms).
- **normNeg (real catch, mid-slice): the taut truth-table over
  `Literal` leaves treated `⟨b,false⟩`/`⟨b,true⟩` as INDEPENDENT atoms
  — `l ∨ ¬l`-shaped forms (exactly what definitional clauses become
  after one-level inlining) failed to check.** `BoolDef.normNeg`
  canonicalizes polarity inside `taut`; soundness now
  `taut_sound_consistent` with a PER-LEAF consistency hypothesis
  (junk literals are NOT polarity-consistent — `litHolds` poisons both
  polarities — so the quantifier must be leaf-local);
  `litHolds_negate` (consistent on decodable literals) +
  `clauseHolds_iff_evalNorm` (the walk's precheck decodability makes
  normNeg invisible at input clauses).

**The frontend (`Tactic/NonlinearArith.lean`, ~1200 lines, untrusted
meta — kernel re-checks every produced term):**
- `reifyArith` (Expr → MPoly over the var table; ℤ/ℕ/ℝ vars, opaque
  subterms → fresh vars (z3's uninterpreted-content treatment, review
  R-iii), div/mod HARD FAIL = the L1-owned invariant, §2.7),
  `reifyCmp` (six comparisons → 3 atoms per difference-poly,
  polarity-folded — lt/ge, gt/le, eq/ne SHARE atoms like z3's
  manager), `reifyProp` (NNF with the EXPANDED prop threaded —
  comparison leaves keep the user's text), `clausify`/`tseitinLit`/
  `mkProxy` (proxies with NORMALIZED defs — the pairing invariant),
  nat nonneg clauses (decision 2).
- Bridges, all term-mode: `mkLitIff` (holds_single + align-Eq
  `Iff.of_eq ∘ congrArg` + `sub_*` zero-shifts + cast links — the only
  sandbox is `mkAlign`'s `simp [evalP, evalM]; push_cast; ring`,
  Refute-idiom), `mkProxyIff`/`mkFormIff` (eval-level congruences +
  the boundary lemmas), `mkDefClauseBridge` (taut_sound + the subst
  link `mkDefLink` + `clauseHolds_iff_evalNorm`), `mkRootBridge`
  (mkNnfIff + the ElimTree plan evaluator — ∃-intro through
  Or.elim/And.proj), `buildDispatch` (the `∀ C ∈ Cs` lambda via
  `List.mem_cons` Iffs + congrArg transport).
- `toRefutationGoal` (the `nla_frontend` dev tactic): `Γ ⊢ G` →
  `∀ ρ, (integrality hyps: ∃ n : ℤ, ρ i = ↑n per ℤ/ℕ slot, BEFORE the
  clause hyp — the 12e convention) → (∀ C ∈ Cs, clauseHolds ρ atoms C)
  → False` — exactly the walk's shape, left as the main goal.

**Pins (NonlinearArithTests) — each closes the produced refutation goal
BY HAND, so the kernel checks the full bridge chain:** sq over ℝ
(user syntax), the two-literal disjunctive clause, the Int
integrality-hyp path, **the proxy path** (`(x ≥ 1 ∧ x < 1) ∨ x*x < 0`:
proxy bvar 3 over the SHARED lt-atom bvar 1 — the z3 atom-sharing pin
too — three definitional clauses + root, walked by hand), and the
Not-Not negated-goal path.

**Traps for the books (all hit this slice):**
- **`→` binds tighter than `↔`** — `H → A ↔ B` parses as
  `(H → A) ↔ B`. Parenthesize trailing Iffs. (Cost: a full afternoon
  of phantom intro failures — the "auto-introduced ∀" hallucination
  was the misparsed goal all along.)
- `mkAppM` takes EXPLICIT args only; implicit-operand lemmas need
  `mkAppOptM` with pinned positions — INCLUDING type-level implicits
  (`some (mkConst ``Real)` for `R`, else "failed to synthesize
  IntCast ?R" at TACTIC RUNTIME, not at the call site).
- `Membership.mem`'s value args are (container, elem) — mem #[Cs, C].
- `List.Mem` on `[]` is not defeq-`False` under mkAppM's isDefEq —
  eliminate via `List.not_mem_nil` (mkAppM' the application);
  cons-case via the `List.mem_cons` Iff (Walk.memChain idiom).
- `Or.elim`/`False.elim`: pin ALL implicit binders via mkAppOptM —
  mkAppM leaves the motive an mvar → "result contains metavariables".
- Sandbox tactics run on the CURRENT goal unless you setGoals to the
  sandbox mvar first (mkAlign lost an afternoon to this too — the
  probe closed the standalone goal while the sandbox simp'd the
  user's).
- Structure field groups need parens; `let (a,b) ← match` not
  `:= ← match`; `return` in a nested match arm exits the OUTER fn;
  multi-statement `if` branches in do need explicit `do`.

**Next: Slice 3** — quote+orchestrate: the solver run in TacticM
(`Solver.run'` is pure), snapshot quoting (the five quoters incl. the
`.bool` atom arm), the proxy-def patch into the extracted snapshot
POST-reorder (bvar-keyed defs are reorder-stable; the walk's atom
table is the internal-order snapshot), SAT-exit model display
(decision 4, skipping proxy vars), and the Slice-3 pins: the same
drivers through search → trace → checked theorem with NO hand-written
snapshot, plus the D-1 disjunctive driver with a proxy in a LEARNED
clause and the foreign-`.arith`-with-proxy sound-rejection probe.
