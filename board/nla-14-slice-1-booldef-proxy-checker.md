## nla-14 Slice 1 `done` (2026-08-13 eve) — Tseitin proxy checker support

**POST-REVIEW AMENDMENT (same evening,
board/nla-14-slice-1-design-review.md, R-i):** the "flattened,
arith-atom-leaves-only, non-recursive" design below was STRUCK at the
design review — flattened defs reintroduce the exponential blowup
Tseitin exists to avoid (def data on shared circuits + truth tables on
inlined subtrees). As LANDED: `BoolDef` leaves may reference other
proxies; `boolDefHolds` is fuel-bounded table recursion (fuel =
`atoms.size + 1`; cycles poison to `False`). Consequence: no kernel
defeq through proxies (WF-compiled) — bridges rewrite via equation
lemmas.

Per the plan (board/nla-14-plan.md, decision 1: full Boolean structure
via Tseitin proxies, z3's mechanism, performance parity). Build green
(7612 jobs), commit `72c3b6a`. Axioms on all new soundness lemmas:
propext/choice/Quot.sound only (printed).

**Trusted additions (all additive — every existing snapshot/test
elaborates untouched):**
- `Types.lean`: `BoolDef` (lit/and/or/neg over `Literal` leaves —
  arith-atom leaves only, flattened at emission, non-recursive);
  `Atom.bool (d : BoolDef)`; `Literal` hoisted above `Atom` (pure
  reorder); `Atom.maxVar (.bool) = none` (z3's bool vars have no
  `max_var`). Module doc updated.
- `Check/Semantics.lean`: `Atom.Holds (.bool) = False` — junk, the
  sound direction; the table-free signature can't see def leaves, so
  the REAL proxy semantics lives one level up (documented).
- `Assemble.lean`: `arithLitHolds` (leaf semantics: `.ineq`/`.root`
  only, everything else poisons to `False`); `boolDefHolds`;
  `interp`/`litHolds` gain the proxy arm; `litSatI_interp` re-proved
  (`cases a` first). `clauseDecodable`/`precheck` UNCHANGED — a
  `some (.bool _)` slot was already "decodable"; junk leaves degrade
  at discharge, never unsound.
- The reflection: `BoolDef.eval`/`evalB`/`leaves`/`allAssign`/
  `assignGet` (recursive, not `find?`, for clean simp), `taut` +
  `taut_sound`, `conseq` + `conseq_sound` — the upRefutes idiom
  (kernel-computable check + soundness lemma). Truth-table over the
  dedup'd leaves; Tseitin definitional clauses carry ≤ a handful.
- Churn arms (all junk/unreachable-defensive, all commented): Solver
  ×7 (`degreeAtom` 0, `atomIsEq` false, `value` .undef, infeasible
  intervals `pure none` = the 29.5 abort image, `isFullDimLit` true,
  census `[]`, `renameAtoms` unchanged — defs reference bvars, not
  vars); Refute ×5 (`atomVars` [], both extractFacts `[]` — proxy
  meaning unfolds at clause level, not per-literal; pd transport lane
  skips proxies — z3 `simplify` passes non-ineq literals through,
  nlsat_explain.cpp:1100-1103).

**Pins (AssembleTests):** decodability through the `.bool` arm (+ junk
slot control); interp unfolds the def (↔ `evalP < 0`); literal
polarity on proxies; junk-leaf poisoning; the three conjunction-proxy
Tseitin clause shapes + one disjunction-proxy shape (def inlined) all
`taut = true`; two non-tautologies rejected; `conseq` both directions;
**end-to-end: the definitional clause {¬b1, b0} over a proxy table
discharged by `taut_sound` alone.**

**Traps for the books:**
- `Classical` decidability in STATEMENTS: `open Classical` inside the
  namespace (the `classical` tactic doesn't help signatures);
  instance synthesis then picks `Classical.propDecidable` for
  `decide (τ l)`.
- `open LeanNonlinearArith.Kernel (evalP)` ≠ the right `evalP` — the
  MPoly evaluator is `Check.evalP` (Semantics.lean:77); the Kernel one
  is the certificate PairQ evaluator. The error was confusing
  ("Function expected ... has type ?m.1") because the unknown-constant
  fallback became an mvar.
- simp needs `Check.Atom.Holds` in the set before `holds_single_lt`
  fires (the Iff's head is `Atom.Holds`, not `IneqAtom.Holds`).
- `litSatI_interp`-style simp proofs over the atom table: `cases a`
  BEFORE `cases n`, or the fresh `match` arm on a variable atom sticks.

**NOT in this slice (unchanged by design):** `Walk.precheck`/
`nodeFSet`/`buildFSet` (bool vars flow through resolution as plain
literals; RUP is interpretation-agnostic); the walk's goal shape;
`s.refutation` extraction (solver bool vars stay `none` search-side —
the Slice-3 frontend patches defs into the extracted snapshot).
`.arith`-marker clauses stay arith-literal-only by construction
(explain never sees proxies); a foreign trace violating that fails at
`proveClauseSat` — sound rejection, pin-worthy at Slice 3/4.

**Next: Slice 2** — reify+Tseitin+bridge (Expr→MPoly/Atom parser,
var table, Tseitin clausification with `mkBoolVar` slots, per-clause
bridges via `conseq_sound`, integrality hyps, byContradiction
assembly). The slice's first recon question: where the frontend's
proxy-def patch meets `heuristicReorder` (defs reference bvars —
stable across the var reorder — but the atom-table PATCH must happen
post-extraction, on the internal-order snapshot; recorded in the
plan's component-0/1 boundary).
