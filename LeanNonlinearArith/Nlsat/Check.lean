import LeanNonlinearArith.Nlsat.Check.Semantics
import LeanNonlinearArith.Nlsat.Check.Discharge

/-!
# nla-19a — the checker, v0 (TRUSTED layer)

The discharge side of the trace contract (`Nlsat/Trace.lean`). No
`assume`/`admit`/`external_body` anywhere; per-step discharge lemmas
compose into the learned-clause theorem (the F-companion architecture:
term-producing, nla-09 house style).

Split at F5 (R8 of design review 3):
- `Check/Semantics.lean` — the semantic layer (`evalM`/`evalP` +
  homomorphism suites, `coeffsOf` univariate extraction, atom
  semantics `IneqAtom.Holds`/`RootAtom.Holds`, Thom region defs).
- `Check/Discharge.lean` — the per-step discharge theorems
  (linearRoot/Thom/cellBound/rootGeneric + the `discPolyOf`/
  `pDiffPolyOf` reconstruction bridges + the coeffsOf↔coeffsIn
  bridge).

Canonicity: `evalM_erase` needs `Monomial.Canon` (the erase/degreeIn
identity fails on duplicate keys); the checker verifies canonicity of
payload data by `decide` at its boundary (F4 parse-level rejection).
-/
