- **nla-01** `done` **S1 statement spike.** `Projection/S1Statement.lean`
  elaborates clean, first pass: psc chains defined as explicit Sylvester-minor
  determinants (mathlib has `resultant`/`sylvester` but no subresultants — ours
  to build), `ParamPoly k = Polynomial (MvPolynomial (Fin k) ℝ)`, conclusion
  packaged as a `Delineation` structure (continuous strictly-ordered root
  functions, constant membership). No mathlib gaps blocking the statement.
  Statement may still evolve during the nla-11 proof campaign.
