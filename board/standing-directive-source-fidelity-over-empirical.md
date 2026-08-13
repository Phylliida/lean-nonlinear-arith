## Standing directive: source-fidelity over empirical confirmation

(Danielle, 2026-07-26) Where we lean on an *equivalent* engine instead of
porting Z3's ("grind's Buchberger ⊇ Z3's throttled PDD, checked by the
nla-16 harness"; "ring_nf ≈ emonics"), prefer making it THE SAME — we
have the source code. Consequences: nla-07b's meta-Buchberger should be a
faithful port of the `nla_grobner` pipeline (its five consumers:
conflict, propagate_fixed, propagate_factorization, propagate_gcd_test,
propagate_quotients), after which grind demotes to an auxiliary layer and
containment no longer rests on a reading of grind's internals; nla-21's
shared-atom-space design should reconsider the emonics port likewise.
The octagon `collect_equivs` port (2026-07-26) is the template: read the
site, match the mechanism, keep any strict superset only where the
containment direction is free.

