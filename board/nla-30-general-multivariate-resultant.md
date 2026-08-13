## nla-30 `todo` — general multivariate resultant (deferred; Danielle 2026-07-31)

The multiplication-matrix elimination route (resultantElim in 12b-i,
extended to mk_binary's shapes in nla-29) covers every reachable call
site: the second argument is always a univariate defining poly. z3's
general multivariate resultant (`polynomial.cpp` manager::resultant)
also accepts multivariate second arguments; no reachable call site
produces those today, but Tier B (full-degree projection, nla-11/nla-13)
and any future elimination shape may. When the first such call site
lands, port the general mechanism (or a value-exact equivalent with a
provably identical capability set — the bar Danielle set for the 29.1
decision). Until then the extended route stands on the
capability-identity argument: both routes are exact on every reachable
input.

