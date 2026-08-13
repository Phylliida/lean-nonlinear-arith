- **nla-19** `todo` **Quadratic-complete checker (S1-free).** Sequencing
  insight: nlsat lowers root conditions to Thom sign encodings at degree <= 2
  (`mk_quadratic_root`), and the nla-02 lemmas (sign-from-rootlessness, IVT
  isolation) already discharge those plus cell-sign steps. A checker restricted
  to traces whose projection steps stay at degree <= 2 per variable needs NO
  S1 — and Verus goals are overwhelmingly per-variable degree <= 2. Build this
  first; full S1 (nla-11) only unlocks the deep tail. Converts the capstone
  from a cliff into a ramp.

