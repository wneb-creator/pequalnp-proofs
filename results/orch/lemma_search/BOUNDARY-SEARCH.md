# Alternate lower-bound investigation

The checked global bound remains 20; the posted bound is 25. The new useful results
are local structural constraints, all valid with arbitrary NOT gates elsewhere.
They are formalized in `../lemmas/Blocking.lean`, `BlockingDeeper.lean`, and
`BlockingDegreeThree.lean`. See `blocking-validation.json` for exact hashes and
complete diagnostic logs.

The key invariant is robust dependence: for every distinct input pair p,q and
either fixed value of q, the target still depends on p. If p has a sole reader,
that reader cannot be disabled by fixing q. This forbids a primary companion
at a binary AND/OR reader, AND-over-AND or OR-over-OR companions containing a
different primary, and degree-three input AND-over-OR-of-two-primary companions.
These are valid synthesis pruning rules, not a proof of any global gate count.

## Quantitative limits of other routes

The maximal independent sets have size distribution `{7:2,6:4,5:26,4:7}`.
Thus certificate complexities are C0=10 and C1=2. The usual nonnegative
adversary bound cannot exceed sqrt(20), so its square cannot give a formula
leaf bound of 26. Negative-weight adversary can escape this barrier, but even a
formula leaf bound would still require a circuit fanout argument.

Across the natural seven-variable/seven-variable partition, there are 39 distinct
neighborhood unions, including the empty set. The corresponding nonempty OR
functions are linearly independent by the multilinear monomial basis after
complementing the right-side variables. Thus the communication matrix of the
target has real rank 38; its complement has rank 39. This does not furnish a
useful 25-gate circuit lower bound.

## Public references read 2026-11-25

- Hoyer, Lee, Spalek, *Negative weights make adversaries stronger*, pp.1–2,
  https://www.ucw.cz/~robert/papers/madv.pdf. It states the nonnegative
  certificate-complexity barrier and explains that negative weights can evade it.
- Jukna and Lingas, *Lower bounds for Boolean circuits of bounded negation width*,
  JCSS129 (2022), https://doi.org/10.1016/j.jcss.2022.05.003. Its monotone
  conversion has a multiplicative overhead, so it does not justify removing one
  NOT without cost. The no-cancellation observation likewise does not apply
  without an additional hypothesis on produced terms.

No unverified bibliographic figure is used in a Lean theorem or circuit bound.
