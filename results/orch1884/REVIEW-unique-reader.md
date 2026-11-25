# Independent review: UniqueReader.lean

Verdict: PASS. No correctness findings.

Reviewer: circuit_search. The reviewed source is 71 lines and 2508 bytes, with
SHA-256 `a43f943861d9971e1c06f2ed36dc1d84243f0299478f8263e18772fd82c5f030`.
This matches `unique-reader-validation.json`, which records check exit 0 and a
successful export. I read the archived stdout/stderr and did not rebuild.

- `count_zero` correctly proves that every member has a false predicate when
  the Boolean-predicate occurrence count is zero. The induction handles the
  head and tail separately and requires no decidable equality on the element
  type.
- `split_one` combines a count of at most one with an explicit true occurrence.
  For a false head, the witness must lie in the tail, and the induction adds
  the false head to the prefix. For a true head, the tail count must be zero,
  so `count_zero` excludes every later true occurrence. The result concerns
  exactly one list occurrence, so repeated equal values do not evade it.
- I inspected the imported definitions: `RestrictionEight.deleted` is exactly
  the singleton finset `{2}`, and `ElimManyCount.reads` scans `g.inputs` with
  `List.any`. Thus `reader_iff` is precisely equivalent to raw membership of
  index 2 in the gate's input list.
- `raw_two_split` applies the generic split to that same predicate. Its prefix
  and suffix exclusions follow by converting an alleged raw read to predicate
  truth and contradicting the false predicate supplied by `split_one`.

Scope is preserved correctly. The conclusion identifies one reader **gate**;
it does not assert that index 2 occurs only once inside that gate, classify its
operator, prove semantic dependence, or supply the existence/count premises.
It uses raw input-list membership, which is distinct from the head-only
effective-reader convention for arbitrary NOT gates. The statement itself
does not confuse those predicates; downstream applications must retain its
stated raw-count premise. In the intended monotone-circuit application, NOT
gates are excluded separately.

The compiler stdout contains two nonblocking style warnings: an unused
`List.countP_cons` simp argument at line 15, and an unnecessary `simpa` at line
27. Stderr is empty. No source changes were made to the stable checked file.
No sorry, new axiom, native_decide, forbidden root marker, string literal, or
attribute appears in it.

This is a partial structural module, not a completed proof of L-meta-1884.
Its local dependency import still requires the final repository-approved
single-file packaging.
