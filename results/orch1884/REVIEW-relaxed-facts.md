# Independent review: RelaxedFacts.lean

Verdict: PASS. No correctness findings.

Reviewer: circuit_search. Reviewed source: `lemmas/RelaxedFacts.lean`, 68 lines,
2973 bytes, SHA-256
`fac8538dbbba8f689529985fc57f812ca11c4580103a936e994ea8b820269c74`.
This matches the stable checked version identified by status_check. Its Lean
check was reported as exit 0 with empty diagnostics; this review did not rerun
compilation, as requested. The named diagnostic files were not located in the
bounded searches, so that compiler status is attributed to the checking agent.

The 25 premises are exactly 12 positive rows and 13 negative rows from
`StrongRelaxRows`. I inspected their definitions and the relevant contracts and
implementations of `negative_below`, `output_mono`, `run_agree`, `ofFn_agree`,
`gate_value`, and `ClosedOrSet.no_copy`.

- `singleton_cover` has a negative superset for every singleton. Independently
  checked witnesses for inputs 0 through 8 are respectively
  25, 58, 52, 25, 25, 52, 69, 138, 274. Monotonicity therefore justifies
  `singleton_rejected`; no full target-function equality is assumed.
- `row_two_rejected` concerns mask 2, whose sole true input is index 1. It is
  below negative row 58. This is distinct from the raw wire index 2 used later.
- `nonconstant` uses positive row 3 and negative row 25, both explicit members
  of the respective lists. Its lack of a monotonicity assumption is correct.
- `output_not_two` is valid because input index 2 is false on positive row 3.
  The nine-input wire-prefix lemma applies, so an output at raw index 2 cannot
  satisfy that positive premise.
- `some_reader_two` compares mask 2 with positive mask 6. They differ exactly
  at input index 2. If no gate input mentions raw index 2, `run_agree` preserves
  equality at every other output index; `output_not_two` excludes the one
  exceptional direct output. This contradicts false versus true on those two
  rows. The conclusion is the stated existence of a raw reader, not uniqueness
  or a stronger fanout classification. ReadsBack is not needed for this
  dependency argument.
- `no_repeated_operand` uses all necessary hypotheses. Monotone2 excludes NOT,
  ReadsBack ensures the duplicated source precedes the gate, and AND/OR of
  `[a,a]` copies that source on every input. The inspected `no_copy` theorem
  deletes that gate while preserving the whole function and reducing size,
  contradicting the stated global minimum among equivalent Monotone2 circuits.
  A weaker local-minimality premise would not suffice, but none is used here.

No sorry, new axiom, native_decide, forbidden root marker, string literal, or
attribute appears in the reviewed file. The finite computations use ordinary
`decide`.

Scope: these are structural consequences of the relaxed 25-row premises. They
do not assert full equality with the nine-input cofactor, reject the exceptional
row 277, or prove the posted L-meta-1884 lower bound. The local dependency
imports are appropriate for this preserved partial module; a final single-file
submission still needs the repository's permitted-import packaging.

Log confirmation by status_check at 2026-11-25T16:50:31.630613+00:00: both complete scratch files1884-relax-facts-first.stdout and.stderr exist and are empty (SHA256e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855). The original reviewer did not read them; this follow-up resolves that diagnostic-location caveat.
