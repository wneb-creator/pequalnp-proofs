# Independent review: unconditional effective-reader floor

UTC: 2026-11-25T15:58:30.314507+00:00
Verdict: PASS as a checked dependency wrapper. It narrows the monotone eighteen-gate case but does not prove the full L-meta-1884 target.

Source: `results/orch1884/lemmas/ConcreteReaderBound.lean`
SHA256: `031cd73a2321e6cb59b5523772e51e80d4ca74e3d31e5afc1e6c4b545c0513c0`
Size: 1086 bytes; 30 lines.
Author reports second Lean run exit 0. Complete /tmp/oec/pequalnp-pilot-103/1884-concrete-reader-second.stdout and .stderr are independently verified empty.

The wrapper supplies ReaderBound.main's explicit cofactor premise using the independently checked NineCircuitFloor.nine_circuit_floor theorem. cofactor_eq unfolds the two exact nine-variable edge functions and reassociates OR, so the equality is definitional after that reassociation; no graph-isomorphism or variable-order assumption is omitted. The final bound is 16 plus the number of effective reader gates of primary positions 0/10, at most C.size. Hence size at most eighteen implies at most two such reader gates.

The theorem assumes Monotone2 and identity-ordered ten inputs plus free negation of x0. It does not cover arbitrary internal NOTs or arbitrary mappings without a separate normalization argument. The prior contraction proof was independently reviewed by lean_setup in REVIEW-reader-bound.md, source hash 539e05e920c9a187680a12f748528d879407aaf7b65f562cabff493b8e0c533d. NineCircuitFloor was independently reviewed by status_check, source hash 445fcd30f2db31bb9adef82dec09dd90536ebdaa9326173427553a29108d44d8. Both dependencies are checked; no unproved lower-bound hypothesis remains in this wrapper.

Imports NineCircuitFloor and ReaderBound make this a dependency test, not a final Defs-only submission. All declarations lie in PEqualNP.Outside.L_meta_1884.ConcreteReaderBound. No sorry, axiom, native_decide, forbidden namespace substring, quote, attribute, option, or unsafe/meta declaration occurs. No credential material was observed. The reviewer did not author this wrapper.
