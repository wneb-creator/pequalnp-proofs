# Independent review: three blockers require two AND gates

UTC: 2026-11-25T15:53:39.500961+00:00
Verdict: PASS for the checked generic circuit helper, simulation, gate count, and format. No full L-meta-1884 result is claimed.

Source: `results/orch1884/lemmas/ThreeBlockers.lean`
SHA256: `5cb13bfe7f5209d8c022bbccc6a30f6ca1df5b0e4007e6ca7ff38b58d4989819`
Size: 9285 bytes, 248 lines.
The author reports fourth compilation exit 0. Exact complete logs are /tmp/oec/pequalnp-pilot-103/1884-blockers-fourth.stdout and .stderr; both are empty (SHA256 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855).

Each four-bit signature records one baseline row and three comparison rows. Weak means a wire true at baseline remains true in at least two comparison rows; strong only requires one. OR preserves each property. AND of two weak signatures is strong because two subsets of size at least two in a three-element set intersect. The finite Boolean facts were also independently checked across all sixteen signatures and all 256 ordered pairs.

With at most one AND gate, every wire before it remains weak, that AND produces a strong wire, and the remaining gates are ORs, preserving strong. Empty and unary ANDs are explicitly covered; OR folds also cover empty input lists. Invalid wire reads and invalid output indices use zero exactly as the library does. A zero signature satisfies both invariants. Thus no acyclicity, well-formed wire index, exact-two-input, or output-is-last hypothesis is silently needed.

The bitwise simulator is related to the standard Circuit evaluator by exact getD/map lemmas, fold evaluation, and list execution induction. The final theorem assumes only AND/OR operations with fan-in at most two, the weak initial-signature property, and the stated output values on all four rows. A true baseline and three false outputs violate strong, forcing at least two AND gates counted by the declared isAnd predicate. The source does not claim how to obtain such four rows or weak supplied signatures for a Petersen circuit; that application remains separate.

Only import: PEqualNP.Defs. All declarations lie in PEqualNP.Outside.L_meta_1884.ThreeBlockers. No sorry, axiom, native_decide, forbidden namespace substring, double quote, attribute, set_option, or unsafe/meta declaration occurs. No credential material was observed. The reviewer did not author this helper.
