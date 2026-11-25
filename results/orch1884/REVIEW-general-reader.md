# Independent review: general effective-reader contraction

UTC: 2026-11-25T16:06:04.133575+00:00
Verdict: PASS as a checked conditional helper. The total-circuit cofactor lower bound remains an explicit premise; this file is not a proof of L-meta-1884.

Source: `results/orch1884/lemmas/GeneralReaderBound.lean`
SHA256: `67ed300c2ceb05f5f4ddff3a318b6a0db467ad7b2d8c16ea69820cf645629e4d`
Size: 12715 bytes; 187 lines.
Root/author reports Lean exit 0. Complete general-reader-checked.stdout/.stderr are independently verified empty.

I compared the entire source with the previously reviewed, fixed ReaderBound helper. The substantive changes add NOT to allowed gate operations, handle the already defined NOT branches of the contraction, replace the Monotone2 premise and conclusion-class requirement with FanInTwo, and rename the namespace. No cofactor identity, counting invariant, output branch, or gate-count inequality was changed.

For NOT of an empty input list, the library output is true and the contraction emits a constant. A NOT of a constant wire also becomes a constant. A NOT of a surviving variable wire emits one unary NOT at the new circuit index. The proof uses the first original operand only, matching GateOp.not evaluation even when the allowed list has two elements. The effective-reader predicate likewise truncates NOT inputs to one, so an ignored second reference to primary 0 or 10 is not incorrectly counted as an eliminated reader. A surviving variable wire cannot be either fixed source position, so every emitted NOT has r0=false and the deletion-count invariant is preserved. Forward/invalid references continue to use the original proved default-false behavior.

The final theorem assumes the sixteen-gate lower bound for every actual nine-input FanInTwo circuit computing p9. From that premise it proves 16 + effectiveReaders(C) <= C.size for arbitrary FanInTwo C computing the exact ten-input Petersen target on identity pins plus free negation of x0. It does not by itself discharge that cofactor premise, normalize arbitrary input maps/unary functions, or exclude the remaining one/two-reader cases.

Only import: PEqualNP.Defs. All declarations lie in PEqualNP.Outside.L_meta_1884.GeneralReaderBound. There are no options, attributes, sorry, axioms, native_decide, forbidden namespace substring, quotes, or unsafe/meta declarations. No credential material was observed. The reviewer did not author this generalization.
