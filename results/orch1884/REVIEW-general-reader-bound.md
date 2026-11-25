# Independent GeneralReaderBound review

Verdict: PASS for the conditional general-circuit contraction and preservation. The complete posted L-meta-1884 exclusion is not asserted.

Source: `lemmas/GeneralReaderBound.lean`,187 lines,12715bytes. SHA256 `67ed300c2ceb05f5f4ddff3a318b6a0db467ad7b2d8c16ea69820cf645629e4d`.

I reviewed the full difference from the corrected monotone ReaderBound. The core eleven-input to nine-input mapping, default-false semantics, output handling, and constant-propagation invariant are unchanged. The generalization permits NOT gates in both the original and reduced circuits and changes the explicit cofactor premise from Monotone2 to FanInTwo.

The added NOT case agrees with the library evaluator: an empty NOT is constant true; otherwise only its first operand matters. A constant operand is complemented without adding a reduced gate. A nonconstant operand produces one unary NOT gate, and its original first operand cannot be either fixed raw position0 or10. Thus a retained NOT is not counted by r0, even if its ignored second operand happens to mention a fixed raw input. This is precisely why r0 truncates the NOT input list to its first entry. Its count is the number of effective reader gates, not read occurrences.

The final theorem remains explicitly conditional on the sixteen-gate cofactor lower bound for all actual nine-input FanInTwo circuits. It then proves sixteen plus the effective-reader count is at most the original size for exact Petersen computation on identity inputs plus free negation of input0. Discharging that cofactor premise through NineGeneralFloor is a separate integration check.

Format scan: only PEqualNP.Defs import, correct helper namespace, no options, attributes, string literals, forbidden root qualifier, additional axioms, sorry, native_decide, unsafe code, credentials, or binary artifacts. Source compilation/export was reported successful by its author; this independent review inspected the exact source and its semantic changes.
