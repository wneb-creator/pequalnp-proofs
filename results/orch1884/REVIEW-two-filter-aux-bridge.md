# Independent review: TwoFilterAuxBridge

UTC: 2026-11-25T16:49:42.978996+00:00

Verdict: PASS as a conditional actual-circuit auxiliary construction. Exact source SHA256 `d8c78af9d397b3e9ab4618f9b046a841320790832bc196881a5e51f5ce5e1257`, 3883 bytes/82 lines. Author reported Lean exit0; complete two-filter-aux-bridge.stdout/.stderr are empty. This reviewer did not rebuild.

The theorem starts from an explicit one-NOT circuit decomposition with AND/OR fan-in≤2 before and after it, total size≤18, at leasttwo base-rail readers outside the selected NOT, and two canonical suffix filters AND[1,q] and AND[5,q], whereq=11+prefix.length. It assumes exact Petersen computation on identity primary inputs plus free NOT(x0), and the full SharedFilter monotonicity/independence/factorization premises for the selected NOT operand.

Replacing the selected NOT bytrue preserves every positive basis row by monotone-suffix comparison. DirectFilterRows proves the operand false on every one of the13 negative rows; there the old NOT was alreadytrue, so replacement leaves the output unchanged. These arguments permit additional NOT-output readers in the suffix; the optional negative260 row is not assumed or asserted.

The two filters lie outside the base rail set and are distinct, so PairReaderCharge supplies two additional gate charges. Together with the explicit two base charges and deletion of the selected constant gate, Forced13Compile produces an actual monotone nine-input circuit of size≤13. Positive row3 and negative row25 establish nonconstancy for output reconstruction. seed_row proves the coordinate/input-list agreement, and exact compiled evaluation transfers all25 row constraints.

This is a substantive auxiliary bridge, but the base two-reader bound and shared-filter structural/semantic hypotheses remain explicit; it is not an unconditional exclusion of all one-NOT candidates. The four imports are reviewed scratch proof dependencies and require an allowed-import assembly for submission. Correct L_meta_1884 namespace, no options, attributes, strings, forbidden constructs, new axioms, unsafe declarations or secret-like content; below512KiB.
