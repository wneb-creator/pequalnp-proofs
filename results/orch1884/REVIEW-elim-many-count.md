# Independent review: ElimManyCount

UTC: 2026-11-25T16:43:37.941440+00:00

Verdict: PASS for the conditional constant-folding count helper. Source SHA256 `eaea5c3166a5df7fd60a41d2d3dd2d4b5b471e76eae4996e51febd39716925e6`, 5583 bytes/132 lines. Author reported Lean exit0; both complete logs beside the source are empty. This reviewer did not rebuild.

The predicate constantK explicitly requires each selected original wire index to exist in the status bank and carry a Boolean constant. Elim appends one status for every original gate, even when no actual gate is emitted, so those original indices retain their meanings. A reader is counted once per gate using a finite-set membership disjunction, including when it reads several selected constant wires.

`read_step_free` depends on NOk: the imported definition permits only AND/OR/NOT with bounded fan-in and explicitly restricts NOT to at most one operand. This matters: a syntactically read but semantically unused later NOT operand must not earn a saving; the NOk hypothesis excludes that case. With a genuine constant operand, simplify_count emits no gate. Every other step emits at mostone. Induction yields count_readers without double-counting gates.

`constant_step_count` first charges readers of the initial constant set, then adds the selected gate's original status index q=initial-status-length+prefix-length to that set. Its explicit hstep premise says the selected operation appends a constant status and emits no gate; the added +1 charges this distinct selected operation. Postfix readers of the enlarged set are again counted once. forced_true_count discharges hstep for AND[], thetrue constant. The arithmetic charges only disjoint prefix/selected/postfix positions.

The import is the existing Elim helper, so this is a dependency test rather than a permitted final standalone import. Correct L_meta_1884 namespace, no options, attributes, strings, forbidden constructs, new axioms, unsafe declarations, or secret-like content, below512KiB. No semantic circuit invariant, output reconstruction, or complete13-gate replacement theorem is claimed here; the caller must combine the count with Elim correctness and normalize arbitrary NOT operands before using NOk.
