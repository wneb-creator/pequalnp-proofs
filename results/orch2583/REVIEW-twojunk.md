# TwoJunk Lean preservation review

Verdict: PASS for the current checked partial. This is a counterexample to insufficient intermediate normalization hypotheses, not a refutation of L-meta-2583.

Reviewed file: `results/orch2583/lemmas/TwoJunk.lean`, 99 lines, 3014 bytes, SHA256 `bde1969ea47def31218ec987cf72163b539c305ee4d4686fc56a11c83ea3f2e0`.

The file uses the genuine library circuit, graph, TopForm, junk, gammaE, lift, read-one, and least-circuit definitions. The graph is the five-vertex path. Its nine-gate circuit and five-gate replacement match the explicit formulas previously evaluated on all 32 assignments. Gate indices 3 and 5 correspond to wires 8 and 10. The source proves both circuits are AO2, both compute the same path function, the path is bipartite and has no four-cycle, and the sizes are nine and five.

The stronger claims are explicitly finite kernel-checked statements: TopForm, lift fixed point, every gate live, exactly two junk gates, both junk gates accepting all four edges, no actual edge covering all accepted edges of either junk gate, and failure of semantic read-one. The final `not_least` lemma uses the genuine minimum-size clause and the five-gate replacement to prove the example is not least.

The edge-pivotal lemma erases each gate and redirects its readers to wire 14. Inspection of `CircuitMoves.eraseGate` confirms this wire is out of bounds after deletion, hence evaluates false. Thus it proves loss of some true edge after replacing that gate by false. It does not claim the erased circuit is AO2, does not establish minimality, and does not yet quantify over arbitrary earlier-wire bypasses. Those distinctions must be preserved in any notes or PR description.

Format checks: sole import `PEqualNP.Defs`; all helpers reside in `PEqualNP.Outside.L_meta_2583.CounterExample`; no forbidden root qualifier, strings, axioms, admissions, native decision calls, custom instances/types, attributes, meta commands, or unsafe declarations. Only permitted maxRecDepth/maxHeartbeats options are used, locally scoped. `decide +kernel` checks finite decisions in the kernel; it is not native_decide.

The author reported standalone compilation exit 0. I inspected the complete `2583-twojunk-first.stdout` and `.stderr` files; both are empty. This review did not rerun Lean. Root will inline the import-free body and build the named partial. The exact posted target remains unproved and no checker acceptance is claimed.

The original Python example was authored by this reviewer, while the Lean translation and finite claims were independently implemented by another agent. This review checks that translation and its precise scope. Any later all-wire-bypass extension changes the source hash and requires a separate review.

## Reviewed irreducibility extension

Verdict: PASS for `results/orch2583/lemmas/TwoJunkIrreducible.lean`, 121 lines, 3905 bytes, SHA256 `6a7128098e98291b483373f2cd0bd33f1aea11852b2a3c7700ce1495c3a5e84b`. The only change from the reviewed 99-line source is three additional finite lemmas before the namespace closes; all earlier claims, including `not_least`, remain unchanged.

- `every_operand_bypass_changes`: deleting any gate and redirecting its readers to either of its original two operands changes the circuit function on some input.
- `every_earlier_wire_bypass_changes`: the same conclusion holds for every wire strictly earlier than that gate, including all input wires and earlier gate wires. The quantified cases total 5 + 6 + ... + 13 = 81. Since a redirect wire is earlier than the deleted gate, the library erasure function does not need to shift that chosen wire.
- `every_one_override_changes`: replacing any gate by an empty AND introduces a false positive. The library definition `GateOp.eval .and [] = true` confirms that this is a true override. This modified circuit is not claimed to satisfy AO2; it is used only as a semantic test.

These are exhaustive finite statements proved by `decide +kernel`, not heuristic observations. The complete `2583-twojunk-irreducible.stdout` and `.stderr` logs are empty, and the author reported compilation exit 0. The same import, namespace, allowed-option, and forbidden-construct scans pass. No new axioms or assumptions were introduced.

The precise consequence is local irreducibility under the listed one-gate changes despite global nonminimality. The extension does not quantify over multi-gate rewrites, arbitrary replacement functions, or all circuits of smaller size. In fact the explicit five-gate equivalent circuit still proves the nine-gate example nonleast. Therefore the extension refutes no statement requiring `IsLeastAO`, and no full-gap refutation or checker acceptance is claimed.
