# Independent review of PivotalNecessary

Verdict: PASS for a partial research checkpoint, conditional on the combined named-module build. This is not a proof of L-meta-2448 and not a checker acceptance report.

Reviewed all 372 lines of results/orch/lemmas/PivotalNecessary.lean, SHA256 332475a5d55ca22554748fcb69d6a275f5d7a8b95943f8ddbf095f50e4f7f3e8. Only PEqualNP.Defs is imported. Helpers stay in the permitted module auxiliary namespace. The bounded forbidden-text scan returned exit 1 with no matches. No new axioms, unsupported proof primitives, options, or attributes occur.

The zero-gate deletion remaps the deleted wire n+k to n+oldGateCount, which remains outside every list of wires in the shorter circuit. Earlier wires retain their indices; later wires shift down by one. Before the deletion point, shifted forward references are still out of range. This establishes equivalence to forcing gate k false without a ReadsBack hypothesis. Monotone2 is preserved, and the gate count decreases by exactly one.

The final lemma assumes a monotone circuit computing the exact graph function and minimality among all such circuits. If false substitution preserved every edge pair, monotonicity and the downward graph sandwich would preserve the entire function. Deletion would then contradict minimality. Thus every valid gate has a graph-edge pair lost by false substitution. The original circuit accepts that pair by its exactness hypothesis. The lemma does not claim that the gate owns its pivotal edge or that its pivotal edges have a common center.

The component validation records exit status 0 at 2026-11-25T07:40:49.563731+00:00. Complete pivotal-necessary-001.stdout and pivotal-necessary-001.stderr are both empty. This review did not rerun the build or the repository statement checker.
