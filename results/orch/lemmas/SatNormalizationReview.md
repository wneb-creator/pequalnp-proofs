# SAT normalization review — pilot 132

Reviewed 2026-11-25 by pilot132_review. This is a source and mathematical review, not a Lean proof of the SAT encoder or an UNSAT certificate. No negative search result settles L-meta-650.

## Exact scope

Reviewed runtime sources:

- `incremental.py`: SHA256 `d0b2be2affa7ff5877e0278d583f57b090fca6002f2b6a4dc935110cd92a8f5b`.
- `synth.py`: SHA256 `3a280142fe4c587440569fd16611c19bdaf2d3334b675a478e3b24aec2ac9f2c`.
- `tap_incremental.py`, including `--free-tap`: SHA256 `6efd94c1b2581ef433c1f6dac468ea0e1c542a29556503c5414827bd87758b14`.

The normalized run uses `rows6-28/meta.json`, all 28 gates free, all extremal cases, `--normal`, and no dirty-input restriction. I independently enumerated its 17-input graph: 24 edges, 52 maximal negative assignments, and every input is essential. The encoder also adds the 17 singleton assignments. The saved 29-gate control log reports SAT in 1.72 seconds with zero failing tests. This control supports implementation sanity, not completeness.

## Joint preservation of existence

For this single-output graph function, the restrictions are compatible with existence of a circuit of at most the chosen gate budget:

1. Choose a smallest monotone circuit. Propagate constants and aliases, discard dead gates, and normalize invalid reads to their actual false value. Since the graph function is nonconstant, these operations produce a circuit using proper earlier references and two-input AND/OR gates without increasing size. Duplicate operands remain allowed.
2. Every remaining gate has nonempty positive-edge support. Otherwise replacing that gate by false preserves all positive edges and decreases the output pointwise; constant propagation removes it. Every essential input and every nonoutput gate is used. Finite backward references and these use conditions place every gate in the final output cone.
3. The singleton clause is precisely the consequence of `SingletonPruning.minimal_gate_has_offstar_edge`: if a gate accepts singleton v, it must accept some positive edge avoiding v. Otherwise that gate could be deleted.
4. A gate supported on exactly one required unordered edge can be replaced by the direct AND of that edge's input endpoints. `PositiveEdgeReplacement.unique_positive_edge_replacement` checks this step with distinct endpoints and an actual required edge. It preserves every positive-edge value throughout the circuit and can only decrease singleton values. Thus it preserves the preceding semantic restrictions. A dead gate created by this transformation would contradict initial size minimality.
5. Commutative operand ordering is harmless. Adjacent independent gates can be ordered by operation and then first operand: swapping a descending independent pair preserves the DAG and decreases the first differing pair in the finite sequence of keys. Repeating gives the encoded local order. A direct dependency disables those ordering clauses.
6. If the minimum size is smaller than the exact SAT budget, append OR(output, output) gates. Their positive support is all 24 edges and they accept no singleton. They satisfy all-used and operand order, trigger no single-positive restriction, and are dependent on their predecessors. Padding therefore preserves all current normalizations.

This argument depends on the actual graph being nonconstant, all encoded inputs being essential, and at least two required positive edges for the stated padding argument. Those conditions hold here. The generic preprocessing and joint argument are mathematical review; the individual checked replacement lemmas are not a formal completeness proof of the encoder.

## Selector qualification

Source selectors are **at least one**, not exactly one. Each selected source is constrained to equal the same gate-input value on every encoded assignment. Taking the first selected source therefore preserves all encoded evaluations. A canonical one-hot witness remains representable, so these relaxed selectors do not exclude witnesses.

However, extra selected aliases can satisfy structural ordering or all-used clauses and then disappear during decoding. Do not claim the decoded circuit necessarily retains those syntactic properties. Literal direct-AND syntax also should not be inferred solely from selector clauses without checking the decoded sources. Every proposed witness must still be decoded and independently evaluated. Exactly-one selectors would make the syntactic interpretation literal while preserving existence.

## Restrictions outside the completeness claim

A free-gate window with other gates pinned is a restricted search. A dirty-input condition requiring an internal AND to fire on one selected negative input is also an extra hypothesis. Neither is justified as covering all witnesses by this review. The 28-gate six-row subproblem is only a sufficient route to a 63-gate full-plane witness; failure on it does not exclude a global witness using sharing across the split.

## Free-tap checkpoint audit

The inspected input artifact has 25 inputs, 61 gates, residual output 85, initial tap 84, and special inputs 12, 13, 15, 21. Its 802 tests combine residual-output extrema with four special singleton positives and negatives for the tap under the residual-false condition. A free tap may select any input or gate wire, with an at-least-one selector; all selected taps agree on constrained tap rows, so first-selected decoding preserves those rows.

The lift shifts every residual wire index by one, appends AND(new input 0, decoded tap + 1) at wire 87, then OR(residual output + 1, wire 87). With the supplied 61-gate artifact this gives 63 gates. The script independently checks the resulting circuit on all full-plane extremal inputs before writing `solution63.json`. No such solution is claimed. The two-output window search has pinned gates/output choices and is not complete for L-meta-650. The checkpoint copies were refreshed and independently compared. `sat_incremental.py` has SHA256 `1569de2e198dc33b3454a3ffb1c9e7a2619f27a0d011554e05f8ef593e51a36b`; `sat_tap_incremental.py` has SHA256 `89757b862a9f62dbe6c483e9ae830b9b009523ee5b411ee062ec3baa6cb7d028`. Their only differences from the runtime sources are local module-name changes in Python import lines. The free-tap extension is prepared but has not been run or given a positive control. The normalized 28-gate run ended UNKNOWN after 301.63 seconds. Checkpoint status records these limits accurately.

## Safe stronger normalization to consider later

The checked `OrReplacement` lemma supports this semantic condition for a circuit chosen first with minimum size, then minimum AND count: an AND gate accepting singletons p and q must accept some positive edge avoiding both p and q. Otherwise its positive-edge function agrees with OR(p,q), and replacing it lowers AND count at unchanged size. Padding uses OR gates and does not violate this condition.

Joint use with the existing single-positive direct-AND rule needs the observation that an OR gate with a single positive-edge support is deletable in a minimum circuit: one nonempty-support operand already agrees on every positive edge and lies below the OR pointwise. Hence the existing direct-AND replacement need not increase AND count in that minimum circuit. This additional joint argument has not been formalized here. Prefer the semantic AND exclusion to forcing a particular OR input pair; several pairs can describe the same edge support in other graphs, so simultaneous per-pair selector pinning may conflict unless uniqueness or a deterministic tie-break is established.

## Checkpoint artifact screen

Independently inspected the refreshed Python source diffs and checkpoint STATUS.json. A credential-pattern scan of all 134 discovered JSON/Python/text/Markdown/log files found zero flagged files. The two remaining `.err` files are empty; the directory contains 136 files including STATUS.json. The checkpoint records searches and checked controls, not an accepted proof or a lower-bound certificate.
