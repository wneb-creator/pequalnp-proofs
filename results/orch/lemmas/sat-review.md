# SAT encoding review for L-meta-2732

Independent review of circuit-search/synthesize.py found its conditional AND/OR CNF, one-hot fanin selections, constant literal, and output row targets correct. Exactly 26 gates suffice for searching at most 26 because output-copy gates may pad a smaller circuit.

Independent Python enumeration verified all 336 Heawood automorphisms (168 Fano collineations and their duals), all 9,555 first-two-gate wiring pairs, and exactly the 65 canonical representatives in R_meta_2732_3 / L_meta_3537. The 14 packed input signatures transpose to exactly the search script row order: 21 edge assignments followed by 37 increasing maximal independent sets. Their sizes are 21 of size 4, 14 of size 5, and 2 of size 7. Target signature is 2097151.

Verification artifacts: /tmp/oec/pequalnp-pilot-70/sat-review/verify_rows_symmetry.py, verification.log, verified_symmetry.json. These are independent computational checks, not Lean proofs.

## Sound search constraints

- Every gate can be required true on at least one of the 21 positive rows and false on at least one of the 37 negative rows. If a gate is false on every positive row, replace it by false: positive evaluations do not change and negative outputs can only decrease. Dually replace a gate true on all negative rows by true. Simplifying constants yields a smaller circuit. Output-copy padding preserves both restrictions. In particular no useful first AND gate combines a nonedge pair.
- Every original input is essential: choose an incident edge and assign exactly its endpoints true. Each input therefore appears as a fanin somewhere. Delete dead gates; each gate except the output is then consumed later. Padding by output-copy chains preserves this liveness restriction.
- Adjacent independent gates can be lexicographically sorted by (left fanin, right fanin, operation). Choose a lexicographically minimal circuit over topological orders and input automorphisms. This also implies first-two-prefix canonicality. A cheap necessary part: if the next gate does not use the current output, its left fanin is at least the current left fanin. With sorted fanins, next.right[current_output] identifies dependency.
- Avoid unconditional nondecreasing maximum-fanin order combined with first-two canonicality unless compatibility is proved. The posted canonical score is left-first, not maximum-fanin-first.
- In a minimal circuit, a gate cannot be boundary-dominated by an earlier wire (earlier wire greater on every positive row and less on every negative row), since substitution preserves the required output. This restriction conflicts with padding copies, so do not add it globally to the fixed-size encoding without an exception or size enumeration.

A weak provable operator count: at least six OR gates, because fixing all seven left inputs to true restricts the function to OR of the seven right inputs; simplification never creates OR gates. No stronger general AND/OR count has been proved by this review.

## Independent partial-checkpoint reviews

Baseline.lean: passed mathematical and format review. Independently evaluated its 27 gates (7 AND, 20 OR), output wire 40, on all 16384 inputs against the posted edge list, with no mismatch. All fanins precede their gate. It proves the 27-gate baseline only, not the assigned 26-gate existence. Allowed Defs import; all helpers in matching auxiliary namespace; permitted scoped options; no forbidden words, strings, attributes, or extra axioms. Detailed report: /tmp/oec/pequalnp-pilot-70/sat-review/baseline-review.json.

DirtyFilter.lean: passed mathematical and format review. If two selected rows each connect safely to the two distinct B witnesses, they create a forbidden K2,2, proving selected-row uniqueness. The columns proof is dual. The final lemma chooses the unique selected row/column, falling back to the supplied A/B witnesses if selection is empty, and covers every selected crosspair. It is a generic helper only, with no claim of a complete circuit bound. Its Mathlib.Init import and auxiliary namespace obey partial-file rules; no forbidden words, strings, attributes, options, or extra axioms. Agent compile log was empty and reported exit 0; root owns final named-module build and push.

## Pair-dirty encoding and first-dirty lemma

Reviewed the restricted at-most-one pair-dirty AND encoding. The extra 85 rows are exactly all false assignments of weight at most two. Each flag is equivalent to AND operation plus a true output on at least one such row; exactly-one with a free dummy flag correctly enforces at most one actual dirty flag. Exhaustive tiny clause checks passed 150 assignments. The existing negative-boundary pruning clause becomes vacuous because its enlarged slice includes the zero row; this only weakens pruning. Tightening it back requires care because replacing a boundary-tautological gate by true can increase the number of pair-dirty downstream AND gates.

New structural result: the first globally dirty AND has a singleton/pair false witness. Before that gate, earlier AND outputs vanish on the chosen false assignment; every true prefix wire therefore has an OR-only path from a true input, which remains true whenever that single input is true. Picking one such input for each binary AND fanin gives the desired small witness.

Formal artifact /tmp/oec/pequalnp-pilot-70/sat-review/FirstDirty.lean compiled with exit 0 and empty first-dirty-lean.log. Final helper firstDirtyAnd_falsePair is stated directly using Circuit.wires and an arbitrary monotone Boolean target F. It assumes every prefix AND is false on the chosen x, and proves a true next binary AND has a false singleton/pair witness. This is a structural partial only. The lower_bound agent independently reviewed mathematics and format and passed it, including out-of-range wires, repeated fanins, and n=0. Root owns integration and preservation.

A separate deterministic random check (seed2732) verified equality of the first globally dirty and first pair-dirty AND indices on10000 random26-gate monotone networks. This is supplemental evidence, not a substitute for the Lean proof.

Generic induced-subgraph synthesis parameterization also passed review: all input counts, row offsets, and liveness bounds are dynamic; custom graphs require no-canon. All generated subgraph files have no isolated inputs. Minimality and dirty-AND options restrict completeness and must remain off when interpreting unrestricted at-most-bound UNSAT results.
