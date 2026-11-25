# Independent review: ClosedOrSafety

UTC: 2026-11-25T16:43:37.941440+00:00

Verdict: PASS. Source SHA256 `09ddf5d680bc8160ab2853ffd3d78cb419b5c947349dc4bfb986aba2757f84f5`, 3150 bytes/70 lines. Author reported Lean exit0; complete second-run stdout/stderr are empty. This reviewer did not rebuild.

`gate_value` uses ReadsBack to identify every stored operand with its value when the gate executed, avoiding an invalid forward-reference assumption. `excludes_or_pair` splits whether the safe operand is satisfiable. The satisfiable case applies the previously reviewed closed-set contradiction. Otherwise that operand is false on every input, so OR[t,a] semantically copies the earlier wiret; the explicit global minimum-size premise and checked no_copy deletion contradict it. This closes the satisfiability caveat without assuming away constant or dead operand wires.

`wire_mono` applies the existing monotone-bank evaluator to List.ofFn inputs and checks both valid indices and false defaults. It needs Monotone2 but no backward-reference premise, consistent with the actual evaluator. output_mono selects the outputwire. The generic helper does not infer safety, minimum size or the rejected row for a particular circuit; those hypotheses remain explicit.

The only direct import is the reviewed scratch ClosedOrSet dependency; this is not an allowed standalone final submission import. Correct L_meta_1884 namespace, no options, attributes, strings, forbidden constructs, new axioms, unsafe declarations, or secret-like content, below512KiB. No full relaxation or posted-target conclusion is claimed.
