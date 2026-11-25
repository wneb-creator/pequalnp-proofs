# Lower-bound strategy notes

Updated: 2026-11-25T14:17:37.721786+00:00

- Checked all three existing reductions for L-meta-2592. The useful decomposition is binary-gate floor 15 plus at most four NOT gates, from R_meta_2592_271. R_meta_2592_408 normalizes invalid reads/output; R_meta_2592_318 cuts at the last NOT.
- Existing L_meta_6194 proves the 15 binary-gate floor by six first-branch groups. This is genuinely weaker than the requested 20 total gates: 1–4 NOT gates remain.
- No semantic loophole in FanInTwo/evaluation found. Nonexistent wires yield false; unused NOT operands yield no extra power.
- A naive one-NOT elimination by replacing its output with a constant is false even for monotone, single-output functions. Let f=x1 OR x2, h=(x1 AND x2) OR x3, f0=f AND h, f1=f OR x3. Then f=f0 OR ((NOT h) AND f1), but replacing NOT h with either constant changes an input. Thus any elimination proof must explicitly use size or graph structure.
- Petersen has no triangles or 4-cycles. An optimistic route is to show that one-NOT nonedge masking cannot profit on such a quadratic function; no proof of that claim yet.
- General dependency counting only gives nine binary gates; first-branch grouping improves to fifteen. Reaching nineteen binary gates for the one-NOT case requires substantially stronger structural information.

No checked lemma or claimed proof yet.

## 2026-11-25T14:25:27.743988+00:00

First-gate retention route now concrete: 360 finite row-pair witnesses were generated for each ordered distinct input pair and four signed gate kinds. Each witness keeps every other raw input and the computed gate equal while changing Petersen output, so either operand cannot be consumed by that first gate. The Lean snippet is Retention.snippet.lean, awaiting compilation.

Projection caution: existing mass counts constants only. A first AND/signed-AND gives two constant retained wires after restricting its positive operand to zero; first OR gives one constant and one duplicate, which does not automatically yield another gate saved. Therefore current method suggests binary floor17 generally and18 for first non-OR, not18 in all cases.

2026-11-25T14:28:31.872399+00:00: RetentionStandalone.lean compiled with exit0 and no output. Finite witness and retained-operands proof now checked by Lean. Exact source saved in results/orch/lemmas; validation recorded in retention-validation.txt.

## OR-first variable identification 2026-11-25T14:37:33.374930+00:00

Investigated x0=x2 (nonadjacent inputs). The target becomes a 9-vertex graph with 14 edges and degree sequence 2,3,3,3,3,3,3,3,5. It is not isomorphic to deleted-Petersen, so the existing 15-binary-gate certificate cannot be reused merely by renaming variables.

An explicit monotone 17-gate expression is: x1*(u OR x6) OR (x3 OR x5)*(u OR x8) OR (x4 OR x7)*(u OR x9) OR x3*x4 OR x5*x7 OR x6*(x8 OR x9), where u=x0=x2. Each multiplication means AND. Exhaustive weighted biclique-cover optimization (71 bicliques, 2^14 edge subsets) also returns 17 within that restricted circuit class. This is an upper bound and a restricted-class optimum, not a general circuit lower bound. Complete data: /tmp/oec/pequalnp-pilot-118/or-identification-cover.json.

For adjacent inputs x0=x1, edge01 becomes a singleton and the target simplifies to one literal OR an 8-vertex edge function, likely too easy for this strategy. For x0=NOT x1, the first OR becomes constant; the 9-input nonmonotone target might support a stronger lower bound, but none was found in the 712 checked Petersen statements. No matching 14-edge identified target appears among their literal or encoded edge-list targets. New finite certificates would be needed.

2026-11-25T14:39:46.229421+00:00: STOPPED on root report of lease410. Prepared signed4-op contraction encoder compiled (source/buildlog archived in results/orch) but never launched. Mode0: x1=NOT x0; mode1: x2=x0. It searches binary gates with free complementation and is witness-search only; an UNSAT answer would not be a Lean certificate.
