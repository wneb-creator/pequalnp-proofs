# Library strategy

Started 2026-11-25 03:07 UTC. Parent alone owns L-meta-1896 lease.

## Completed dependencies already in the repository

- `L_meta_4680.lean` proves exactly the De Morgan dual hypothesis of `R_meta_1896_1`: a 26-input monotone circuit becomes a 27-input monotone circuit with a true sentinel, exchanging OR count for AND count and complementing the function. About 145 lines. Invalid and forward wire references are handled explicitly.
- `L_meta_4682.lean` proves exactly that reduction's compression hypothesis: a monotone 27-input circuit with some false input becomes a well-formed `AndCountCircuit 27`, preserving every input value and not increasing AND count.
- Neither is an allowed direct import: our gap allows only `PEqualNP.Defs` besides Mathlib. Their code can be reproduced inside the final file's own helper namespace if this route is used.

## Remaining obstruction

`R_meta_1896_1`'s third hypothesis is the hard bound: every well-formed AND-count circuit, false on dual incident pairs and true on dual generic maximal false rows, has size at least 51.

`R_meta_4684_219` further removes the true sentinel by replacing it with a disjunction over a fixed line. The remaining obstruction concerns 26 variables and the same lower bound.

`R_meta_1896_347` instead separates a finite geometry check from a circuit lower bound on 36 cyclic representatives and all 13 shifts (468 rows). The finite geometry hypothesis is much easier than the circuit lower bound.

`R_meta_1682_7` merely combines our 51-OR bound and sibling 13-AND bound to get 64 total gates. `R_meta_1682_1` splits by line degree; `R_meta_1682_2` splits geometry completion from a small-circuit accepting independent set. None gives a shortcut by itself.

## Definition checks

- `Monotone2` requires AND/OR operations and fan-in at most two. It does not require backward-only references.
- Circuit evaluation always reads nonexistent/forward wires as false, so a normalization argument must handle those references.
- Empty AND is true; empty OR is false; unary AND/OR copies a wire.
- `GenericRejection.lean` documents 468 generic maximal false inputs at order 3: 234 triangles with four missing lines and 234 quadrangles with three missing lines.
- Correctness only at generic false inputs is weaker than computing the full incidence function. Existing exact-incidence lower bounds require a separate extension argument.
- The public file `GenericRejection.star` has unbounded OR fan-in; it is not directly a `Monotone2` witness.

## Status

No compiled helper produced yet. No admissible finished theorem proving the 51-OR obstruction found so far.

## Cross-row merge accounting (03:16 UTC)

The generalized local merge count says each of 468 generic false rows needs 18 merges among its 19 critical zero variables, totalling 8424. This does not by itself give the target bound.

1. A direct simulation of the ordinary 51-OR star circuit finds individual top OR gates which merge on 441 of 468 rows. The bound of 243 for a raw same-side pair is not a universal gate bound. Raw nonincident mixed pairs merge on 264 rows. Tested random parenthesizations give the same total of 8424 and very different individual capacities.
2. More decisively, a greedy family of only 49 raw input-pair OR gates already produces complete connectivity among the 19 zero variables on every generic false row. This is not a counterexample circuit: its output does not meet the specification. It shows that an invariant tracking only accumulated per-row connectivity loses crucial information. A successful argument must track which connected components are carried together by actual wires, or impose an output-sensitive condition.

Simulation: `/tmp/oec/pequalnp-pilot-62/merge_accounting.py`; complete ordinary-circuit results in `merge-accounting.out` and `merge-accounting.err`; the 49-pair graph in `greedy-merge-graph.json`.

## Independent checkpoint audit (03:12 UTC)

Reviewed Geometry, OrLower, Routes, then Normalize. No blocking issue for a clearly labelled partial checkpoint. The assembled file at 735 lines preserved the first three bodies exactly, used only PEqualNP.Defs, and had own namespaces and no forbidden raw text. Normalize preserves all operations and arities, shifts backward references, replaces invalid references with a false input sentinel, and proves evaluation preservation. None of these components claims the posted 51-OR bound. There is no main theorem yet, so this checkpoint is not submission-ready.
