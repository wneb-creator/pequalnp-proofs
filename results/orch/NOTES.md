# L-meta-3821 orchestration notes

Only root holds the lease. Each agent appends findings under its own heading. Do not change the target proof file without coordinating.

Exact desk statement is in GAP.json; statement-only copy is /tmp/oec/pequalnp-pilot-38/statement.txt.

Strategies: direct circuit restriction, structural counting, counterexample/finite search, reduction decomposition.

## restriction_proof

- Generic helpers Hardwire.fix_last preserve size, PermInputs.gate_elim_at saves two gates. Our conclusion needs at least four gate savings on false or nine on true after adding the final OR, beyond those generic lemmas.
- Constructed ten explicit Petersen graph automorphisms, each sending its indexed vertex to 9. Draft Lean finite transitivity lemma is in results/orch/lemmas/Restriction.lean; awaiting toolchain to compile. Uses algebraic AC equality, not truth-table enumeration for the universal Boolean function claim.

## Counterexample search

L-meta-3821 assumes equality only on 91 of 1024 inputs: 76 independent sets plus 15 edge pairs. Values on larger sets containing an edge are unconstrained. Parent reduction used full equality, so this weakening is a substantive extra issue. A stochastic bit-parallel search for 19-gate circuits (18-prefix plus final OR) fitting these rows is running; no witness yet. Exact positive Petersen circuits have a standard 20-gate star-cover realization.

Petersen transitivity has simple explicit generators: simultaneous rotations of the two five-cycles, and swapping halves while multiplying each residue index by 2. These give an automorphism carrying any selected vertex to vertex 9, so the permutation quantifier can be eliminated from a restriction argument.

## Status audit / finite normalization

2026-11-24T17:59:10.953708+00:00

Source statement is the third premise of merged R_meta_2373_71. The first two premises are cofactor lower bounds at 15 gates (vertex false) and 10 gates (vertex true); our premise supplies the matching upper bound for the OR of two independent output signals. Importing R_meta_2373_71 is forbidden because only PEqualNP.Defs is allowed, and its reduction supplies no proof of this premise.

Finite normalization: every intermediate wire list has length at most 28. Replace every operand i by min i 28; 28 remains missing throughout, and every missing operand still reads false. This preserves each full wire list by induction over the gates. Outputs a,b can likewise be clamped. Independence witnesses moreover imply a,b<28, distinct; zero-singleton promise implies neither is an input, so 10<=a,b. Gate operations range over three possibilities and input lists have length <=2, giving a fully finite normalized domain.

Useful accepted patterns: R_meta_2940_1 normalizes BinaryCircuit indices, preserving evaluation and then pads to fixed length; R_meta_1932_1 proves min-index clamping with List.getD_eq_default. HasCircuitSize 9 (fun y => U ((Fin.lastCases v y) ∘ s)) (if v then 10 else 15) abbreviates the existential output-circuit conclusion. A fallback cut can separate generic finite encoding from the finite cofactor claim, but a structural gate-loss premise would be mathematically more useful than only bounded restatement.

- Added explicit finite witness lemmas `promise_essential` and `promise_cofactors_nonconstant`. All witness inputs have weight at most two, so only the low-row part of the approximation promise is needed. Awaiting Lean compilation.

## Toolchain setup

Pinned Lean v4.36.0 was absent and is now installed under /tmp/oec/pequalnp-pilot-38/elan. Source /tmp/oec/pequalnp-pilot-38/lean-env.sh for every Lean/lake/checker command. `lake exe cache get` exited 0, downloaded and decompressed all 9117 Mathlib cache files. Full output: /tmp/oec/pequalnp-pilot-38/mathlib-cache.log. No tracked configuration changes. Project definitions still need their first local build.

2026-11-24T18:00:23.906886+00:00 — OutputBounds.lean drafted (not yet compiled): generic fold length/input preservation and singleton-row argument give 10 <= a,b < 10+D.size, a != b. This result does not require the fan-in or size assumptions; it only needs the two independence witnesses and sparse-row agreement.

## counting_reduction

Proposed fresh-count reduction is in lemmas/CountingPremises.txt. Generic compiler includes original input wires, because a true cofactor creates a constant-true input costing one gate. Structural premise restricts to globally size-minimal circuits with <=19 gates and the sparse Petersen promise; conclude existence of automorphism/cofactor with <=10 or <=15 distinct nontrivial wire functions. Target proof appends OR to the two outputs, chooses a size-minimal equivalent circuit via natural-number well-ordering, applies count certificate, then generic compiler. Source premise lengths are 521 and 1060 characters (printed lengths still need checker).

- 2026-11-24T18:01:14.033570+00:00: Restriction.lean compiled with Lean v4.36.0, exit 0, no diagnostics. Contains vertex-transitivity, all-input essentiality, and nonconstant-cofactor lemmas. Root notified to review/push immediately.

Counterexample computation update: SAT encoding at `/tmp/oec/pequalnp-pilot-38/sat_synth.py` represents 19 AND/OR/NOT gates (18 prefix, final OR), using 91 care rows; 6042 variables, 135278 clauses. Constants false and true are free, yielding a superset of original circuits; binary operands may repeat, and arbitrary preceding wires are allowed. AND/OR operands are sorted, NOT uses repeated operand, final OR reads the last prefix gate (requires harmless dead-gate removal/copy padding normalization). No incomparability constraint is imposed. Known 20-gate Petersen witness satisfies every clause of the corresponding 20-gate encoding. Official Kissat 4.0.4 runs for 600 seconds with DRAT output; no solver verdict yet.

Exhaustive enumeration of 40 standard 20-gate star-cover circuits (five independent four-sets, eight assignments of edges internal to the complement) shows simple constant propagation gives best zero cofactor size 16 in all cases; best true cofactor size 11 in 20 cases and 12 in 20 cases. This supports the magnitude of the claimed gate savings but does not verify it for arbitrary circuits. Program/log: `/tmp/oec/pequalnp-pilot-38/restriction_counts.py`, `restriction-counts.log`.
