# Counterexample strategy: L-meta-2583

## Definition audit
No immediate hypothesis/model defect found. The q>=2 and N=q^2+q+1 assumptions ensure at least seven points. The incidence assumptions form a symmetric 2-(N,q+1,1) design, hence the usual finite projective plane. ReadK is proof-tree multiplicity per prime implicant, not globally read-once.

## Quantitative target
The star circuit for q=2 has 27 gates: two ORs plus one AND for each of seven lines, followed by six ORs. A 26-gate monotone AO2 circuit would refute the replacement statement, once the existing read-1 lower bound is copied/proved locally.

Useful checked-file references (cannot import these unless desk allows, but proofs can be copied):
- lean/PEqualNP/Outside/L_meta_7639.lean (1977 lines): for C4-free bipartite E with a perfect matching, read-1 implies |E|+N <= C.size+1.
- lean/PEqualNP/Outside/L_meta_7684.lean (1126 lines): a vertex cover gives an AO2 read-1 construction with at most |E|+|left cover|+|right cover|-1 gates.
- lean/PEqualNP/Outside/L_meta_2237.lean: general graph C4-free read-1 lower bound via a vertex cover.

Existing refutations L_meta_2797 and L_meta_2799 only disprove conjectured size <=2N plane circuits. They do not refute this step.

## Planned finite search
Use monotonicity: checking all minimal true assignments (21 incidence edges) and maximal false assignments suffices for full truth-table equivalence of monotone circuits. Start from the 27-gate star circuit and search smaller AO2 circuits by gate mutations. A negative heuristic search is not a proof of impossibility.

## Exhaustive q=2 incidence check
Enumerated all 30 labelled-point Fano designs with unlabelled lines as exact covers of the 21 point pairs by triples. Each has point degree three, each pair of distinct lines intersects once, and exhaustive 2^14 vertex-cover enumeration gives minimum seven. Full case data: /tmp/oec/pequalnp-pilot-144/counterexample/fano_designs.json. This is a Python check, not a Lean theorem.

## Baseline Lean source
Prepared /tmp/oec/pequalnp-pilot-144/counterexample/FanoBaseline.lean (101 lines), uncompiled while root installs the toolchain/cache. It states finite incidence axioms, an explicit 27-gate AO2 circuit, exact function equality, per-edge read-1 checks, and derives IsReadK from prime-implicant minimality. No claimed check until compilation succeeds.

## Near-witness validation
The best 26-gate candidate omits point 4 / line 3. Exhaustive evaluation of all 16,384 inputs shows 47 false negatives and zero false positives, so it is not a counterexample. Full diagnostic: /tmp/oec/pequalnp-pilot-144/counterexample/near-witness-validation.json.

## Heuristic run result
{"finished": true, "elapsed": 240.000115102, "iterations": 65730969, "restarts": 2192, "best": 1}
Full log and source retained in the scratch counterexample directory. This run is heuristic and does not prove absence of a 26-gate circuit.

## Checked partial (follow-up)
FanoDesign.lean compiled successfully with Lean 4.36.0 via lake env lean, exit 0. Full output design-build-2.log is empty. It checks the Fano incidence axioms, explicit 27-gate circuit size, and AO2 validity. Full semantic/read-1 baseline remains unverified: direct finite correctness checking was terminated for memory use; replacement symbolic check was terminated on root instruction after lease loss. No further proof/search work is running.
