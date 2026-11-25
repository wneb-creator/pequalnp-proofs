Counterexample search for L-meta-2590

Target: a monotone Petersen circuit with at most 19 gates. The posted Monotone2 class permits fan-in at most two, constants, and invalid reads. The current search uses the strict AO2 subclass: AND/OR only, exactly two earlier inputs per gate. Any returned witness is valid for the posted class. Search completeness would additionally need the usual constant and unused-gate normalization; no global Lean lower bound is claimed from solver results.

The exact monotone specification has 30 rows: 15 positive edge assignments and 15 maximal independent sets. The latter match the rows in checked reduction R_meta_2590_1. Every SAT candidate is independently evaluated on all 1,024 inputs immediately.

The general graph theorem L_meta_2237 proves that a read-1 AO2 circuit on a C4-free graph has edge count plus some vertex-cover size at most circuit size plus one. Petersen has 15 edges, no four-cycle, and minimum vertex-cover size 6. Thus a 19-gate strict witness must lack a squarefree proof on some edge. The exact squarefree DP from the previous task is reused with 10 linear-input bits and 15 pair bits per wire; its recurrence uses OR-only linear reachability, not ordinary singleton truth.

Validation passed: the standard 20-gate star-cover circuit computes the function on all inputs and has every squarefree edge proof; requiring it to miss one gives UNSAT. An equivalent but deliberately redundant 22-gate test circuit computes the same function and lacks squarefree proofs on exactly the three edges of its first star. The latter is validation data, not a refutation.

The graph's 120 automorphisms give two unordered-pair orbits: edges (15) and nonedges (30), represented by (0,1) and (0,2). Productivity excludes a first AND on a nonedge. Three sequential cases completed, 120 seconds each: incident AND, incident OR, and nonincident OR. Each gate must be true on some positive edge row, and at least one output edge proof must fail read-1. Other normalization restrictions are output-last, every gate structurally used, and sorting the two commutative operands.

Sources, hashes, data, and completed-case stdout/stderr are preserved in search/. The checked priority split R_meta_2590_932 could further strengthen later runs: first incident OR; otherwise nonincident OR with no raw incident OR anywhere; otherwise incident AND with no raw OR of distinct inputs anywhere.


Completed first split: incident AND, incident OR, and nonincident OR all returned UNKNOWN after approximately 120 seconds per case. Every case used all 30 extremal rows, exact squarefree-proof deficiency, productivity, strict earlier wires, sorted commutative operands, and all gates structurally used. No 19-gate witness was found. Complete diagnostic streams and result JSON are saved in search/.

The parent received HTTP 410 on the lease renewal and stopped this gap at approximately 15:22 UTC. No owned solver or driver remained active when the STOP arrived; the first split had already completed. No further encoder changes, validations, or searches were started.

Planned but NOT implemented next split: add an optional raw-primary-OR exclusion based on checked priority reduction R_meta_2590_932. Use incident OR with no additional exclusion; nonincident OR forbidding all incident raw primary OR gates; incident AND forbidding all raw primary OR gates on distinct inputs. These syntactic conditions are weaker than the reduction's semantic wire exclusions. Also optionally add at least six AND gates, based on checked L_meta_635 after the free-OR-region translation. A sequential-counter encoding was planned; no claims depend on that unwritten implementation.

Before STOP, circuit_search reported a 24-gate exact circuit using only 13 OR gates and 11 AND gates, disproving the tentative unconditional OR-count lower bound 14. The checked simplified 23-gate version and independent validation are elsewhere in this results directory. The agent additionally identified an absorption simplification that appears to save one AND gate, but this 22-gate variant was not written or checked before STOP. No 19-gate counterexample or proof of the target was obtained.
