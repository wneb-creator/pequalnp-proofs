Fano-plane counterexample search for L-meta-2583

A correct AO2 circuit of at most26 gates for the q2 Fano incidence function would refute the posted Read1 normalization claim: L_meta_7639 gives Read1 size at least27 using the21edges and perfect matching; L_meta_7684 gives the standard27-gate Read1 construction. No counterexample has been found.

The chosen incidence relation is dot(p+1,l+1)=0 over GF(2), with point and line labels0..6. Its21edges, line degree3, unique lines through distinct point pairs, and matching(1,0,3,2,4,6,5) were checked computationally. FanoFiniteData.lean is the small formal-data helper.

The monotone synthesis instance has exactly58 complete boundary inputs:21minimal true edge pairs and37maximal independent sets. All16,384 assignments were checked to lie above a minimal true row or below a maximal false row. The generated26-gate CNF has26,730 compressed variables and503,709 clauses, including21,308 pairwise onehot clauses. A direct27-gate star cover shortened to26 gates gives a seed violating exactly one output clause, with47 errors over all inputs.

A phase-seeded CaDiCaL run started14:55:17 UTC with a45-minute limit. Full stdout and stderr are retained in scratch/plane. The decoder reconstructs an actual AO2 circuit, removes only unreachable padding, checks every input, and evaluates joint capped proof-tree multiplicities for each edge. Any SAT model must pass that decoder and independent root review before it is called a counterexample. An UNSAT solver response under these structural constraints is not by itself a Lean proof.

Independent review by reduction_strategy passed14:55–14:56 UTC: plane axioms and boundary completeness recomputed over all inputs; all21,308 onehot clauses found in the CNF; compressed indices are collision-free; decoder validates all inputs, AO2, size, and joint Read1 vectors; mocked seed correctly reports47 errors. Preserved sources and small validation files are in results/orch/plane-counterexample/. No large CNFs or binaries are committed.

FanoFiniteData.lean kernel-check passed at15:00 UTC, exit0, empty full diagnostics. It proves21edge cardinality, degree3 on both sides, unique common line for distinct points, no rectangle, and an involutive perfect matching. No native_decide, axioms, or extra imports.

2026-11-25 15:08 UTC — Root reported another unexpected desk HTTP410. Stopped the mainSAT and annealer by SIGINT; no SAT, UNSAT, or zero-error circuit was found. Both drivers saved interruption timestamps. Complete solver/heuristic stdout and stderr, sources, canonical seed, and the21 one-missing-edge approximate circuits were preserved in this folder. Read1-cut and6AND/freeOR encoding were prepared and independently reviewed but never launched. No search process remains active under this agent.
