## Checked formula lower bound

At17:20:34UTC, `lemmas/KWFormula.lean` passed Lean and exported an olean. It imports only PEqualNP.Defs, has161lines/8291bytes, SHA256 `4a367c8e74da00361e448a190f771d30ac0f4220ebe297bb64cb5339214bfefb`. Complete stdout/stderr are archived as `kw-formula-checked.*` and are empty.

The exact19edge target has a signed Karchmer–Wigderson rectangle weight certificate with19positive edge assignments and36maximal independent negative assignments. All weights are integers after multiplication by4. Total weight is104; every monochromatic input-leaf rectangle has weight at most4. The generic AND/OR formula induction gives `26 ≤ f.leaves` for every positive DMFormula14 computing the target. The finite rectangle bounds, total, and all positive/negative target evaluations were checked in Lean, not merely by the exploratory LP.

This proves a25binary-gate formula lower bound. It does not prove that every monotone circuit needs25gates: an internal gate may be shared and hence appear more than once when a circuit is unfolded into a formula. Any24gate counterexample must exploit such sharing. The exact rational LP generator and its JSON weights are retained as kw_formula_lp.py/.json, but the Lean proof does not trust the solver.

## Structural route still open

The graph is the Fano incidence graph with two disjoint incidences removed. Its19edges and perfectmatching7 give a25gate star-cover construction. The degree2 vertices are0,2,7,12; the other10vertices have degree3. Simple input-read counting only forces at least3 singly read inputs in a connected24binary-gate circuit. Those inputs need not be among the four degree2 vertices. C4-freeness prevents ordinary shared two-neighbor star sums, but it does not by itself rule out mixed intermediate functions filtered later. The earlier local irreducibility/no-garbage shortcuts remain insufficient.

17:39 UTC progress: The 600-second OR-cost search completed8,050,000 updates, best18 OR gates, corresponding to a full-cube-validated25-gate circuit. This is a heuristic negative search, not a lower bound. Complete artifacts are in search-or.

The exploratory L910 six-AND occurrence model initially used total Boolean gate orientations and was UNSAT. That model was too strong: the checked L910 lemma permits Option Bool orientations. The corrected three-valued model is SAT and has an independently checked abstract model on all36 maximal independent rows. Thus no new AND-count lower bound was obtained. Both runs are preserved with this correction in and-pattern.

The newer L9774 graph is not isomorphic to this graph (its degree-two vertices induce one edge; ours induce none). Its generic surplus machinery does apply after regenerating geometry. PrivateProjection.lean now compiles and exports against UpstreamGraph, proving44 conditional Bzero=0 exclusions. Its exact SHA is44b9b39221be13e8502eeaf2b3393ee1b2201151c98159b58e4f8373e8b413f4. Independent finite/generic reviews passed. This includes pure-side masks127/16256. The full44-lemma source is40,391 bytes; only13 orbit-representative exclusions are needed in a size-conscious final assembly.

Individual and globally restriction-consistent projected_count tests did not exclude Bplus10/Bzero1 sides; the global196-variable abstraction was SAT. Root's later paired-exact layout certificates did close these finite abstract cases. No structural conclusion is claimed from the failed simpler abstraction.

Independent full-case audit passed: all16,384 masks recomputed from actual Lean weights; cap9 none, cap10 exactly5, cap11 exactly117; all4 automorphisms and37 disjoint orbits checked. See REVIEW-case-coverage.md and case-coverage-independent.json. The cap10 residual sizes are3,0,2,0,3, respectively; mask4757 has cardinality6. GraphSymmetry.lean reviewed at ef9df681b3e74cae0bdf516a6fbc73ca6c0b83d9f4fedb2299d1be75e0126b9a: correct direct-image source-to-representative transport, no unproved surplus invariance assumed. Final certificate assembly/kernel verification remains root's active work.
