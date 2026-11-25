# Counterexample route for L-meta-2602

## Semantics checked

Circuit.wires is an append-only fold and Circuit.eval reads its output with false default. Proper earlier binary inputs rule out cyclic or future-wire tricks. Correctness on the pair {0,13} forces output into the actual wire range, so the derivative witnesses cannot assign an unconstrained output value.

## Small finite search

results/orch/small_double_search.py searches AND/OR circuits over complete Boolean truth tables together with both formal derivative values at the chosen edge singletons. States retain wire signatures with multiplicity up to two; repeated semantic wires remain legal when their indices differ. Results are computational evidence, not Lean checks.

- One edge, two inputs: first double-re-read circuit at 3 gates; ordinary minimum 1.
- Two-edge star, three inputs: first double-re-read circuit at 4 gates; ordinary minimum 2.
- Two disjoint edges, four inputs: first double-re-read circuit at 4 gates; ordinary minimum 3. Explicit circuit: t=x*y; u=t OR z; v=t OR w; output=u AND v. Thus a claimed two-gate double-re-read penalty is false.

## Near counterexample at 65

The ordinary plane star construction has 64 gates. Let t combine twelve column stars, and let the final star be a AND b with neither factor true on the singleton point0 or singleton line0 (choose a column other than0 nonincident with point0). Replacing t OR (a AND b) by (t OR a) AND (t OR b) costs one extra gate, preserves the Boolean function by distributivity, and forces both derivatives at edge(0,0) to zero. This constructs a 65-gate double-re-read circuit, so the desired lower bound65 is potentially tight.

No 63- or64-gate counterexample found.

## Lean-checked 65-gate witness

2026-11-25T03:07:16.110859+00:00: results/orch/lemmas/Counterexample.lean passed lake env lean with exit0. The lemma tightness65 uses the exact posted existential, removing the negation and changing only the upperbound64 to65. It proves all proper-input, incidence-function, and two derivative-witness clauses. Full build output is /tmp/oec/pequalnp-pilot-60/tight-lean-final.log. This establishes feasibility at65 gates. It does not prove a minimum or refute L-meta-2602.

## Follow-up: global AND bounds

Generic dirty-AND strictness fails even for bipartite C4-free P4: (x OR z) AND (y OR z) AND (y OR w) computes xy OR zy OR zw with2ANDs, the matching/cover number, but its first AND is dirty (true on singletonz). The excess is in ORcount3 versusordinary2.

Repository L_meta_1006 refutes ANDcount≥cover under maximal-independent-set boundary tests, using a nonbipartite 11-vertex 6-AND graph with cover≥7. Crucially its circuit rejects the actual graph edge {6,7}; it does not compute the full edge function and does not refute a full-function lower bound.

The Fano proof L_meta_910 is structural. Its generic no_cover_gt lemma handles signed literalsets ofwidth≤2, with partial-assignment separation of every selected subset ofatmost2 vertices. The plane has704 maximal independentsets,197 throughapoint,52 throughapair,8or16 throughatriple. Assuming≤12ANDs, its coding method onlyforces literalwidth≤4, not2, so substantial new combinatorics is needed.

Unsigned cover-free reduction is false: S1={a+,b+}, S2={a−,c+}, S3={b−,c−} satisfies signed separation for ALL selected subsets ofthe3words, while unsigned supportS1 iscovered bysupportS2 union supportS3. Exhaustive3-valued assignments checked in signed-cover-counterexample.json. Thus simplepacking must count24signed literals, not12gatecoordinates.

CORRECTION: L_meta_1006 onlychecks maximalindependent-set boundary behavior. Itscircuitrejects graph edge{6,7}, so it doesNOT refute AND≥cover forfull edgefunction correctness. The finite3×3bipartite census checksfull truth tables andfoundnocounterexamplewith≤2ANDs.

### Fooling-set AND lower bound: evidence, not proved

The exact census `and_fooling_small.py` checked all 512 bipartite 3×3 graph functions with arbitrary free ORs and at most two AND gates. It enumerated 1,415 first-gate functions and 4,465,825 possible second-gate operand pairs. Of the graph functions, 356 were realized; none had a fooling set larger than its AND count. The complete result is in `/tmp/oec/pequalnp-pilot-60/and-fooling-small.json`.

The heuristic `and_fooling_search.py` evaluated two million three-AND circuits on eight variables, searching for a bipartite quadratic output with a diagonal fooling set of size four. It found no counterexample. The best candidate accepts every diagonal pair and has no forbidden cross-pair collision, but accepts four higher-degree inputs not justified by its edge pairs. This illustrates why pair behavior alone is insufficient. This search is not exhaustive.

A proof of fooling-set size ≤ AND count for full bipartite quadratic functions is still missing. First-birth rectangles can contain nonedges subsequently filtered by later AND gates. The global full-function condition must be used to control those filters; the usual rectangle-cover injection does not directly apply. No applicable primary-source theorem was located in the allowed-host web search.

The generic signed-code route also needs care: signed words 000, 011, 101, 110 on three coordinates satisfy partial-assignment separation of every selected subset of at most two words, despite having four width-three words. Thus a blanket extension from width≤r to width≤r+1 would be false already at r=2.

### Exact SAT encoding and safe symmetries

`and_count_sat.py` represents each AND operand as an arbitrary OR of input variables and earlier AND gates; the output is an arbitrary OR of AND gates. The core selector CNF was independently reviewed by structural_proof. L_meta_563 supplies singleton-stripping normalization and disjoint bare-variable sides for arbitrary circuits, without a clean-gate hypothesis. Bare output variables are impossible for a target rejecting singletons. Padding with dead gates realizes smaller AND counts.

The full four-by-four graph-function search with a diagonal fooling set of size four and three ANDs was UNSAT in 0.70 seconds. Four ANDs was SAT, and the extracted circuit was checked independently on all256 inputs. The five-by-five/four-AND instance timed out at60 seconds. These are solver outcomes, not Lean proofs.

For the plane, minimal true edges52 plus all704 maximal false inputs suffice for full correctness by monotonicity. The initial twelve-AND CNF has137604 variables and608064 clauses. Optional row cuts derive from injective zero-certificate choice codes:197 rows contain each variable,52 contain each same-side pair,70 contain each cross nonedge pair. Hence twelve ANDs force occurrence-union sizes at most4,6,5 respectively. Optional operand ordering uses commutativity only.

Optional positive-use constraints are justified by deleting gates that are false on every minimal true edge. Replacing such a gate by false leaves all minimal true outputs unchanged and only shrinks the function elsewhere. Repeated pruning preserves the full target; padding can duplicate any surviving positive gate. In the first remaining gate, some incident point-line pair occurs on opposite bare sides. Explicit incidence automorphisms carrying each of the52 flags to(0,0) were generated and checked on all169 incidences. Thus a first-flag anchor is a valid symmetry after positive-use normalization. The generator is `plane_automorphisms.py`; a finite Lean certificate is being checked separately.
