# L-meta-2583 lower-bound route

Exact target: on a projective-plane incidence relation, every AO2 circuit has an equally small READ1 implementation. READ1 is one simultaneous proof tree per prime implicant; it is stronger than separate point-single and line-single properties.

## Existing checked components

- L_meta_7684 constructs a READ1 AO2 implementation for any bipartite vertex cover A,B with size at most |E|+|A|+|B|-1 (1126 lines).
- L_meta_4897 gives the reverse inequality from any READ1 AO2 circuit on a C4-free bipartite graph: there is a cover with |E|+|A|+|B| <= C.size+1 (1961 lines).
- L_meta_7639 combines that lower bound with an incident permutation/perfect matching to get |E|+N <= C.size+1 (1977 lines).
- L_meta_1942 / L_meta_2058 / L_meta_2581 only supply constant-factor bounds under READ2 or READ3.
- L_meta_1660 proves the generic input-dependency lower bound 2N <= C.size+1 even with promise soundness, far weaker than the target.
- L_meta_4616 point_card (line469) or L_meta_3499 lines_card derive point degree q+1 from the posted incidence assumptions.

Thus, once regularity and a perfect matching are supplied, the target is equivalent to the sharp unrestricted monotone lower bound N(q+2)-1; for Fano q2 this is27 gates. No existing unrestricted sharp lower bound for all q was found.

## Fano case resolved by a hidden repository helper

Detailed source inspection (not just final theorem statements) found that L_meta_7997 contains an unrestricted bound:

- `heawood_lb_27` at line9341: every Monotone2 circuit computing its Heawood edge function has at least27 gates.
- `fano27` and `ao27` transfer that result to exactly the cyclic incidence relation p=l or p=l+1 or p=l+3 on Fin7 used by our SAT attempt.
- The posted final theorem L_meta_7997 is weaker: its proof ignores distinct-operand and reread hypotheses and directly invokes `ao27`.
- All auxiliary variable sections close before this theorem. Agent status_review independently confirmed no hidden Read1 assumption.

Consequently the26-gate Fano counterexample search cannot succeed. Parent and circuit_search were notified immediately. This result does not settle q>=3.

Compiled partial `FanoReadOneBound.lean` gives only Read1>=27, plus concrete Fano geometry. It is correct but weaker than the discovered helper. Frozen hash61570a7a4558d5248e4aee15295dfe37e8e94556a601e99a1c5e36a9bdd73229,2014lines; build exit0.

New `SingerThreeReadOneBound.lean` specializes the same checked general matched bound to Fin13 difference set{0,1,3,9}. It proves52 edges, degree4, unique common line, and Read1>=64. It compiled exit0 and was independently approved at hash7913fd344ac017ac85499eae7dc928534d5ac04bd67584454ece02f4377707f6,2019lines. Parent notified for immediate preservation. Complete compiler logs are singer-bound-build.stdout/.stderr in the2583 scratch directory.

Order3 census: L4803 gives64 only under no nestedAND; L2613/L2615 assume everyAND below the target. L9071's output<26 assumption is contradictory for its target. The reviewer also found L4101 requires Productive, L1500 requires line-degree1, and L8791 requires no junk gates. None is an unrestricted q3 bound.

## SAT normalization and critical-row orbit seed

A sound normalization: any internal wire true on exactly one minimal true edge can be replaced at the same one-gate cost by the direct AND of that edge's primary inputs. Monotonicity makes the new function pointwise smaller, and it agrees with the old wire on every minimal true edge assignment. The final output therefore still computes the edge function. Agent proof_route independently confirmed the argument and owns a possible formalization. Equality of a gate's mintrue profile with one child alone does not permit deleting an AND: the child may accept false rows.

The script scratch/gate-elimination/2583/q3_orbits.py enumerates projective collineations from the Singer model over F3[a]/(a^3-a-1). The108 collineations fixing edge(0,13), together with a polarity, partition704 maximal false assignments into21 orbits. Data in q3-edge-stabilizer-orbits.json contains21 representative rows and complete orbit lists. This is a CEGAR initialization heuristic only: a circuit is not assumed invariant, so representative checks alone are insufficient. Any witness must be checked on all704 maximal false rows and52 minimal true rows (or the complete truth table).

## Structural obstacles already exposed by checked files

- L_meta_4849 refutes the claim that every AND gate of every least monotone circuit on a triangle-/C4-free graph is below the edge function. Do not assume this normalization for an arbitrary minimum.
- L_meta_7241 proves the exact edge-plus-cover lower bound if every AND gate is false on nonedges; that hypothesis is the missing hard step.
- L_meta_3760 rules out exactly one junk AND gate in a least bipartite C4-free circuit; it leaves two or more.
- L_meta_3706 gives an edge-plus-cover lower bound with an explicit penalty for reread edges.

The repository note notes/note-1-edge-function-exact-size.md cites Jukna, ECCC TR05-021, Disproving the single level conjecture, as relevant literature. Original paper not read under current allowed-host restrictions; applicability remains UNVERIFIED. Allowed GitHub web search found no useful primary mirror on2026-11-25.
