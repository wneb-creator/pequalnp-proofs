# L-meta-2583 lower-bound route

Exact target: on a projective-plane incidence relation, every AO2 circuit has an equally small READ1 implementation. READ1 is one simultaneous proof tree per prime implicant; it is stronger than separate point-single and line-single properties.

## Existing checked components

- L_meta_7684 constructs a READ1 AO2 implementation for any bipartite vertex cover A,B with size at most |E|+|A|+|B|-1 (1126 lines).
- L_meta_4897 gives the reverse inequality from any READ1 AO2 circuit on a C4-free bipartite graph: there is a cover with |E|+|A|+|B| <= C.size+1 (1961 lines).
- L_meta_7639 combines that lower bound with an incident permutation/perfect matching to get |E|+N <= C.size+1 (1977 lines).
- L_meta_1942 / L_meta_2058 / L_meta_2581 only supply constant-factor bounds under READ2 or READ3.
- L_meta_1660 proves the generic input-dependency lower bound 2N <= C.size+1 even with promise soundness, far weaker than the target.
- L_meta_4616 point_card (line469) or L_meta_3499 lines_card derive point degree q+1 from the posted incidence assumptions.

Thus, once regularity and a perfect matching are supplied, the target is equivalent to the sharp unrestricted monotone lower bound N(q+2)-1; for Fano q2 this is27 gates. No existing unrestricted sharp lower bound was found.

## Structural obstacles already exposed by checked files

- L_meta_4849 refutes the claim that every AND gate of every least monotone circuit on a triangle-/C4-free graph is below the edge function. Do not assume this normalization for an arbitrary minimum.
- L_meta_7241 proves the exact edge-plus-cover lower bound if every AND gate is false on nonedges; that hypothesis is the missing hard step.
- L_meta_3760 rules out exactly one junk AND gate in a least bipartite C4-free circuit; it leaves two or more.
- L_meta_3706 gives an edge-plus-cover lower bound with an explicit penalty for reread edges.

The repository note notes/note-1-edge-function-exact-size.md cites Jukna, ECCC TR05-021, Disproving the single level conjecture, as relevant literature. Original paper not read under current allowed-host restrictions; applicability remains UNVERIFIED. Allowed GitHub web search found no useful primary mirror on2026-11-25.
