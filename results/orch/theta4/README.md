# Theta4 finite search for L-meta-2056

Graph: four internally disjoint length-three paths between vertices 0 and 1, with path i using vertices 2+2i and 3+2i. Ten vertices and twelve edges. Complete monotone boundary: twelve minimal-true rows and seventeen maximal-false rows.

The sixteen-gate star control was checked on all 1024 assignments with zero errors. The fixed SMT control also passed CaDiCaL, model reconstruction, all 824 original assertions, all boundary rows, and all 1024 assignments. Directed dominance preserves this control.

The first unrestricted fifteen-gate query reached its 300-second native solver limit with UNKNOWN (exit 0). It does not establish a lower bound. Full solver stdout and stderr are retained here. The successor combines directed dominance with the independently audited 48 graph automorphisms and full lexicographic symmetry normalization; its native 600-second run began at 16:14:35 UTC.

The additional cover-demand JSON concerns an unproved circuit abstraction only. It is diagnostic data, not a circuit lower bound or Lean theorem. No fifteen-gate witness has been found.

The combined dominance and full-symmetry constraints also pass a stronger positive control: the sixteen-gate star was canonicalized over all 48 input automorphisms and legal greedy topological orders, then fixed in the combined query. All 871 original assertions passed and all 1024 assignments matched. This confirms satisfiability at sixteen gates under the exact combined normalizations.

A potential fifteen-gate theta witness would only be a necessary core result. Lifting it to the five-point twenty-three-gate patch requires suitable internal factors or a separately checked construction; simply adding private lines into connecting-line inputs introduces spurious edges.

The dominance-plus-full-symmetry successor also reached its native 600-second limit with UNKNOWN (exit 0): 48,823 CNF variables and 436,251 clauses. Its full stdout, stderr, wrapper logs, and metadata are retained here. No fifteen-gate witness or lower-bound result was obtained. Theta4 solver work stopped after these two bounded runs; the agent moved to constructive full-plane CEGIS.
