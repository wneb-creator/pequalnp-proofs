# Frozen cycle instances for L-meta-3754

Vertices are Fin n, indexed 0 through n-1. The generating edge list is exactly [(i,(i+1)%n) for i in range(n)], including the final oriented pair (n-1,0). Use the undirected simple graph given by EdgeOwnership.edgeGraph from those pairs. The target Boolean function is OR over those edges of xi AND xj. Bipartition is i modulo2. For a mask x, bit i is the value of input xi; no vertex renumbering is performed.

The independent plain-Python enumeration tests every one of the 2^n assignments. A maximal false assignment is false for the target and becomes true upon setting any missing bit. It also independently checks every induced vertex subset has at most as many edges as vertices, bipartition correctness, and that any two distinct vertices have at most one common neighbor (no four-cycle).

C8 has exactly10 maximal false masks:
37,41,73,74,82,85,146,148,164,170.

C10 has exactly17 maximal false masks:
149,165,169,293,297,298,329,330,338,341,586,594,596,658,660,676,682.

The JSON also records the C6 and C12 counts (5 and29). These are independently reproducible finite computations, not Lean proof terms. The root and ledger agents are preparing corresponding kernel-checked graph and counting lemmas. Standard clean star-cover upper sizes are8 forC6,11 forC8,14 forC10,17 forC12; no lower-bound theorem is asserted by this bundle alone.
