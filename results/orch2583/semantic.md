# L-meta-2583 semantic normalization notes

- 2026-11-25T14:56:46.823071+00:00: ReadK1 means proof-tree multiplicity on each prime implicant, not global wire fanout. Generic AO2-to-least-top-form normalization is already checked in L_meta_8567; L_meta_4543 also minimizes Ustar. The missing step is the cost of blocks containing junk AND gates, not normalization to TopForm.
- L_meta_7684 constructs read1 circuits from bipartite covers; L_meta_4897 gives the matching read1 lower bound for C4-free graphs. The few_nots agent has now specialized these to show the posted statement is equivalent to the unrestricted lower bound N*(q+2) <= C.size+1.
- Naive multilinearization is not a size-preserving argument: a repeated-variable subtree may filter nonedges shared with other outputs of the block. No general elimination theorem found.
- New checked partial SemanticTripleBlock.lean: for E=((P intersect Wp) times L) union (P times (L intersect Wl)), no rectangle implies a cover U,V with |E|+|U|+|V| <= |P|+|L|+|Wp|+|Wl|. This is the pair core of three OR factors, with no OR sharing charged. Kernel build passed; independent review passed; root notified for preservation.
- SemanticClauseSuffix adds the pure-factor extraction from below-incidence semantics and the exact pair-core identity; compilation is in progress after a minor Finset nonempty simplification fix.
- Combinatorial agent owns generic rectangle cover and an added-C one-junk block. Few_nots owns two product branches under one common filter. Toolchain agent owns a sparse single-reader OR cut criterion.
