# L-meta-2583 lower-bound route

Updated 2026-11-25T14:46:07.925733+00:00

ReadK.IsReadK n C 1 is a joint proof-tree property on each prime implicant, not a bound on global variable fanout. For every incidence pair, a Read1 witness tree has exactly one point leaf and one line leaf. Repeated variable reads elsewhere are allowed.

Existing checked ingredients:
- L_meta_7684: a bipartite vertex cover A,B gives an AO2 Read1 circuit of size at most |E|+|A|+|B|-1.
- L_meta_4897: for C4-free bipartite E, every already-Read1 AO2 circuit yields a cover with |E|+|A|+|B|≤size+1.
- L_meta_7639: with a perfect matching this implies |E|+N≤Read1 size+1.
- L_meta_8805 lines890–974: projective plane point regularity and the cover lower bound N≤|A|+|B|. This avoids Hall/matching entirely.

Thus the posted no-larger normalization is equivalent to the exact unrestricted monotone incidence lower bound N(q+2)-1. Existing Read2/Read3 estimates L2058/L2581 are only constant-factor Ω(Nq), and do not solve this exact normalization. L8805 itself only establishes unrestricted 3N≤size+1.

## Checked component

`/tmp/oec/pequalnp-pilot-99/gap2583/lower_bound/PlaneGeometry.lean` (121 lines), SHA256 b0809d2989de916107b647fe2bb2a6b6a2c2b882ad8075ac1c5c4dfd3e49a107. Only import PEqualNP.Defs. Compile/export exit0; complete stdout/stderr are empty in plane-geometry.stdout/.stderr. Module namespace PEqualNP.Outside.L_meta_2583.PlaneGeometry.

Contains lines_through, cardL, cardR, cover (adapted from L8805), and edges/edges_card/no_rectangle/cover_edges wrappers. Exact posted plane assumptions imply every point has q+1 incident lines, incidence edge count N(q+1), C4-freeness, and every bipartite vertex cover has at least N vertices. Library agent is integrating with Read1Cost; sat_encoding owns the canonical constructor.
