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

## New mixed-cover gap

Checked 2026-11-25T14:53:32.381998+00:00: `gap2583/lower_bound/MixedCoverGap.lean`, SHA256 19a1a42a301a7000db931591f2ee68ad2115f4f46a4d89984fedc4886cb27b45. Compiles/exports exit0; complete mixed-cover-gap.stdout has one unused-argument warning, stderr empty. Imports checked PlaneGeometry for scratch; MixedCoverGap.append.txt is inline text. Earlier MixedCover.lean is frozen separately at8996952a6c0a56ea08543b1c97f8a23f0ba99b852835c829d3c291edffac23b9.

New general theorem: if nonempty point set S and nonempty line set T have no incidences, |S|+|T|≤q²+1. Pick a nonincident p∈S,l∈T. The residual incidence graph on points off l except p and lines not through p except l is q-regular. Count incidences to bound the residual independent sets by q²−1, then restore p,l. Dual unique line intersection is derived from the posted axioms inside the proof.

Consequence: any bipartite vertex cover A,B with both A and B proper has |A|+|B|≥N+q. Thus a cost conversion to such a cover may lose up to q gates and still imply the desired canonical lower bound. The file proves this conditional cost conclusion; it does NOT prove a q-bound on arbitrary core conversion debt.

Computational check only: exhaustive point-subset enumeration for the standard projective planes over F2 and F3 confirms maximum mixed independent-set totals5 and10, with14 and26 maximizers respectively. JSON is mixed-cover-check.json. These computations are not part of the Lean proof.

Possible structural use, still unproved: a rectangle core (OR points on l) AND (OR lines through p), for incident p,l, has allowable singleton centers exactly p,l. Distinct rectangle cores OR-mixed before a top have allowed centers in the intersection of their endpoint pairs, hence at most one. This suggests cost-preserving normalization of a layer of rectangle junk gates; arbitrary nonlinear cores and their sharing remain open.
