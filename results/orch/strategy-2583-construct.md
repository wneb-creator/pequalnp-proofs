# L-meta-2583 construction route

## Read-k semantics

`PEqualNP.ReadK.IsReadK n C 1` means every prime implicant has one joint proof tree reading each of its variables at most once. It is not a global fan-out bound. The separate scalar minima `eachReadsAtMost` are strictly weaker and cannot establish the goal. `TopForm.IsAO2` requires AND/OR only, exactly two inputs per gate, and backward reads.

## Checked constructor

Preferred artifact: `results/orch/lemmas/PlaneStarExact2583.lean` (664 lines), adapted from the self-contained `Own.upper` block of checked `L_meta_2393.lean` (lines4174–4805). Imports are Mathlib and PEqualNP.Defs only. Namespace is `PEqualNP.Outside.L_meta_2583_aux` with helper subnamespace StarExact.

`plane_star_exact` assumes 0<N and every line contains q+1 points. It constructs a correct incidence circuit D, proves IsAO2 and IsReadK(...,1), and proves exact gate count D.size+1=N*(q+2). In ordinary terms: each line has q OR gates to collect its q+1 points, one AND with its line input, and the N star outputs need N−1 OR gates.

`normalize_from_bound` converts the numeric lower bound N*(q+2)≤C.size+1 to exactly the existence conclusion of L-meta-2583. The plane-size hypothesis implies 0<N.

Validation: queued lake env lean exited0 with empty diagnostics. Logs `/tmp/oec/pequalnp-pilot-121/construct2583/exact-build-001.stdout` and `.stderr`. SHA256 dd6e73b3f2a7b599d143eed3e8726f87f833001f9b596e5a4f741612f9d5ec1a. No sorry, axioms, native_decide, forbidden root identifier text, or quotes.

Alternative (larger): `StarConstruction2583.lean`,1179lines, adapted checked L_meta_7684. It gives arbitrary bipartite star-cover construction, a new incidence-card lemma, plane size upper bound, and the analogous normalization condition. It also compiles, with inherited harmless linter warnings. The exact plane-specific file is preferred for final integration.

## Bounds found and remaining obstacle

Checked L_meta_4897 proves the edge-plus-cover lower bound only for read-1 circuits. Checked L_meta_7639 proves E.card+N≤C.size+1 for C4-free bipartite incidence with a perfect matching, again only under read-1. A plane has q+1 regularity on both sides and hence a perfect matching. Therefore these results show the constructed read-1 circuit is optimal among read-1 circuits, but using either to bound arbitrary C would be circular.

Checked L_meta_6369 supplies the analogous graph read-1 bound. L_meta_7344 repairs arbitrary quadratic circuits into read-1 circuits with a factor3 overhead and a penalty for unread prime implicants; it does not meet the no-larger requirement.

No unconditional N*(q+2)≤C.size+1 lower bound was found in the repository. The target is effectively the sharp unrestricted monotone lower bound for projective-plane incidence. The source sketch's remaining block-cost claim is exactly the obstacle; the constructor itself is settled.
