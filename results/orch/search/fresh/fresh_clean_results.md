# Saturated-meeting finite status filter

These are external, reproducible arithmetic diagnostics conditional on the mathematical carrier and terminal-marking arguments. There is no Lean certificate for them. The compilation of the separate generic lemmas does not certify this census.

The program fresh_clean_prep.py constructs secant-only point modules of PG(2,3), and the nine-point affine module. Points are permuted through their full stabilizer when reducing eligibility masks to orbits. For the affine module the explicitly generated AGL(2,3) has 432 elements. For the selected projective point subsets only the incidence automorphisms of the compressed core are needed. Present row sets remain arbitrary within each representative, and orbit multiplicities restore the full labelled totals. To regenerate, place the companion programs fresh_modules.py, fresh_case_charge.py, fresh_affine_charge.py next to fresh_clean_prep.py and run it with Python 3. Compile fresh_clean_census.cpp with a C++20 compiler and pass each generated .in file on standard input.

The C++ calculation factorizes the two color choices by the count z of singleton-empty reservations. For each possible present-row set it counts the exact missing-ineligible requirement, the necessary pure extra surplus of every opposite vertex, then tests the upper bound on each full carrier. Each saturated eligible vertex with two or more eligible neighbors is marked. A joined marked point and marked line is impossible by the clean-meeting argument. The terminal-marking bound for degree-two vertices imposes a conflict only if the common neighbor has at least three compulsory exits. It computes the minimum set whose deletion removes these conflicts by direct submask enumeration. The program counts the number of full labelled statuses surviving all necessary conditions, not the number of circuits.

| core | points | secants | edges | one-below gates | before clean-meeting | after |
|------|--------|---------|-------|-----------------|----------------------|-------|
| affine order three | 9 | 12 | 36 | 43 | 4,009,631 | 3,976,799 |
| six-point type 2 | 6 | 9 | 21 | 25 | 3 | 0 |
| seven-point type 0 | 7 | 11 | 26 | 31 | 156 | 0 |
| seven-point type 1 | 7 | 10 | 25 | 30 | 1,472 | 739 |
| seven-point type 2 | 7 | 9 | 24 | 29 | 3,782 | 3,050 |
| seven-point type 3 | 7 | 11 | 27 | 32 | 1,703 | 1,112 |
| eight-point type 0 | 8 | 12 | 31 | 37 | 140,463 | 101,910 |
| eight-point type 1 | 8 | 11 | 30 | 36 | 203,577 | 172,509 |
| eight-point type 2 | 8 | 12 | 32 | 38 | 285,731 | 248,487 |

If the secant-only lower bound is sharp, reintroducing the private line inputs preserves sharpness. In any full circuit set one private line input to zero. Since it was essential, there is a reader; substituting zero at that reader and simplifying removes at least one gate. The remaining private inputs are still essential and may be treated successively, so the full lower bound gains one gate per private neighbor. For the upper bound, insert each private input into its point-centered star by one extra OR. This applies also to identical private-neighborhood inputs before compression. The six-point status contradiction and Fano type-1 reduction therefore exclude all noncollinear PG(2,3) point modules on up to six points, and the seven-point type-0 contradiction excludes that type with its private inputs restored. Exclusion here refers to the combined mathematical and numerical argument.

In Singer labels p-l in {0,1,3,9} modulo 13, the full seven-point type-3 representative [0,1,2,3,4,6,7] has 28 positive flags and 89 maximal negatives, with a single private line 8 at point 4. Every line except 9 is incident to the selected points. The full eight-point type-2 representative adds point 8 and has 32 flags and 136 maximal negatives, with all its columns of degree at least two. Their one-below targets are 33 and 38 gates. A strict saving in either full module would extend by the omitted four-neighbor point stars to a 63-gate full plane circuit.
