# Capacity-two singleton-block packing control

This is a finite research control for L-meta-1896, not a Lean proof or a checker verdict.

The 351 blocks are the 26 singleton coordinates and 325 unordered pairs. Selected blocks must be vertex-disjoint, and each of the 468 generic false rows may meet at most two selected blocks. The objective is the number of the 52 incidence edges touching selected vertices.

The exact maximum is **21**, leaving **31** incidence edges untouched. A maximizing family is `{0,14}`, `{1,15}`, `{3,25}` in the original 26-input coordinate numbering. Its generic-row activity histogram is 72 rows meeting zero blocks, 180 meeting one, and 216 meeting two.

Two C++ runs agreed:

- Branch-and-bound: 177,263 visited nodes, 166,651 valid edge-union upper-bound prunes, about 0.047 seconds.
- Unpruned enumeration: all 189,723 feasible families, no objective pruning, about 0.047 seconds. There are 936 maximizing families, all with three pairs using three point and three line coordinates. Maximum family size is five blocks; exactly 26 families have that size.

Unpruned family counts by number of blocks are `1,351,52975,112814,23556,26`. The last family size consists of an incidence star's five singleton coordinates. The observed optimal-family count agrees with the theta-three construction: 117 nonincident point-line choices, four ways to choose three of the line's points, and two cyclic cross-pairings, giving 936. The independent Python verifier generated all936theta families, checked every row and edge count, and likewise checked all26singleton stars. Together with the exhaustive counts, this identifies the maximizing and maximum-block families computationally; it is not a Lean proof.

The DFS maintains the 468-bit masks of rows touched at least once and rows touched twice. A new block is allowed exactly when it uses no selected vertex and touches no row already touched twice. Blocks are added in increasing index order. The branch-and-bound version additionally uses the union of all remaining edge masks as an upper bound. The unpruned run does not use that objective bound.

Reproduce from this directory:

```sh
g++ -O3 -std=c++20 singleton_packing_unpruned.cpp -o /tmp/oec/pequalnp-pilot-62/packing-recheck
/tmp/oec/pequalnp-pilot-62/packing-recheck singleton-packing-input.txt 60
python3 verify.py
```

The input file begins with the row and edge counts, then the 468 row masks and 52 edge masks. `verify.py` independently checks the maximizing family against every row and edge. Complete source, input, output, incumbent verification, the earlier MILP control, and hashes are archived here.

## Smaller row controls for Lean

The full468-row control also proves at most6selected coordinates. The original25Lean-checked rows alone are insufficient: they permit9coordinates and32removed edges. Two smaller augmentations are archived:

- `packing-augmented-rows.json`: the original25plus22rows,47total. Exact maximum7coordinates and25removed edges. The unpruned enumeration has421952states. `packing-47-lean-data.json` and the `.lean.txt` fragments export all351triples `(coordinateMask,activeRowMask,blockSize)` and the47row masks. Active masks fit47bits. `packing-47-root-chunks.json` splits the enumeration by firstblock; the largestchunk has17980states.
- `packing-edge-augmented-rows.json`: the original25plus only `(S,D)=(170,5376),(402,1540)`,27total. Exact maximum30removed edges, leaving22flags, but still allows9coordinates. Unpruned enumeration has1164428states.

The47-row augmentation was chosen by covering all13903minimal prefixes reaching at least8coordinates under the25-row control, then independently re-enumerated. The27-row augmentation covers the15prefixes removing at least31edges. Both controls completed far below the60second cap. The Lean agent is using the47-row count-based version; no further optimization was started.


## Capacity-three objective control

For the same 351 blocks and 468 rows, change the row capacity to three and maximize **removed incidence flags minus number of selected blocks**. The exact maximum is **28**. The unpruned DFS completed in 9.8096 seconds, visiting all **56,424,915** feasible families. No objective bound or symmetry pruning was used. The depth counts for zero through eight blocks are `1,351,52975,4532450,28911402,20269808,2608320,49140,468`. Maximum selected coordinates is ten, and maximum selected blocks is eight.

There are exactly **2,106** maximizing families: four pairs on eight coordinates, all coordinates on the same side of the incidence graph. There are 1,053 on each side. The point-side example is `{0,1}`, `{2,5}`, `{4,6}`, `{7,8}`. It removes 32 flags using four blocks, giving objective 28. Its row-activity histogram for zero through three touched blocks is `12,102,264,90`.

The independent Python verifier checks this witness directly against every row and edge. It also independently enumerates all 135,135 four-pair families on each 13-coordinate side and confirms exactly 1,053 feasible families per side. Each side has 585 distinct eight-coordinate supports: 468 supports admit two valid partitions and 117 admit one. This second enumeration verifies the maximizing-family structure; the global upper bound comes from the C++ exhaustive DFS and has **not been proved in Lean**.

The DFS extends the capacity-two state by maintaining rows touched at least three times. The update is `third := third | (second & active)`, `second := second | (first & active)`, `first := first | active`, all using the previous masks. A new block is legal exactly when it is vertex-disjoint and its active-row mask misses the current third mask. Canonical increasing block indices enumerate each feasible family exactly once. Source and complete diagnostics are `singleton_packing_capacity3.cpp`, `packing-capacity3-compile.log`, and `packing-capacity3-exact.log`; independent checks are `verify_capacity3.py` and `packing-capacity3-verification.{json,log}`.


## Compact capacity-three decision certificate

To prove only objective at most29, a normalized decision search is much smaller. Four explicit permutations of the26coordinates preserve all52incidence-edge masks and468generic-row masks. They are stored as26-element arrays in `packing-capacity3-symmetries.json`; their preservation was checked directly, without assuming any projective-group classification. Their action has one singleton orbit, three pair orbits, and27orbits on the44,850unordered families of two disjoint pair blocks.

Every nonempty feasible family belongs to one of three cases: no pair blocks, exactly one pair block, or at least two pair blocks. Normalize a chosen singleton, the unique pair, or two chosen pairs respectively. This yields31fixed-root searches. Initial extension candidates include **every compatible block**, irrespective of its index relative to fixed roots. Additional blocks alone are chosen in increasing order. The no-pair and one-pair cases permit only singleton extensions. The two-pair case permits arbitrary compatible extensions.

The preferred evaluator is `packing_capacity3_simple_roots.cpp`. If `U` is the union of currently removed edges with every remaining candidate's edge mask, and `d` is the current block count, then `popcount(U) < 30+d` safely terminates the branch: every extension removes at most `popcount(U)` edges and uses at least `d` blocks. No degree or rounded-division argument is needed. Its complete31-root search has78,682visited states:71,834for the27two-pair roots,4,393for the three one-pair roots, and2,455for the singleton-only root. The largest individual tree has7,572states. All trees complete; no objective30 witness is found. This is a decision bound, so other reported optimum/depth counts from these pruned logs do not enumerate all feasible families.

Root files `packing-capacity3-two-pair-roots.txt`, `packing-capacity3-pairs-roots.txt`, and `packing-capacity3-singletons-roots.txt` start with a root count; each remaining line is the number of fixed blocks followed by their26-bit coordinate masks. Run the last two files with maximum-pairs arguments1and0 respectively. All block indices use26singletons followed by325pairs lexicographically.

The orbit-cover certificate `packing-capacity3-orbit-certificate.txt` has44,850records `(i,j,parent,generator)`, preceded by its record count. Pair indices0through324 correspond to full block indices26through350. Root records use parent/generator−1. Otherwise the parent is an earlier record; applying the specified generator to both parent blocks and sorting yields the current pair of blocks. Every legal disjoint pair-of-pair state occurs exactly once. The small pairs/singletons certificate files use `(coordinateMask,parent,generator)`. `verify_capacity3_orbits.py` independently checks all records, complete coverage, and generator preservation. This finite certificate is **not yet Lean checked**.

The older `packing_capacity3_roots.cpp` uses the valid but less convenient upper bound subtracting `ceil(additional_edges/8)`; its66,757states are not needed by the preferred Lean route. `packing_capacity3_target.cpp` is the global, unsymmetrized version. Their complete output remains preserved for audit.


### Compact orbit labels for Lean

`pack_capacity3_orbits.py` replaces each orbit record by a six-bit label: `(depth << 2) | generator`, with depth0through10. Applying the inverse generator to any nonroot state yields a state of exactly one smaller depth; all depth-zero states are exactly the27normalized roots. This was independently verified for all44,850legal states. Inverse26-coordinate permutation arrays are exported as Lean literals.

The legal-state table uses lexicographic `(i,j)` order restricted to disjoint pair masks. Ten six-bit labels are packed per60-bit word; `packing-capacity3-compact-labels.lean.txt` is86,337bytes. An optional triangular table covers all52,650pairs of distinct pair indices, using label63for the7,800overlapping cases. Its direct index is `i*(649-i)/2 + j-i-1` for `i<j`; `packing-capacity3-triangular-labels.lean.txt` is101,349bytes. Both packed formats were unpacked and checked. The triangular form trades15KBfor avoiding the legal-state rank function. All data, inverse maps, roots, and format metadata are in `packing-capacity3-compact-orbits.json`.
