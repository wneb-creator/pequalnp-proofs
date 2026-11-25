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
