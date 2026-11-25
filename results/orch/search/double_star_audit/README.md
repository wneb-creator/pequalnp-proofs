# Eight-input double-star synthesis audit

The graph has edges (0,4), (0,5), (0,6), (0,7), (1,4), (2,4), (3,4). The search asks for exactly nine binary AND/OR gates, distinct earlier operands, the last gate as output, and both formal derivatives on the central edge (0,4) false.

All ten possible AND counts were excluded by CaDiCaL. Counts 0,1,2,6,7,8,9 have direct UNSAT runs. Counts 3,4,5 each have ten UNSAT cases: five first-gate operand-pair orbits times two operations. The orbit driver enumerates and tests all 72 leaf-permutation/side-swap automorphisms and their coverage of all 28 operand pairs. The ten-row boundary basis is independently tested against all 256 inputs. Essential-input occurrence clauses are logically necessary for this function. These coverage runs do not restrict connectedness or gate order.

This is computational evidence only. Neither the SAT encoding nor the UNSAT certificates have been proved in Lean, and no lower-bound bridge from the full projective-plane circuit is established. The separate connected and ordered runs are extra experiments and are not needed for the coverage claim. Timeouts have no mathematical verdict. A fixed ten-gate witness was scalar-verified on all 256 inputs and both derivative traces.

Pinned source versions, exact run summaries, full gzip solver outputs, and CNF hashes are preserved. Large CNFs are omitted but remain reproducible from the encoders. The manifest identifies one overwritten, unused timeout output; every UNSAT run used for coverage has its complete output. The original unpartitioned full-assignment attempt is encoder v1, the original ten-row attempt v2, initial count partitions and the ten-gate control v3, relevant-input/orbit runs v4, and connected gate-order experiments v5.
