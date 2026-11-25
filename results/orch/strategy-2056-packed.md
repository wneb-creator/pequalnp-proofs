# L-meta-2056 packed verification

The leased statement asks for a63-gate monotone circuit for the order3 plane, using sum incidence(p+l)%13 in{0,1,3,9}. Its negative tests use subsets of size at most3 on both sides. These tests already force full correctness; existing checked L_meta_2054 supplies the completeness direction. No weaker-test shortcut is available.

## Checked infrastructure

- PackedCircuit2056.lean: generic BitVec circuit evaluator, bit-projection soundness, logarithmic doubling point patterns, line-complement patterns, and transfer from one8192-bit zero check to every point-subset closure. Compiled exit0, independently approved, frozen hashbc74c73e812cbbdbceb78d757aa647608a61493ed870513fa7c11257e90c3909.
- PackedControl2056.lean: explicit64-gate star circuit in the exact sum convention, kernel-checked8192-row negative closure certificate and52-row positive edge certificate, plus row coverage and semantic transfer. Compiled exit0, independently approved, frozen hash1bdf1123a4cc949f9c23ea71e90f7e9a2b7b11373955486f66ef386cf31f1071,365lines. All checks use decide+kernel; no native_decide, external SAT trust, or large decimal literals.

The control is64 gates, so it does NOT prove the63-gate target. Its complete successful diagnostics are packed-control2056-build-3.stdout/.stderr under scratch/gate-elimination/2583/. They contain only five deprecation warnings and no errors. Previous complete logs are preserved too; the initial drafts had a missing GateOp equality-decider and an elaboration heartbeat issue, both fixed before the successful build.

## Exact statement verifier

PackedWitness2056.lean compiled successfully at hashb6bed66e77a0a3d9daaead16de704f0860e27a7a97cc86dae949eb259ed593a7. It requires a concrete circuit, Monotone2, size<=63, a52-bit positive certificate and two8192-bit negative certificates (original and swapped input halves). The final theorem exact_statement_of_checks concludes the literal leased statement. The Finset/Fin.ofNat input convention is transferred directly to Fin.append. The file contains no candidate circuit and proves only the conditional verification theorem. Complete successful logs are packed-witness2056-build-3.stdout/.stderr in the same scratch directory.

PackedEndToEnd2056.lean instantiates that entire pipeline on the known64-gate control, including the swapped negative check and exact Finset PostedTests. It compiled exit0 and was independently approved at hasha9684a60606e69d5801ed0aa5ece6adea37cee4272a9410003667be1cc268e2d,475lines. The measured build took25.672seconds and peaked at7,056,024KiB RSS (about6.73GiB). Complete output and metrics are packed-endtoend2056-build-1.stdout/.stderr and packed-endtoend2056-metrics.json. The memory peak is substantial; future candidate compilation should run with sufficient headroom. Verifier development is frozen after this successful control test.

## SAT symmetry assistance

The verified216-element stabilizer of unordered incident edge{0,13} partitions325 unordered input pairs into14 orbits in the sum convention. Representatives for a first OR gate are:

(0,1),(0,2),(0,13),(0,14),(0,15),(1,2),(1,3),(1,14),(1,15),(1,17),(2,4),(2,8),(2,15),(2,20).

The four incident representatives for a first AND gate are(0,13),(0,14),(1,15),(2,20). They are compatible with marking a joint-read obstruction at edge(0,13), unlike unrestricted full-group normalization. Data q3-plus-first-pair-orbits.json was independently audited at hasha80e2765ca3699bf1d38de2c4debfb5b487fb7e0e8e32cbd8a863b393acf70a8.

All1716 six-point subsets split into four projective-group orbits, represented by masks63,95,183,207, with orbit sizes234,936,468,78 and stabilizer sizes24,6,12,72. The current SAT target is mask207={0,1,2,3,6,7}; it has two unused line inputs, nine line vertices of degree2 and two of degree3. Data q3-sixpoint-orbits.json was independently audited at hash9f81343fd37f28d4e01c7d9528c246ba4b37f5a6d3872d6c9e2964234477b07d.

### Memory optimization: direct 512-bit closure chunks

Frozen `lemmas/PackedChunks2056.lean` (728 lines; SHA256 `19c0e60b53f255ed800c96b51539473d84a44c65da699e1838c61542a85fd38d`) compiled successfully on the identical 64-gate control. It imports only `PEqualNP.Defs`, constructs sixteen 512-bit chunks directly (low nine point bits vary, upper four fixed), and proves all 13-bit subsets are covered using independent Fin 9 / Fin 4 representations. Thirty-two separate kernel certificates check both closure orientations, followed by the original 52-positive check and exact posted Finset transfer. No 8192-bit bitvector is constructed in this module.

With the checker queue default `LEAN_NUM_THREADS=3`, the complete module took 37.998 seconds and peak RSS 3,187,024 KiB (3.04 GiB), comfortably below the stated 6.5 GiB budget. Full logs are `gate-elimination/2583/packed-chunks2056-build-3.stdout` and `.stderr`; metrics are `packed-chunks2056-metrics-3.json` under the task scratch directory. Exit code 0; warnings only. The original compiled 8192-bit modules remain unchanged. This certifies infrastructure on a 64-gate control, not a 63-gate witness.

Two earlier measurements are retained: quantifying all sixteen chunks in one kernel decision was terminated at 31.844 seconds / 8,366,640 KiB; splitting the certificates but retaining full Mathlib and default concurrency gave 42.060 seconds / 7,155,300 KiB and one generic allOnes get-bit proof error. The final module fixes that proof explicitly and narrows imports/concurrency to the repository queue configuration.

2026-11-25 research note: Read [discussion12644](https://github.com/open-goat/pequalnp-proofs/discussions/12644). Its external run counts are author-reported and were not reproduced here. It supplies no nonexistence proof. Our independently audited full-plane encoding has about8.8million clauses and executes; the post's size assessment does not establish a limitation of our implementation. Structured SAT continues, with complete controls and exact scope recorded in the plane-cegis archives.

2026-11-25 18:36 UTC: Prepared a separate existential non-read1-edge layer for the full-plane SAT query. The compiled sum-oriented `SumPlaneReadOne2056.sum_read_one_lower` gives the necessary64-gate threshold for joint READ1, avoiding the earlier difference-incidence orientation issue. The new layer chooses one of52 incident edges and tracks the10/01/11 capped proof-count states through each binary gate; it requires no11 state at the output. This existential choice preserves the existing full-plane symmetry normalization. Independent reference enumeration compared14,144 wire/edge cases against the actual capped count-set recurrence.

The source and actual artifacts are independently approved and frozen in `plane-cegis/warm-nonread`: a correct nonlinear67-gate control with three syntactically free suffix gates is SAT and passes all756 rows, while the fixed read-one64 control is rejected. The63 target is only prepared, not solved; it has8,858,897 clauses and164,294 variables. Its existing nonlinear phase hint still misses the same three positives. The current separate first-gate full63 query started native search at18:09:32 UTC and continues toward its original one-hour cap. A publication recovery paused the same processes for65.213seconds at18:23:50–18:24:55; they resumed without restart or source changes.
