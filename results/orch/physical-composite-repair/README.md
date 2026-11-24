# Physical composite-neighborhood repair

Both reviewed sources retain the fixed-size strict-backward binary representation, singleton-rejecting/dirty-count heuristic admission, and full88-case scalar witness verification from PhysicalRepairPairs. Resynthesize exhaustively replaces one gate by either operation with every unordered backward input pair, then recomputes the suffix. Jump adds16sampled whole-gate replacements per gate and32sampled two-gate edits to the existing single-wire/neutral neighborhoods. These expand a heuristic neighborhood only; neither is a complete synthesis proof procedure.

Author calibration checked4352resynthesis neighbors on69,632exhaustive scalar cases, including exact neighborhood cardinality, and2212jump neighbors on141,568cases. Independent review checked2150resynthesis neighbors/34,400scalar cases and1098jump neighbors/17,568cases. The first independent harness lacked INPUT_MASKS for Jump; corrected002 passed without a source change. Both complete review logs are preserved.

Completed run010 repeated the earlier Pair source, and run011 used Resynthesize with width16,40rounds,120seconds, seed14772956 and the included singleton-free positive-complete28gate seed with43raw errors (54augmented errors). Run011 inspected6,453,248neighbors in120.012462seconds without improving the seed. The complete run010/011 logs are included; both are bounded heuristic outcomes with no UNSAT or target-witness claim. The included seed remains explicitly INVALID.

A subsequent run012 on a different nested-dirty seed and any future Jump trial are separate runs, not results of this snapshot.
