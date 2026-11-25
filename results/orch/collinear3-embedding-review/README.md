# Three-collinear-points local separator to global circuit

Independent review on 2026-11-25: PASS for the source, data and 11-OR baseline embedding. No Lean or SAT process was run for this audit. There is no 10-OR local witness in this package.

The local input map is [0,1,3,13,14,15,16,17,18,20,23,24,25]. It contains three collinear points and their ten incident lines, giving 12 local incidence edges. The projected generic negatives have 81 inclusion-maximal members. Rejection of those maxima implies rejection of every projected generic row by monotonicity.

Local input references map through the displayed list; each local OR reference n+g maps to global signal 26+g. Append one binary OR with an explicit edge monomial for each of the 40 remaining incidence edges. A 10-OR local witness would therefore give 50 global ORs. The direct-DNF control uses 11 local ORs and 51 global ORs.

The independent audit reconstructs the exact 468 generic rows from all point subsets, checks all 8192 local assignments, verifies the complete reference translation and 40 joins, and replays all 547 global samples. Its symbolic-DNF calculation confirms that the control's minimal terms are exactly the 52 incidence edges. The exported 520-sample masks match the already checked compiler sample order and every input bit.

Run `collinear3-embedding-audit.py` with arguments `collinear3-full-truth.json collinear3-direct11-control.json collinear3-direct11-global51-control.json fixed-compiler-samples.json <output-directory>`. The script accepts explicit paths and is portable. Original helper source is copied for provenance. All results here are Python/algebra checks; no Lean certificate has been claimed.
