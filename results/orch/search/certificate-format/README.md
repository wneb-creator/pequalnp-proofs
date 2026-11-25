Certificate format study for the completed signed-17 OR-edge computation

This directory measures storage alternatives. It contains no Lean decoder or
complete Lean certificate. Both full source traces are preserved in the sibling
signed17-or-edge directory, including their audited resume dependency.

The root-reachable DAG has 649 expanded states and 2,831 formula leaves.
The compact bit-cost estimate is 58,380 bytes of binary skeleton, or about
116,760 hexadecimal characters before Lean syntax. This estimate excludes
formula certificates, helper code, truth-function derivation programs, seed
histories, and decoder proofs. Exact memo permutation values were budgeted but
not emitted. The XOR/gap shortlist stream is emitted and round-trip checked. Other streams are emitted for measurement.
The estimate therefore does not establish a complete certificate below 100 KB.

Reproduction scripts currently use the original scratch directory constant.
Restore/decompress the two archived traces and the DAG there, or update BASE
consistently before rerunning trim_proof_dag.py, measure_certificate.py, and
measure_compact_skeleton.py in that order. The complete stdout reports and
structured metrics are preserved alongside their exact sources.
