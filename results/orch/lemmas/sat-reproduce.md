# Reproducing the reviewed Fano SAT model

These artifacts preserve a computational search, not a Lean proof or an UNSAT certificate. The final target has 9,801 variables and 205,448 clauses. The reviewed 28-gate control satisfies all 218,726 clauses of its corresponding model and passes exhaustive Boolean and derivative checks.

The JSON manifest lists each selected file, byte size, SHA256 digest, role, and exact reproduction arguments. Copy the listed Python sources, JSON control, and review scripts to one artifact directory. Decompress every listed `.gz` file into that directory using its basename without `.gz`. All compression is lossless. The verifier starts no solver and makes no network requests.

Run `python3 status-final-fano-sat-review.py ARTIFACT_DIRECTORY` to reproduce the complete final control assignment and the exact 28-clause extension check. Run `python3 status-full-fano-sat-review.py ARTIFACT_DIRECTORY` to reproduce the original CNF primitive, boundary, full truth-table, derivative, symmetry, and baseline control audit. The baseline script rewrites its text report in the artifact directory.

The three encoders use only Python standard-library modules. Running a solver additionally requires CaDiCaL, expected at `/tmp/oec/pequalnp-pilot-81/lean-4.36.0-linux/bin/cadical`. Their generated artifacts use the fixed scratch root `/tmp/oec/pequalnp-pilot-81`. The `--no-solve` commands in the manifest regenerate the immutable target/control files without invoking CaDiCaL.

The stopped baseline returned UNKNOWN after 590.05 seconds on 2026-11-25. Its complete stdout and stderr are preserved. The final minimality variant started at approximately 10:44:41 UTC with a 6,555-second wall-clock limit. Only its immutable CNF and metadata are included in this checkpoint; mutable live output is deliberately excluded.
