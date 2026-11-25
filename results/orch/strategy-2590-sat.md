# Petersen monotone SAT checkpoint: L-meta-2590

The exact 19-gate query was interrupted by the parent after a desk error, at 2026-11-25T15:22:07.819688+00:00. Its Python process exited 143 after SIGTERM. It returned no SAT or UNSAT verdict. Complete input, source, stdout, stderr and stop record are archived in `results/orch/sat2590/`.

The 20-gate positive control passed the same SMT encoding. Its supplied circuit was independently evaluated on all 1024 input assignments and had a joint read-one proof on each of the 15 minimal true assignments. The boundary contains the 15 edge assignments and the 15 maximal independent sets, sufficient for exact equality of monotone circuits.

The search uses AND/OR gates with two distinct earlier sources, boundary-value irredundancy, no unused gates, and a final output wire. The normalizations forbid clean operands to AND and mixed clean/dirty OR, enforce at most one reader of each clean gate, and replace singleton edge-profile gates by direct input ANDs. It also assumes a missing joint read-one proof on edge (0,1), using the known read-one lower bound 20 and Petersen edge transitivity. No bipartite-only or Fano-specific constraint is present.

Independent reviewer status: full-boundary duplicate elimination and all-negative-true constant propagation were approved mathematically. The current script's entire implementation and the joint normalization/adjacent lexicographic ordering were not completely reviewed before the stop, so no complete UNSAT certificate claim is made. The normalizations also need a Lean bridge to the posted arbitrary Circuit statement.

Scope caveat: this query fixes exactly 19 irredundant gates. Even an UNSAT result alone would not exclude smaller irredundant witnesses. A next encoding should permit a variable active prefix or run all remaining sizes after establishing a lower bound. No such replacement query was launched.

Data: `petersen2590-data.json`; positive control `petersen2590-259020.json`; interrupted query `petersen2590-259019.smt2`; process status `stop-2590.json`.

Archive portability: the archived generator uses its own directory for data/output and the adjacent unmodified `synth-2590.py` C-API helper. The original executed source remains in scratch. Only these path references differ; the complete generated SMT query is preserved exactly.
