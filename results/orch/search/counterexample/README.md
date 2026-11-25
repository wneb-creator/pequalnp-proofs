# Counterexample search archive

All active searches were stopped on root instruction because fresh lease ownership was uncertain. The five remaining processes exited 130. These interrupted searches give no nonexistence result, and no target counterexample was found.

## Checked and computational results

- L-meta-2592: root Lean-checked and pushed a 20-gate monotone Petersen witness in `results/orch/lemmas/Counterexample.lean`. This is an upper bound, not a refutation of the 19-gate statement.
- The 19-gate Petersen SAT searches (exactly one, two, three, four, or any positive number of NOT gates) remained unresolved. Heuristic approximate circuits are not proofs.
- The Fano 26-gate searches were stopped when existing checked theorem `L_meta_7997_aux.ao27` was confirmed to rule out exactly that cyclic incidence case. No inference from the interrupted search was needed.
- For PG(2,3), the generated incidence data has 52 edges and 704 maximal false assignments. Independent Python checks exhausted all 8192 point subsets and confirmed that every false completion extends to one listed maximal false assignment. Thus 756 rows suffice for monotone correctness. This computational certificate is not itself a Lean proof.
- The 64-gate sanity search immediately found the standard correct circuit; independent evaluation passed all 756 rows.
- No 63-gate PG(2,3) witness was found. Plain annealing reached one wrong prime-edge row. Reread-biased candidates with two wrong rows contained removable repeated-filter identities; they do not improve the canonical circuit.
- Near-seed SAT used fixed skeletons: remove one OR from a 64-gate circuit, then allow 13 gates around three final point stars and two final output gates to change. The noncollinear and collinear cases started with 112 rows. Both were interrupted without a SAT or UNSAT verdict.
- A further SAT variant required every gate to be used, at least 13 AND gates, and a live AND true on a symbolic false input with operands separable in both directions. It was also interrupted without a verdict. These are restricted search classes, not exhaustive circuit censuses.
- Five-line and six-line block heuristic searches also stopped without an exact witness.

## Reproduction and preservation

Full stdout and stderr are included. The manifest records every preserved source/data/log file and hashes of generated CNF inputs. Large CNF inputs remain in scratch and were not duplicated into this archive; their source programs and deterministic seeds reproduce them.

`plane3_near_sat_initial.py` reproduces case 25831 without the later AND-count bound. `plane3_near_sat.py` reproduces case 25832 with that bound. `plane3_junk_sat.py` is the stronger variant, case 25833. No SAT verdict should be inferred from a Python wrapper exit status: inspect the solver output and the explicit full-certificate validation.
