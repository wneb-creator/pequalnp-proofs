# L-meta-2732 formalization findings

- The assigned statement is exactly the first hypothesis of `R_meta_582_773.lean`.
- `Circuit.eval` is a forward fold of gate evaluations; missing wire indices evaluate to false. `Monotone2` requires AND/OR operations and at most two inputs. No encoding loophole found.
- Three reductions for the assigned step already exist: `R_meta_2732_3`, `_427`, `_773`, matching the desk count of three live reductions.
- `L_meta_3537.lean` proves canonicality of all 65 first-two-gate representatives by describing every graph automorphism through 336 possibilities. It imports only `PEqualNP.Defs`.
- `L_meta_3539.lean` proves that the packed 58-row AND/OR evaluator correctly computes the Heawood target whenever it returns 2097151. Its proof can be copied into the permitted file if a circuit is found.
- The search agent has the packed rows and canonical prefix table from `R_meta_2732_3.lean`.
- The definitions root has 86 project modules and 67 direct Mathlib roots; exact roots are recorded in `/tmp/oec/pequalnp-pilot-70/formalization/defs-imports.json`.

Prepared but not yet compiled, waiting for root's definitions build:

- `Baseline.lean`: canonical 27-gate circuit supplied by the search agent, with symbolic correctness proof.
- `PrefixMin.lean`: choose a raw prefix witness of minimum numerical score, then derive canonicality from transport under automorphisms.
- `Transport.fragment`: transport raw prefix witnesses using input renaming and sorted fan-ins.
- Child agent `/root/formalization/rename_wires` prepared `rename/Rename.lean`: generic input renaming, suffix preservation, circuit size and monotonicity preservation.

All scratch Lean sources are under `/tmp/oec/pequalnp-pilot-70/formalization/`. No builds or final-file edits have been performed by this strategy yet.
