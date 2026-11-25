# L-meta-2732 formalization findings

- The assigned statement is exactly the first hypothesis of `R_meta_582_773.lean`.
- `Circuit.eval` is a forward fold of gate evaluations; missing wire indices evaluate to false. `Monotone2` requires AND/OR operations and at most two inputs. No encoding loophole found.
- Three reductions for the assigned step already exist: `R_meta_2732_3`, `_427`, `_773`, matching the desk count of three live reductions.
- `L_meta_3537.lean` proves canonicality of all 65 first-two-gate representatives by describing every graph automorphism through 336 possibilities. It imports only `PEqualNP.Defs`.
- `L_meta_3539.lean` proves that the packed 58-row AND/OR evaluator correctly computes the Heawood target whenever it returns 2097151. Its proof can be copied into the permitted file if a circuit is found.
- The search agent has the packed rows and canonical prefix table from `R_meta_2732_3.lean`.
- The definitions root has 86 project modules and 67 direct Mathlib roots; exact roots are recorded in `/tmp/oec/pequalnp-pilot-70/formalization/defs-imports.json`.

Checked results:

- `PrefixNormalize.lean` compiled with exit 0 on its first attempt. It combines generic circuit renaming, minimum-score selection, and transport under automorphisms. Applying `canonical_prefix F raw (transport_prefix F)` gives the exact ordered, symmetry-minimal prefix shape required by the assigned statement from any raw prefix witness.
- `rename/Rename.lean` compiled with exit 0. Root has integrated and independently reviewed these helpers.
- `Baseline.lean` compiled with exit 0. It proves monotonicity, exact size 27, and exact Heawood edge-function semantics for the search agent's canonical star circuit. Full log: `baseline-check-4.log`. The broad propositional simplification takes roughly 87 seconds.
- `rename/BaselineExplicit.lean` also compiled with exit 0 and no warnings. It uses explicit disjunction cases and takes about 20 seconds of simplification, but is longer. Root may keep the original baseline. The optional Tauto/AC attempts were stopped or failed; they are not deliverables.
- `rename/PackedDecoder.lean` compiled with exit 0 and no diagnostics. Its 184 lines copy and adapt the checked decoder from `L_meta_3539`, importing only `PEqualNP.Defs`. `Packed.decode` turns the 58-row packed equality into correctness on every 14-input assignment.
- `PackedWitness.fragment` was checked in `AssemblyTest.lean` against the saved decoder olean, with exit 0 and no warnings (`assembly-check-2.log`). `PackedWitness.raw` takes two first gates, at most 24 tail codes, and one packed equality, and produces `prefixWitness`.

The complete future witness route is now checked component by component:

1. Prove the finite packed equality for a candidate program by kernel computation.
2. Apply `PackedWitness.raw` to construct the raw prefix witness.
3. Apply `canonical_prefix F raw (transport_prefix F)` to obtain the required symmetry condition.

The only missing substantive input is a circuit with at most 26 gates. The original 27-gate baseline is not a proof of the posted bound.

Prepared components:

- `BaselineTauto.lean` and `BaselineAC.lean` are abandoned experiments, not checked deliverables.
- `PrefixMin.lean`: choose a raw prefix witness of minimum numerical score, then derive canonicality from transport under automorphisms.
- `Transport.fragment`: transport raw prefix witnesses using input renaming and sorted fan-ins.
- Child agent `/root/formalization/rename_wires` prepared `rename/Rename.lean`: generic input renaming, suffix preservation, circuit size and monotonicity preservation.

All scratch Lean sources and complete build logs are under `/tmp/oec/pequalnp-pilot-70/formalization/`. No final-file edits have been performed by this strategy. Root owns integration and publication.
