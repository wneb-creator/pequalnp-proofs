# Lower-bound agent preservation status for L-meta-2590

Development stopped immediately on the root renewal-error instruction. No own build remains active. No proof edits, fixes, or new builds were made after the stop.

- `lower_mono9_slim_core.lean`: SHA256 `32d78ab7ac6bec0ff6114d85d98e81e39fecb035f68795da60d27487999dd2df`. CHECKED exit 0; local prerequisite definitions/lemmas only, no monoRoot certificate.
- `lower_mono18_conditional.lean`: SHA256 `841862376ce2e6c617d8d19bdd40f69b44c72c0d7e74db3994a95c082501bad3`. CHECKED exit 0; 18-gate lower bound conditional on explicit monoRoot proposition parameter.
- `lower_mono19_conditional.lean`: SHA256 `3c4c82ae05d67611d0032fe925a61e57c619188dde7c659f2477b2120e4a0267`. CHECKED exit 0; includes conditional18, first-AND suffix18 (total19), and canonical overlapping-two-AND suffix18 (total20 with two paid prefix gates).
- `lower_overlap_conditional.lean`: SHA256 `cfcf01f1acd35d2896e5b899d08654e7e16125335dc11574252be488d7ce9702`. FAILED exit 1; one type mismatch in arbitrary-variable overlapping-AND transport. Prior checked prefix unchanged; do not treat final transport as established.
- `lower_mono18_base.lean`: SHA256 `6d00c850e432acb0156c27e9bbf7b39fef80942e73eb4928a7d4b7287445c903`. NOT COMPILED; imports missing ExistingMonoNine.olean and uses undischarged locally-unverified full certificate.
- `lower_mono18_integration.lean`: SHA256 `476c9a96b0b8c95413701726d8645b835b805b1272dcf3353ee88d2d7a5c445f`. NOT COMPILED; intended unconditional18 integration importing missing ExistingMonoNine.olean.

The explicit proposition parameter in every checked bound is
`PEqualNP.Outside.L_meta_2590_aux.MonoNine.Impossible false graph 15 inputs.toFinset`.
It asserts the nine-input Petersen-deleted-vertex function has no monotone Live derivation of at most fifteen binary gates from its nine inputs. There are no new axioms or placeholder declarations in the checked files; this premise is a theorem argument. The imported `ExistingMonoNineSlim` module can be reconstructed from the checked `lower_mono9_slim_core.lean` source by compiling it under that module name. Its local `.olean` existed successfully.

The full renamed nine-input certificate build was terminated by the existing-results agent with exit 130 after the stop; `ExistingMonoNine.olean` was never produced. Hence the unconditional eighteen-gate result was not locally established by this work.

The canonical overlapping-two-AND lemma applies when the first gate is AND of pin0 with pin1 or pin2, and the second output is AND of either that first output or pin0 with another input. The second output is assumed live; pin0 is proved live. These become distinct constant-zero roots under pin0=0. The conditional nine-input floor then charges eighteen suffix gates. The arbitrary-variable transport has one unresolved Lean type mismatch. The first-two-gate extraction fragment was drafted but never compiled; it is preserved under research/ for later work.

Complete stdout/stderr from all attempted builds are preserved under logs/. These checked partials do not prove the posted L-meta-2590 statement, which needs exclusion of every monotone circuit with at most nineteen gates.
