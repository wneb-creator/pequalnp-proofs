SAT proof capability audit, Lean 4.36.0

The bundled CaDiCaL 2.1.2 executable accepts --lrat --no-binary and -t seconds. Complete help is cadical-help.txt. The tiny four-clause contradiction was solved with exit 20, producing lrat-probe-produced.lrat; its full stdout/stderr is cadical-probe.log.

Ordinary bv_decide and bv_check are unsuitable for the repository axiom policy. The local Lean source Lean/Elab/Tactic/BVDecide.lean explicitly documents an additional compiled-reflection axiom. The implementation Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean calls nativeEqTrue in LratCert.toReflectionProof. We did not use those tactics as target proof evidence.

Mathlib.Tactic.Sat.FromLRAT reconstructs ordinary proof terms. LratProbe.lean successfully checked both the documented example and the actual bundled-CaDiCaL certificate; lrat-probe-3.log reports only propext, Classical.choice, Quot.sound. The module is not provided by PEqualNP.Defs alone, but CONTRIBUTING permits Mathlib modules.

The from_lrat term form works inside an ordinary lemma. PlainLrat.lean defines the CNF and LRAT strings as lists of numeric character codes converted through String.ofList; it has no quoted strings, commands, new datatype, instance, custom elaborator, or custom syntax. The separate PlainLratAudit.lean repeats that source and audits the resulting theorem. plain-lrat-audit.log reports only the three permitted axioms. This is a working capability probe, not the target lower bound.

Mathlib FromLRAT rejects negative RAT proof hints as unimplemented. Its reconstruction relies on DAG sharing of proof expressions; a large certificate may require substantial memory. The repository also limits the source to512KiB. Numeric certificate encoding does not by itself solve that size limit; substantial trimming or compression may be necessary.

Std.Tactic.BVDecide.LRAT.check_sound is available after Mathlib and itself has only the permitted axioms. However the direct checker-reduction probes KernelLratAudit.lean FAILED: both decide and decide +kernel got stuck at an imported private checker helper. Their failure logs contain the automatically introduced failed-proof placeholder and are not accepted proof evidence. No direct kernel-reduction route was validated.

Any finite circuit-synthesis UNSAT certificate still needs a kernel-checked completeness bridge from every allowed small circuit to the selected CNF. In particular constants, unary gates, unavailable reads, padding, and final-output normalization must be justified. SAT solver output alone is not a theorem or checker acceptance.
