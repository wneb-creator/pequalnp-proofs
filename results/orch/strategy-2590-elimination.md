# L-meta-2590 structural elimination checkpoint

The exact target is the unrestricted monotone Petersen lower bound20 gates.

The old2592 terminal ledger cannot directly reach20. Its four singly-occurring terminal variables were obtained only under at most15 non-NOT gates. A19-gate circuit on10 inputs can have two readers at every input, so the four-terminal premise is unavailable. Monotonicity does not remove all signed masks from that ledger because it takes Boolean differences relative to a nonzero baseline.

A separate structural route uses the checked generic monotone formula rank argument from L_meta_3793 (itself adapting L_meta_252). Petersen has15 edges and minimum vertex cover6, so every positive formula needs at least21 leaves. Therefore a circuit with no internal fanout needs at least20 gates.

For any live binary circuit with at most19 gates, if all10 inputs have at leasttwo readers, the20 input uses leave at most one use per internal gate. Liveness then forces no internal fanout. Combined with the formula lower bound, any hypothetical19-gate counterexample must contain a singly-read input. This reduces the previous0..3-single-terminal obstruction but does not prove the full target.

## Frozen draft files

- PetersenFormula2590.lean: hashb0431d957c39d68eb53a346c4877006e35a26d0a6db9d95bf28efb87775a66e4. Generic prefix is copied from L3793 lines15–37 and267–1040 with namespace replacement. New graph geometry and cover-size checks elaborated in the first build. The first build stopped at the final formula bound with the default200000-heartbeat limit. A second build with scoped4000000 limits was suspended and then terminated at the parent's desk-error stop instruction; exit137. The complete file is UNCOMPILED/INTERRUPTED, not a checked result.
- PetersenReaders2590.lean: hashfb994b39b1ca9a9b418dce811dafb688872d160192f04ce7e7a23c60e461b390. Contains the input-reader budget argument. First build exited1 at two small proof issues: Fin.val coercion needs normalization before omega, and Bool.not_decide is not a known lemma. The complete file is UNCOMPILED.

The formula draft was independently reviewed before the two heartbeat-limit additions. It declares an auxiliary private RawFormula datatype inherited from the checked source; any eventual final PR must disclose that datatype as required by the repository workflow.

Complete diagnostics are under scratch/gate-elimination/2583/ with names petersen-formula-build-1.stdout/.stderr, petersen-formula-build-2.stdout/.stderr, and petersen-readers-build-1.stdout/.stderr. No processes remain active.
