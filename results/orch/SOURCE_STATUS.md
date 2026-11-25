# Source status at lease loss

The named L_meta_2592.lean contains the checked partial binaryFloor17. It does not declare the full posted theorem.

Checked standalone helpers: ReplaceLast, SensitivityMask, SensitivityExtension, EffectiveReads, AntiDiagonal, SecondGate, PrefixReplay.
Checked historical extensions: BinaryFloor17Extension against the floor16 target, BinaryFloor18NonOrExtension against the floor17 target. Use the commits in CHECKPOINTS.md; names in historical extensions may duplicate later integrated target declarations.
Checked as the named file: BinaryFloor16.lean and BinaryFloor17.lean source copies.

UNCHECKED drafts or adaptations, preserved without a compilation claim:
- BinaryFloor.lean (15-gate adaptation)
- BinaryFloor18NonOr.lean (combined standalone integration)
- BinaryFloor18Compact.lean (proposed certificate cleanup)
- SharedOrThird.lean (new shared-OR argument)
- CutLast.lean (adaptation of an already checked upstream lemma)

BinaryFloor18NonOrFragment.lean is the body of the checked extension, intended for future integration. Computational search archives are evidence and reproducible code, not Lean certificates.
