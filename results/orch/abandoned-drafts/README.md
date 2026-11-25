# Abandoned cycle compiler draft

`proof_cycle_ext.lean` is an unfinished fragment, not an independently compilable Lean module. Its only attempted combined compilation failed; complete diagnostics are preserved in `proof-cycle-001.log` (exit1). The reserved identifier `prefix` caused parser failures, and other local errors remain.

The draft was abandoned when inventory found the already checked generic three/four-gate elimination theorem in `MetaComplexity/L107.lean`, with its dependence, nonconstant-input, and no-pair-funnel premises, and exact cycle complexity in `L106.lean`. It is not included in the checked named source or consolidated partials.

The redundant `lemmas/proof_cycle_work.lean` combined copy was removed after verifying it ended byte-for-byte with this fragment; its remaining prefix was the separately preserved, checked `lemmas/inventory_forest.lean`.

These files are research provenance only. They are not a successful proof, counterexample, or validation artifact for the posted gap.
