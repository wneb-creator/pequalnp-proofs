# Source-only restricted39 development

Status: UNCOMPILED. No Lean build or solver was launched to produce this archive.

These drafts target a39-OR lower bound for a thirteen-line-input architecture whose internal supports are backward binary unions of singletons, empty sets, and earlier supports. The thirteen pencil outputs may be free intersections of those unions. This architecture explicitly excludes AND filtering inside OR operands. The drafts do not establish the posted51-OR bound for arbitrary26-input circuits and are not a counterexample.

The generic conditional counting dependency GuardCharging has already compiled; its checked source is ../checked/guard-charging.lean, SHA2566e2c31baa3ce2f08339feb65bfaa9e5f13da150da828e5bd7f669ca63b52d9be. GeometryRowsDefs provides the exact AllRows incidence definition.

Unresolved source dependency at freeze time: RestrictedUnionBound.guard_targets_card refers to GuardGeometry.fourCap_avoiding_card, which has not yet been declared in the archived GuardGeometry.lean. Its required statement is:

    lemma fourCap_avoiding_card (N : Finset (Fin 13))
        (hN : IsFourCap N) : (avoidingPoints N).card = 3

The geometry owner has been asked to add a bounded finite certificate. Independent Python checks confirm the mathematical statement for all234 four-caps; this is not a Lean certificate. The archived assembly is intentionally labelled incomplete until that declaration and all three modules compile.

PureUnionAncestry uses elementary counting, not an unsupported circuit normalization: a support ofsize at least3 has a prior support ofsize at least2. A support ofsize at least4 either has an operand ofsize at least3 (two ancestor levels) or two distinct operands ofsize2. Thus at least3 nontrivial union nodes lie inside it, including the producing gate. This ancestry argument is not claimed for arbitrary AND filtering.

The original live sources remain under ../lemmas/. This directory is an immutable source checkpoint; future changes should be archived separately.
