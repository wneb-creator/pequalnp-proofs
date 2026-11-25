# Comparable NOT gate elimination

2026-11-25T14:33:15.615166+00:00

ComparableNot.lean has been checked in Lean. For a bracket f(x)=G(x,NOT h(x)) monotone in its extra input, h≤f allows constant true replacement, and f≤h allows constant false replacement. No monotonicity of f or h is needed for this semantic statement.

ComparableDelete.lean is now a checked circuit-level strengthening (Lean exit 0). It copies the checked Sum Bool Nat constant-propagation engine from L_meta_4725 (via the BinaryFloor extraction), then adds a strict size bound when any empty-input gate is present. For nonconstant outputs the normalized output is an existing wire, so no replacement constant gate is needed. The final lemma produces a monotone circuit with at least one fewer gate from an AND/OR prefix, one comparable NOT, and an AND/OR suffix.

Caution: even after this lemma is checked, it does not alone refute a 19-gate Petersen circuit with a comparable NOT: it yields a monotone circuit with at most 18 gates, whose exclusion still requires a separate lower bound. A search may discard such NOT sources only if it separately searches the cheaper monotone case or is explicitly restricted to globally minimal circuits.

Checked at 2026-11-25T14:34:59.978900+00:00. Complete compiler logs: comparable-delete-lean.stdout (inherited linter warnings only) and comparable-delete-lean.stderr (empty), in the job scratch directory.

A second extension, ConstantDropTwo.lean, is under compilation: if a later gate reads the sole NOT output, its constant replacement also deletes that reader, giving at least two gates saved. This is not yet marked checked.

Paused on root lease HTTP 410 at 2026-11-25T14:39:24Z. ComparableDelete.lean is fully checked (exit 0); ConstantDropTwo.lean is NOT yet checked: its first build failed only at one projection normalization in omega, fixed in current source, but recompile was waiting for renewal and was never started. All complete compiler logs remain in scratch.
