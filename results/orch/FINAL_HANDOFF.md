# L-meta-2592 partial handoff

The full posted statement remains unproved. The strongest compiled result is17 binary gates, excluding at least3NOT gates at total size19. Only the one- and two-NOT cases remain.

Read validation.txt for exact validation scope and the desk collision that stopped this job. No PR was opened, no Outside source was added in the main worktree, and no other pilot lease was released.

- BinarySeventeen.lean and SeventeenCorollaries.lean contain the compiled improvement; only standard axioms.
- BinarySeventeenStandalone.lean is an inlined candidate with only Mathlib and PEqualNP.Defs imports. Its source guard passes, but it still needs a named build and local checker against the explicit binary17 PARTIAL statement.
- BinarySixteenStandalone.lean is the earlier officially accepted partial, with complete checker and cleanup logs.
- FirstSigns.lean is a draft: a hypothetical17-binary least circuit starts with positive OR or double-negative AND. It was not compiled.
- ReadTwiceEssential.lean proves a least17-binary circuit has at least two primary origins used in exactly one binary operand slot.
- SingleUseAny.lean proves a sole primary reader cannot combine two signed primary literals, even after an arbitrary prefix.
- StrictRestriction.lean tracks extra binary savings when restriction makes a previously nonprimary wire constant; SharedSecondReader.lean gives the two-coordinate information obstruction.

Every proof source and generator is under lemmas/ or this folder. Full build, checker, axiom and independent review outputs are under validation/. Search experiments are documented separately and establish no unrestricted lower bound or counterexample.

The branch is a backup branch with results files. A valid submission still needs a freshly leased posted gap and a clean single-file proof branch; these partial theorem names are not posted gaps.
