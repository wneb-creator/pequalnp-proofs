# Unfinished joint certificate assembly

These are preservation artifacts, not a submitted proof of L-meta-2592.

- `JointReadable.lean`: the shared monotone/signed nine-input certificate from checked L-meta-9818, renamed into the current gap namespace, plus the already checked seventeen-binary-gate machinery and a mode-generic circuit bridge. Its build completed successfully at14:43:55UTC, exit0, session91625, approximately19m18s. The complete diagnostics and exit status are retained. This readable file exceeds the 512 KiB submission cap.
- `MonoReadyReadable.lean`: an uncompiled assembly adding the conditional monotone-eighteen derivation, its actual-circuit wrapper, and extraction of constant NOT gates. Obsolete Sixteen-only helpers were removed. This readable file also exceeds the submission cap.
- `MonoReadyCompact.lean` and `MonoReadyCompactShift.lean`: attempted compact versions. The latter was interrupted after lexical errors; the full diagnostics are retained in `mono-ready-full.stdout` and `.stderr`. Neither version is checked.

The compact failure was caused by removing spaces around Unicode operators: for example, an arrow followed by the identifier `owns` became the registered `→o` notation followed by `wns`. Future repair must preserve these operator boundaries. The one-space indentation shift preserved relative layout and passed a small syntax test, but the whole compact source did not compile.

Separately preserved checked components include MonoPublic, SignedConstantNot, and SignedConstantNotFloor. The monotone-eighteen and constant-NOT prefix bounds take the nine-input monotone floor as an explicit hypothesis. Their success does not certify the unfinished combined file.

Only the root agent holds leases, pushes results, and decides the final delivery. The existing joint build finished before the root's cutoff. No further build or proof work was started after completion.

The checked joint source establishes `PEqualNP.Outside.L_meta_2592.Signed.nineMonoFloor` (nine-input monotone binary floor16), `nineFloor` (signed binary floor15), and `Extended.realizeOrdinaryMode` (ordinary circuit extraction in either normalization mode, with a no-NOT premise in monotone mode). Its existing `atLeastSeventeen`, `seventeen_binary`, `three_not_impossible`, and `nonOr_first_lower` remain checked. The later concrete `monotone_eighteen` wrapper is only present in the uncompiled MonoReady assemblies. The separately checked `atLeastEighteenMono` and `constant_not_prefix_floor` take the nine-input monotone floor as an explicit hypothesis.

The nine-input core comes from the Core namespace of checked `lean/PEqualNP/Outside/L_meta_9818.lean`. The obsolete `twoRoots` and `directSplit` wrappers were removed,639 internal helper names were shortened, and the namespace was changed. Its nine-input root and target literals agree exactly with the prior signed core. The ten-input machinery and partial bounds come from the already checked Seventeen source; new code connects both root certificates and provides mode-generic extraction. The README records provenance; Lean checking establishes the actual assembled declarations.
