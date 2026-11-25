# Checked scalar certificate: C4 open case 0, zero extension parameter

**Lean PASS**, exit 0 in 70.888 seconds, peak sampled process-group RSS 4,506,616 KiB. `C4Case0Zero.lean` is 42,649 bytes / 54 lines, SHA256 `83e6d1460f944d357842868e06cee2c1af2d2093a8edef62d6458e4daa8debe7`. The exact-source audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

The theorem proves a contradiction from four explicit complex polynomial equations in two variables. These are necessary resultants for the fixed-C4 support family's nonzero-product pencil, permutation 0, det(W) nonzero, extension parameter v=0. Independent reviews verify the geometric necessity, factor-removal conditions, resultant formulas, exact input mapping, and rational certificate DAG. This is a scoped scalar helper, **not** the full C4 theorem or the posted gap.

The exact rational solver completed in about 0.01 seconds. Its dependency slice and exact replay give 23 needed polynomial steps. The Lean proof checks every polynomial identity through `linear_combination`; no solver verdict, new axiom, sorry, or native_decide is used. Complete solver, replay, emission, Lean and axiom-audit outputs are preserved here.

The archived elimination source retains the initial failed diagnostic (a missing symbolic variable in a temporary polynomial-domain declaration) and the corrected successful diagnostic separately. That failure produced no result used by this certificate. The original failed saturated nonzero proof emission is outside this snapshot.

All review files are copied unchanged at top level, excluding Python cache directories. Shared trace-engine provenance and reviewed replay sources are in sibling `neogb-trace`, `neogb-compact`, and `neogb-slicer` archives. The exact source audit file is for verification only and is not a PR proof file.
