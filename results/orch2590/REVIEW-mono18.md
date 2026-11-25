# Independent review of monotone Petersen partial

Reviewed 2026-11-25T15:21:12.481219+00:00

Input: `results/orch2590/lemmas/Mono18.lean`, SHA256 `ca145c55fe4e69cd551725a543318b389e73a4e3cc93299a3f015819b020e26f`,519562bytes7398lines. Reviewer: status_check, independent of author lower_bound. Full compilation is pending at this review timestamp; this review is not a checker verdict.

## Verdict

No semantic or plain-file issue found in the stated partial claims. The exported claims are only `monotone_size_eighteen` and normalized `first_and_floor_nineteen`. Neither proves the posted size20 theorem. This source alone cannot be submitted as the target proof.

## Mathematical checks

- The large nine-variable certificate prefix is byte-identical to the exact line ranges of checked L_meta_4332 specified by generate_mono_base.py, except namespace replacement. Its inputs/graph constants are byte-identical to checked L_meta_6581. No coordinate permutation is required.
- `nineMonoFloorOfCert` uses the existing essential-input witnesses to turn `Impossible false graph15 inputs.toFinset` into the general `Lower false inputs graph16` interface. Thus constants remain freely available in the projection model.
- `realizeMono` uses Monotone2, not an unmentioned exact-two/readback condition. Existing `gate_rep` handles empty-input AND/OR constants, unary gates, invalid wire references via getD zero, and duplicate or unused semantic values. The extraction counts at most the original gate count.
- `Live false` only permits AND and OR: the signed alternatives require false=true. The stronger helper handling d<4 is harmless, and no signed operation is introduced into a monotone projected computation.
- The old Geometry is reused with elementary replacement bit lemmas. Its projection sends the chosen pin to zero and Petersen target to the exact nine-variable graph. Supplied raw first binary projects to zero or a remaining pin; a supplied AND projects to zero.
- Independent row witnesses force the chosen pin to be live in the suffix. The mass charge1 is for its constant projection; in the AND case, the distinct supplied conjunction is also live and contributes a second constant charge. Freshness supplies distinctness. The generic projection accounting then gives suffix floors17/18 and total floors18/19.
- No assumption about the first syntactic gate is silently added to `monotone_size_eighteen`. `first_and_floor_nineteen` explicitly concerns the normalized semantic Live trace.

## Format and preservation

Only `import PEqualNP.Defs`; all declarations are in the target subnamespace. No `_root_`, quotes, sorry, axioms, native_decide, code-execution commands, forbidden attributes, or disallowed options found. All checked limit options use the permitted per-declaration form. No credentials or external executable content found. There are4726bytes remaining under512KiB; a future final theorem/auxiliary additions must recheck this cap.

Re-run compilation and the exact posted-statement checker before any proof PR. Partial branch preservation can identify this honestly as a partial18/19 lower bound after compilation succeeds.
