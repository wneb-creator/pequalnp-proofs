# Final L-meta-982 review

The scratch modules and checkpoint branch are not the final proof artifact. Apply these checks to the assembled single file and to the Mac's clean proof branch.

- The final file is exactly lean/PEqualNP/Outside/L_meta_982.lean, regular UTF-8 text, not executable, at most 512 KiB. Its PR adds that one file and changes nothing else.
- Imports are only allowed modules, at the very top, one plain import per line. No occurrence of the import word follows that initial block.
- The last declaration is theorem PEqualNP.Outside.L_meta_982 with the exact posted 31-conjunct statement from next-2025.json. No helper definitions, local notation, instances or namespace shadowing change the statement's interpretation.
- Each of the 14 finite cores discharges its complete upper-budget no-run premise, including shorter actual runs. The 17 structural routes use the exact checked core bounds. No conditional bridge is mistaken for an unconditional result.
- All helpers are in the approved theorem namespace or its auxiliary namespace. Namespace/section/end lines start in column zero, and every end names its scope.
- There is no `_root_` substring anywhere, including comments and identifiers. Rename scratch seed0_root_perm/seed8_root_perm to seed0_rt_perm/seed8_rt_perm consistently.
- There are no double quotes, command directives, compile-time code mechanisms, new axioms, sorry terms, or native decision shortcuts. The final theorem's axiom query must report only propext, Classical.choice and Quot.sound.
- Attributes, if present, are only simp or local simp. Prefer no global helper instances or simp attributes. No custom data type declarations.
- The only option names allowed are maxRecDepth, maxHeartbeats, synthInstance.maxSize and synthInstance.maxHeartbeats. Each is a numeric set_option line ending in in and scoped directly to its declaration. Scratch global options and diagnostic commands must be removed.
- Run the pinned lake build for the named file, then the repository checker against the exact desk statement. Preserve full output. A checkpoint compilation or Python round trip is not the repository checker's acceptance.
- Before delivery, independently inspect the complete final diff and source hash. The cleanup version must pass the same build and checker. Record measurement lines and cleanup line counts as requested by the owner.
