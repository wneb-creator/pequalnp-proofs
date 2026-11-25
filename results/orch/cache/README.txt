These source modules reproduce the scratch compilation dependencies for partial components.
FewNotBase is the checked FewNot source with private modifiers removed; PermutationSupport is the checked permutation source; RowEmbeddingSupport shares definitions from FewNotBase and adds the checked row embedding lemmas.
Build within the pinned lean project using lake env lean, with this directory added to LEAN_PATH and the module root set here. Compile FewNotBase, then PermutationSupport and RowEmbeddingSupport, before files that reference them.
Final proof submission must inline needed declarations and retain only permitted project imports.
