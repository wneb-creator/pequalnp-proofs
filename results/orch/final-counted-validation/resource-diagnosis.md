# Pinned Lean 4.36.0 import-memory diagnosis

Read-only investigation on 2026-11-25. No proof, checker, runtime, or artifact-cache modifications were made for this investigation.

## Confirmed mechanism

The unchanged `lean/CheckLemma.lean` retains the statement environment from `importModules [Mathlib, Defs]` at lines 355–356 while separately importing the proof at line 380. It later imports the definitions' dependencies a third time at line 411.

Pinned Lean 4.36.0 `src/Lean/Environment.lean`, lines 2808–2820, starts a new import state on every `importModules` call. The native reader has no global region reuse cache. In `src/library/module.cpp`, lines 524–541, it attempts `MAP_PRIVATE | MAP_FIXED_NOREPLACE` at the base address stored in each artifact. If the address is occupied, lines 558–573 allocate a complete heap buffer and read the entire file into it. The subsequent reader relocates the objects. Therefore later imports of dependencies already mapped by the first environment require additional anonymous-memory copies. Renaming files, changing symlinks, or using hard links does not change the stored base addresses or remove this collision.

Pinned sources:

- https://github.com/leanprover/lean4/blob/v4.36.0/src/library/module.cpp#L524-L573
- https://github.com/leanprover/lean4/blob/v4.36.0/src/Lean/Environment.lean#L2808-L2832
- https://github.com/leanprover/lean4/blob/v4.36.0/src/Lean/Environment.lean#L2672-L2800

The default `leakEnv` is already false. That setting cannot release the live statement environment, and compacted region lifetime is separate from ordinary reference-counted collection. The explicit `withImportModules` helper frees regions only after its callback, with no live references; it deliberately disables extension loading. Substituting that helper would change checker code and is outside this task.

## Operational conclusion

The local checker filters `LAKE*`, `LEAN_*`, and `ELAN_TOOLCHAIN` variables but preserves allocator variables. Existing attempts already set immediate mimalloc purging and disabled transparent huge pages. Such settings cannot reclaim live imported buffers. Moving exact memfd-backed artifacts to ordinary disk would make their original backing pages reclaimable, but it would not remove the later anonymous import copies. The filesystem had approximately 39 MB available during this investigation, insufficient for the remaining approximately 1.7 GB of RAM-backed runtime artifacts.

No supported pinned-runtime environment switch was found that makes these imports share regions. The realistic route preserving checker, trust level, initialization, toolchain, and exact proof bytes is to run the unchanged checker on the normal CI runner with sufficient RAM/swap. A source/toolchain upgrade or checker modification is not an equivalent local verification.

## Evidence copies

Read-only source responses were decoded into scratch files `resource-module.txt`, `resource-environment.txt`, `resource-compact.txt`, `resource-memory.txt`, and `resource-mimalloc.txt`. GitHub blob SHA for the pinned module reader: `402e5220e1379d1204beefec0817ce9dda74294a`.
