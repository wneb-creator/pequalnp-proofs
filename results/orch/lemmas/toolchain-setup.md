# Toolchain setup

UTC 2026-11-25 13:50:27: official Lean 4.36.0 installed in scratch. The prepared environment described by the job was absent: no Lean binaries or .lake cache existed.

Use `. /tmp/oec/pequalnp-pilot-96/lean-env.sh` before Lake/checker commands.

Downloaded official pinned Mathlib cache for the 67 Mathlib imports from PEqualNP.Defs plus Mathlib.Tactic.FinCases and Mathlib.Tactic.NormNum: 2480 files, exit 0. No Mathlib modules built from source.

The genuine Mathlib.olean root artifact was fetched separately from the official cache using hash 79da901f0eeeaa4a, because the checker tests its presence even when the target imports only selected modules. The entire unused Mathlib dependency closure is not cached. Do not use `import Mathlib`; use only PEqualNP.Defs and selected cached modules. Checker source remains unchanged.

Full diagnostics are under /tmp/oec/pequalnp-pilot-96: lean-download.*, lean-extract.*, cache-help.*, cache-selective.*, cache-mathlib-lookup.*, cache-mathlib-root-*.

The initial root-artifact extraction command placed a duplicate in the project build folder because leantar requires options before file arguments. All those accidental duplicates were removed, then the artifact was extracted in the correct Mathlib package folder.

UTC 2026-11-25 13:51:00: root renewed lease and authorized project Defs/checklemma build. Full output: project-setup.stdout and project-setup.stderr.

2026-11-25T13:55:51.153523+00:00: `lake build PEqualNP.Defs checklemma` succeeded, 5151 jobs; no Mathlib source rebuilds. Removed 156496578 bytes of downloaded .ltar archives after successful extraction/build to recover space. All installed artifacts remain.

Correction after inspecting verifier implementation: CheckLemma fixes its statement library to all Mathlib, so the selective cache supports proof compilation and building the verifier, but not a complete verifier run. A genuine root artifact alone is insufficient for checker acceptance. The checker has not accepted the full gap, and no such claim is made.

Readonly storage study: /workspace and /tmp share an 8.417 GB filesystem; /dev/shm has 5.226 GB but is outside the permitted scratch scope, so it was not used. The pinned Mathlib contains 8712 source modules, versus 2189 cached Mathlib modules. Count-based extrapolation is about 7.40 GB for the full cache, or 5.95 GB for olean/private/server alone; these are estimates, not measured complete-cache sizes. Static toolchain archives total 427.5 MB and compiler LLVM/clang libraries total 146.3 MB; deleting these would prevent subsequent native links, so none were removed.

BVDecide probe: Mathlib.Tactic.BVDecide is absent, and no Mathlib source imports BVDecide. A direct test under PEqualNP.Defs failed requesting Std.Tactic.BVDecide, whose direct import is outside the gap allowlist. No additional cache module was fetched. Boolean distributivity lemmas Bool.and_or_distrib_left and Bool.and_or_distrib_right exist in pinned core and provide an alternative for fixed-circuit symbolic verification.
