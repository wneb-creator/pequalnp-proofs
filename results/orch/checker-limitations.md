Local checker storage limitation

Recorded 2026-11-25T14:13:25.281999+00:00.

Verdict: CHECKER FAULT (infrastructure), not a rejected Lean proof.

The pinned Lean v4.36.0 toolchain, actual Mathlib dependencies, PEqualNP.Defs, and checklemma executable build successfully. The real cached Mathlib targets passed --no-build (4,974 jobs); PEqualNP.Defs passed its build (5,147 jobs); checklemma passed its build (5 jobs). Full logs and setup summary are preserved in validation/.

The local checker subsequently stopped with this complete diagnostic:

    checker fault: object file '/workspace/pequalnp-proofs/lean/.lake/packages/batteries/.lake/build/lib/lean/Batteries.olean' of module Batteries does not exist
    CHECKER FAULT: the verifier ended without a verdict (exit 3).

Why the larger cache is needed: lean/CheckLemma.lean declares statementLibrary = Mathlib at line 64 and imports both Mathlib and the definitions root at line 355. Thus the checker loads all Mathlib even when the submitted file uses only PEqualNP.Defs. The genuine Mathlib root artifact alone does not provide its transitive dependencies. No fake artifact or checker change was used.

Pinned Lean source confirms that merely retaining public .olean files is insufficient. Lean/Environment.lean:2443-2455 reads a module's .olean.server and .olean.private files whenever its public artifact uses the module system. importModules defaults to the private level (lines 2808-2810). IR may also be needed for extension initialization. Deleting those runtime parts would break authentic imports.

Storage: the container has a 7.9 GiB overlay. The Lean toolchain alone occupies about 3 GiB; required ordinary dependency/build artifacts consume most remaining space. The full statement library cannot presently fit alongside them. Existing complete dependencies were retained; only unused optional artifacts and duplicate scratch cache links were cleaned. The checker itself and pinned configuration remain unchanged.

An authentic compressed-storage route was investigated: a read-only FUSE prototype, intended to serve exact official artifact bytes from compressed files, compiled against official libfuse 3.17.2 headers and the installed library. Its mount point was strictly inside the authorized scratch directory. The mount failed with the complete result:

    fusermount3: mount failed: Operation not permitted

The mount command exited 4. No mount was created, and no cache files were replaced. CAP_SYS_ADMIN is absent. After this denial, storage workaround attempts stopped; no privilege workaround was attempted.

Authoritative checks have not been run or claimed accepted by this note. The local checker limitation remains unresolved. The preserved partial proofs retain their separate Lean compilation status; that does not imply the posted full statement is proved.
