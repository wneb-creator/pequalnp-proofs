# L-meta-2583 tooling and checker status

Pinned Lean 4.36.0 was installed from the official GitHub release. Its archive
matched the release SHA-256. The nine packages were shallow-fetched at the
exact revisions in the committed manifest; no manifest update was run.

The required full `lake exe cache get` downloaded all 9,117 artifacts but
exhausted the 7.9 GiB overlay while unpacking. No mathematical Mathlib modules
were compiled from source. Disposable archives and downloaded compiled
Mathlib artifacts outside the needed dependency closure were removed; all
sources and committed configuration were preserved.

A narrow cache fetch for 3,233 dependency modules succeeded. A no-build
preflight of all those modules succeeded, followed by a successful build of
`PEqualNP.Defs` (5,147 jobs, 86 project definition modules compiled, zero
Mathlib source targets compiled). Hall.Basic and Hall.Finite were subsequently
restored from the prebuilt cache; both passed `lake build --no-build`.

The unmodified local checker was invoked on the named partial
`lean/PEqualNP/Outside/L_meta_2583.lean` against the posted statement in check
mode. It exited 3 before judging the partial:

    CHECKER FAULT: the prebuilt Mathlib cache is missing. Run `lake exe cache get` in lean/ (RUNBOOK.md, section 2).

The full-gap theorem is absent from that partial. This fault is neither an
acceptance nor a rejection of a proof. Complete checker output is saved in
the job scratch directory as `checker-2583.stdout`, `checker-2583.stderr`, and
`checker-2583.exit`.

## Memory-backed artifact feasibility

A Linux memfd capability test passed: a second process read an anonymous
memory-backed file through a symlink under the authorized scratch directory.
The test file, descriptor, and symlink were then removed. No permanent memory
cache was started and no full-cache restoration was attempted after this test.
The process descriptor limit is 16,384.

At measurement after Hall restoration, `free -b` reported 10,452,459,520 bytes
total RAM, 8,684,478,464 bytes available including reclaimable cache, and no
swap. The overlay had 368,373,760 bytes free. An earlier figure obtained from
SC_AVPHYS_PAGES represented free physical pages, not Linux MemAvailable, and
must not be treated as the total available memory budget.

Memfd storage could move selected immutable downloaded artifacts off disk
without writing outside the repository and scratch paths. A holder process
would have to remain alive for every consumer; loss of that process would
invalidate its artifact symlinks. Its memory, descriptor count, and the
checker's peak memory would all need budgeting. Full-cache size and checker
peak have not been measured in this container, so feasibility of a complete
checker run remains unconfirmed. The checker has not been changed or weakened.
