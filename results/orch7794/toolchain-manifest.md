# Toolchain readiness

Lean 4.36.0 toolchain: /tmp/oec/pequalnp-pilot-104/toolchain/lean-4.36.0-linux/bin. Node 24.22.3. Pinned Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.

The storage repair is fully documented in ../orch2962/toolchain-recovery.md, with complete manifests and logs beside it. Required C artifacts and the cache executable were restored. The final read-only verification `lake --no-build -v build PEqualNP.Defs Mathlib.Combinatorics.Hall.Finite` passed: all 5149 targets up-to-date. No Mathlib source build ran. 742 MiB was free after repair.

The exact posted statement is /tmp/oec/pequalnp-pilot-104/7794-statement.txt and matches the desk response except its terminating newline. The source-format guard passed for the currently copied file; that is not a Lean acceptance verdict.

Run the official checker from the repository root with the toolchain bin on PATH, PEQUALNP_REAL_LAKE set to the absolute lake executable above, and PEQUALNP_HOME set under /tmp/oec/pequalnp-pilot-104/ to keep the queue local. Command:

    node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_7794.lean /tmp/oec/pequalnp-pilot-104/7794-statement.txt check

Save complete stdout/stderr. The checker builds its verifier, builds the named file and Defs, checks exact type and axioms, and then performs a no-build freshness check. It deliberately disables the artifact-sharing cache. No checker run has been started by this tooling subagent.
