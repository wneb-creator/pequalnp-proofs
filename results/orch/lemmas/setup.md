# Environment setup

- The kit's prepared environment was absent: no elan proxies, no preparation marker, and no `lean/.lake` directory.
- Installed official elan 4.4.0 in `/tmp/oec/pequalnp-pilot-109/toolchain/elan`; no shell profiles or HOME paths changed.
- Installed and verified pinned Lean `leanprover/lean4:v4.36.0` (commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`).
- Pinned Mathlib revision: `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
- Full installation logs live under `/tmp/oec/pequalnp-pilot-109/toolchain/`.
- Required environment: `ELAN_HOME=/tmp/oec/pequalnp-pilot-109/toolchain/elan`; `PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-109/toolchain/elan/bin/lake`; prepend the elan `bin` directory to PATH. Keep caches in scratch with `XDG_CACHE_HOME=/tmp/oec/pequalnp-pilot-109/toolchain/cache` and `MATHLIB_CACHE_DIR=/tmp/oec/pequalnp-pilot-109/toolchain/cache/mathlib`.
- Materialized all pinned dependency checkouts. `lake exe cache get` completed with exit 0: all 9,117 prebuilt artifacts downloaded and decompressed. `Mathlib.olean` verified present. No Mathlib source build and no `lake update`.
- Current full cache logs: `cache-get-scratch.stdout` and `cache-get-scratch.stderr` under the toolchain scratch directory.
- Use `source /tmp/oec/pequalnp-pilot-109/toolchain/env.sh` for subsequent commands. This puts the repository queue wrapper first in PATH and keeps queue/cache state in task scratch via `PEQUALNP_HOME`.
- `lake build +PEqualNP.Defs` completed with exit 0; the root definitions olean is available. Full logs: `defs-build.stdout` and `defs-build.stderr` under the toolchain scratch directory. Existing module-system warnings only; zero Mathlib modules built from source.
