Lean v4.36.0 installed from official GitHub Linux release under /tmp/oec/pequalnp-pilot-118/toolchain/lean-4.36.0-linux. Archive size 607649028 bytes; omitted editor .ilean files and bundled source, retained compiler/runtime artifacts. No pre-existing accessible toolchain/cache was present.

Use `. /tmp/oec/pequalnp-pilot-118/lean-env.sh` before `lake` or checker calls. This sets the real Lake path, repo queue shim on PATH, and scratch cache/build-state paths; it contains no credentials.

Initial full `lake exe cache get` bootstrapped pinned package sources and the official cache tool, then was interrupted because full Mathlib would exceed the 7.9 GiB filesystem. Exact 67 direct Mathlib imports used by PEqualNP.Defs expand to 2480 prebuilt cache files; all downloaded and decompressed successfully. Genuine Mathlib root artifact (hash 79da901f0eeeaa4a) was also fetched from official cache for the checker's presence check. Narrow imports are necessary; importing all Mathlib needs further cached modules. No Mathlib module built from source.

Full logs: /tmp/oec/pequalnp-pilot-118/lean-download.log, lean-extract.log, mathlib-cache.log, mathlib-defs-cache.log, mathlib-root-cache-download.log, mathlib-root-cache-extract.log. Pinned configuration unchanged.

Setup complete: targeted cache exit 0, Decompressed 2480 file(s). `lake build checklemma` passed (5 jobs); full log /tmp/oec/pequalnp-pilot-118/checklemma-build.log. `lake build PEqualNP.Defs` passed; full log /tmp/oec/pequalnp-pilot-118/defs-build.log. No Mathlib source modules compiled. Proof agents can now use the environment script and ordinary lake build or lake env lean.
