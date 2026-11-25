# Official checker runtime closure investigation

The checker failed at its runtime verifier because Batteries.olean was missing. CheckLemma.lean line 355 deliberately imports the entire Mathlib root plus Defs, at the default private import level. This is broader than the proof's allowed Defs import and than its successful named Lake build.

Read the exact Lean 4.36.0 implementation at https://github.com/leanprover/lean4/blob/v4.36.0/src/Lean/Environment.lean. readModuleDataPartsOfMod loads .olean, .olean.server, and .olean.private; default importModules uses private level and transitive IR. Omitting split private/server artifacts would not be valid. The checker and definitions were not changed.

A reproducible uniform sample of 100 of 6,522 missing Mathlib modules estimated the missing genuine runtime closure at 4,392,723,006 bytes, with official archives totaling approximately 303,333,002 compressed bytes. Sample seed 7794, complete per-module measurements preserved. Available disk was about 686 MiB before the small investigation downloads. Outside source working copies total 429,489,924 bytes; optional native static libraries total about 408.8 MB. Even these savings do not accommodate the missing closure.

Cgroup memory.max is 8,589,934,592 bytes, swap absent. RAM-backed genuine files would consume several GiB in addition to the verifier's own memory.

A standard read-only compressed filesystem was investigated, avoiding checker changes and synthetic artifacts. /dev/fuse exists and could be opened read/write. Built the official libfuse 3.17.2 hello example against the installed matching libfuse3.so.4 and attempted one ordinary read-only user mount. It returned exit 4: fusermount3: mount failed: Operation not permitted. No sudo, retry, or bypass was attempted. SquashFS itself was not built.

All repository proof sources, cached build dependencies, checker sources, and verifier binaries remain unchanged by this investigation. No Mathlib source build ran.
