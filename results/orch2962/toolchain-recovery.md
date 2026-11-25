# Disk recovery and finite Hall cache

Recovered from a full filesystem by removing 2,957 regenerable Mathlib native C files under its build/ir directory (263,027,242 bytes). Retained every Lean artifact, dependency source, proof, search checkpoint, and log.

Preserved the cache executable as /tmp/oec/pequalnp-pilot-104/toolchain/cache-executable.gz (34,576,764 bytes), verified that decompression hashes to the original SHA256 253379b9758269d38f80239d274ef0fc6d0595944e0fabae5a1741999c5e5758, then removed its 124,968,488-byte uncompressed copy. Restore it to lean/.lake/packages/mathlib/.lake/build/bin/cache and make it executable before further cache commands. Do not let Lake rebuild it incidentally.

Disk free after recovery: 308 MiB. No .olean.server or .ilean file was removed.

Looked up exactly Mathlib.Combinatorics.Hall.Finite: cache hash 84671f9ea5a4327d. Fetched its one official archive from https://cache.mathlib.org/mathlib4-master/f/84671f9ea5a4327d.ltar and extracted it. No dependency closure download and no Mathlib source build. Both immediate dependencies were already present.

The test importing PEqualNP.Defs plus Hall.Finite and checking Finset.all_card_le_biUnion_card_iff_existsInjective' passed (exit 0); stdout contains the expected finite-index theorem signature and stderr is empty. Complete lookup, fetch, extraction and test logs are in counting-logs. The lookup command exits 1 only because it additionally attempts to read comments from the as-yet-undownloaded archive; its printed hash was then downloaded and verified by the successful import.
