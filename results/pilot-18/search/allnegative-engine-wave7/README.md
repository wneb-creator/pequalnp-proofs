Frozen 141-row candidate engine and independent review

Source SHA256 18efdd149487dfee83693dd0781a17316ba0fda9d68c43c6c70c73f96a77250b.
Reviewed optimized binary SHA256 7d802a63b218449bd58178785a917a363edecedace5f65201344804dec3a3870.
Independent review 23a3c36f8a714214fbe4df4cff142820cfef6d091d9401793f74c255442253c2.
Production-plan review 62f416117e7717595e76c3db9d054f4754d01c5aa1ee25be92f2f1fbd784ba40.

The archive includes current/parent C++ sources and exact diff; original build and all finite main/S08 control logs; source and metadata for both seed packs; unchanged wrapper, raw validator and normalizer; full hash-bound reviews; and prelaunch plan. Three ELF binaries are omitted with sizes/hashes in the manifest; their source and build commands remain. Compiler output does not imply portable byte-identical binaries on other toolchains. The historical main-review says independent review pending and production not launched: these fields describe its frozen prelaunch time and are superseded by the S08 review and later main launch, respectively.

The sole production-derived addition is the explicitly supplied immutable best4 snapshot b6da8ac6962d7836f2e5546423f5ed3846b7165fbe1ae47e58b8e470955101b0 and both scalar reviews. Independent 2048-input evaluation gives zero FN and FP [21,29,85,149], exactly F OR (x0 AND x2 AND x4), 21 live gates. It remains inexact. No active worker directory, evolving log, or final production result is included or inferred. Main's one-iteration control is UNKNOWN; deliberately false-candidate control is expected ERROR/validator exit2 and its full traceback is retained.

Fitness uses 16 minimal positive edges plus all125 negative inputs. Zero edge-FN/full-FP is equivalent to exactness for valid monotone gates; the unchanged engine and independent validator still check all2048 inputs before accepting a candidate. FN is edge-only, FP is now full-negative count, and energy includes the live-gate fraction. Main evidence includes2,048,000 scalar comparisons; S08 independently tested1,073,152 scalar inputs underUBSan plus word/mask/operator boundaries, weighted scores, four exact22 controls, the exact binary's finite selftest and actual wrapper rejection. No performance guarantee, exhaustive search, exact21 witness, Lean theorem or posted acceptance is claimed.

Finite source-control reproduction after extracting this archive, from its root:
  mkdir rebuild
  g++ -std=c++17 -O1 -g -fsanitize=undefined -fno-sanitize-recover=all -Wall -Wextra -Werror review/independent_review_controls.cpp -o rebuild/independent_review_controls
  rebuild/independent_review_controls dependencies/packs/best3/direct-seeds.txt dependencies/packs/legacy/seeds.txt
  g++ -std=c++17 -O3 -Wall -Wextra -Werror review/snapshot/main/circuit_anneal_allnegative.cpp -o rebuild/circuit_anneal_allnegative
  rebuild/circuit_anneal_allnegative --pack dependencies/packs/best3/direct-seeds.txt --output rebuild/selftest.json --seed 134231 --self-test
Only finite selftests are shown; production commands are historical evidence and are not reproduction steps. Original wrapper/controller commands retain their absolute workspace paths. The independent C++ control above is portable within the extracted directory tree. Archive verification hashes all payloads; it does not execute commands.
