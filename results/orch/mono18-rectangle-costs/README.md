# Complete mono18 rectangle costs

This archive preserves the complete checked rectangle-cost table shared by the fresh strong and weak mono18 first-OR-edge exports. It contains 19 coefficient arrays, 39 sample instances, 6,159 support/cap records, and 108 bounded computation blocks. All 177,807 subset checks (including 123 empty-support cases) passed Lean kernel evaluation. Every strong-export profile occurs in the weak table.

The 27 data modules and their shared base/consumers are listed with exact source/log hashes in `sources.json`. Sources and complete compile logs live at the archive-relative `../lemmas/` paths listed there; every listed module compiled with exit 0. The table build used 437.7 seconds including queue waits and peaked at 4,405,936 KB RSS. The historical status files retain original container paths as provenance, not as replay dependencies.

The checked semantic chain is: packed rectangle maximum (`RectanglePackedCheck`) → record validity (`Mono18RectangleBase`) → actual sample support (`Mono18RectangleSamples`) → correct target sample labels (`Mono18RectangleLabels`) → duplicate-preserving tight monotone Run contradiction (`Mono18RectangleBank`). `Mono18RectangleLookup` provides checked record retrieval. `Mono18RectangleNode38` applies the chain to the actual weak-trace leaf with 17 root occurrences, remaining budget 16, target weight 79 and root-cost sum 76.

These are rectangle-cost certificates and one actual leaf consumer. They do not establish exhaustive DAG coverage, all cofactor cuts, a complete first-gate case, or the posted theorem.

## Source regeneration

Copy this archive to a writable scratch directory, then run `python3 code/generate_complete.py`. It reads only the bundled `mono18-oredge-weak-census/weights.json` and `profiles.json`. It regenerates all 27 data-module sources in `code/`, together with block/locator/compile-plan files. This exact regeneration was tested in a fresh directory: all 30 generated files matched the compiled originals byte-for-byte. Generic proof sources are the immutable `../lemmas/` files, not generated output.

`code/generate_samples.py` additionally reads the bundled `matrices.json` and reconstructs the sample adapter. `generate_node38.py` is preserved as historical export code; it reads the original full trace at its recorded container path. The complete immutable node38 values and profile links needed to audit the checked leaf are included in `node38.json`, so that trace path is not a dependency of the cost-table replay.

`compile_one.py` and `compile_all.py` preserve the original build invocation and queue-aware environment used in this job; their absolute launcher/cache paths are historical environment details. To compile in a new prepared Lean workspace, place the listed generic dependencies and generated modules on LEAN_PATH and invoke Lean 4.36.0 through the project's lake environment. No lake update was used.

Independent exact profile/weight auditing is archived alongside this folder in `../mono18-packed-profile-audit/`; mathematical reviews are `../review-mono18-rectangle-base.txt`, `../review-mono18-rectangle-consumers.txt`, and `../review-mono18-rectangle-adapters.txt`. The final lookup/leaf review is separate when available.

The rectangle-specific source budget is 130,642 bytes excluding the optional 4,950-byte node38 smoke and the existing Run/BitVec/cofactor foundation. This is the current checked representation; optional further fixed-width packing has only been measured, not substituted.
