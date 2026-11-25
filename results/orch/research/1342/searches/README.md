# L-meta-1342 research archive

This archive preserves completed genetic and symbolic searches by the toolchain_setup agent. No valid21-gate circuit was found. The strongest near candidate computes the target OR(x9 AND x10), with four false positives among2048 assignments. Its invalid status is documented in genetic_cpp/near-false-positive-audit.json.

Start with genetic_cpp/FINDINGS.md and symbolic_templates/FINDINGS.md, then their validation.json files. All original source variants, result snapshots, independent audit JSONs and complete retained stdout/stderr logs are copied byte-for-byte. Compile logs that were empty remain empty. The symbolic run-001.log is a complete startup failure diagnostic; the three completed symbolic runs are separately identified in its FINDINGS.md.

The genetic collection records11completed45-second bursts and1,527,014,525mutation attempts. The symbolic collection records three45-second solver timeouts with no incumbent. These are bounded heuristic searches, not exhaustive impossibility results. Early genetic snapshots count redundant or inactive junk ANDs; only later irredundancy-aware snapshots are identified as meaningful two-unit near architectures.

No executable binaries, caches, lease data, desk responses, credentials or authentication material are included. The compiler capability output is retained in diagnostics/compiler-help.log. Original scratch-source paths appear only as provenance and in original scripts/logs. Symbolic scripts use NumPy/SciPy and retain their original output-directory constant; adjust it explicitly when reproducing outside the original scratch tree.

MANIFEST.json records each included payload file's byte length and SHA256. It does not hash itself. All payload logs are complete files, never head/tail excerpts.
