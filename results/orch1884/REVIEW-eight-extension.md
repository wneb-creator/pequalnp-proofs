# Independent review: EightExtension

UTC: 2026-11-25T16:48:36.498173+00:00

Verdict: PASS for the unconditional eight-input FanInTwo floor12, dependency-tested against the fully compiled GeneralReaderStandalone. Exact source SHA256 `32c56c28b9d4ed667b887aa8a8bdf0a07642cad0a349c6f850e411a8b4eacbd2`, 6371 bytes/151 lines. Author reported Lean exit0; complete archived eight-extension-checked.stdout/.stderr were inspected, with no error diagnostics and empty stderr. No new Lean compilation was run by this reviewer.

The input permutation injects the eight inputs into nine coordinates other than1. Original gate-wire indices shift byone. remap_run compares entire evolving banks and covers old valid positions, the appended gate position, and invalid/forward positions separately; false defaults remainfalse during execution. No backward-read premise is assumed for the input circuit. initial_rows establishes the reindexed primary-input equality.

Four appended gates compute the missing vertex1 star on neighbors0,6,2 and OR it with the previous output. The edge_split identity was independently verified on all512nine-variable inputs. The original output must be a valid wire because the computed eight-input function is true atalltrue; otherwise its default value would befalse. This validity proof is necessary before appending gates: an originally invalid output index could otherwise become a newly appended live wire. The proof explicitly establishes it and then uses wire persistence and the four-gate evaluator.

The grown circuit remains FanInTwo and has exactly originalsize+4. The previously checked actual nine-input general lower bound16 therefore yields originalsize≥12. The theorem is not limited to monotone circuits and permits library-style nullary/unary gates, NOT gates, and invalid operands in the original circuit. It does not depend on the earlier conditional theta helper.

The import GeneralReaderStandalone is a scratch dependency, so this source is not itself a permitted final standalone file. Its full dependency is already independently reviewed and compiled; an allowed-import assembly would still need a separate check. Namespace L_meta_1884.EightExtension, no options, attributes, strings, forbidden constructs, new axioms, unsafe declarations, or secret-like content; below512KiB. No full L-meta-1884 theorem is claimed.
