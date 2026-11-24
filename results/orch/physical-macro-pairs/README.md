# Neutral algebraic physical repair and augmented-pair variant

SearchPhysicalRepairMacro copies the reviewed singleton-rejecting, minimum-dirty beam search and adds neutral associativity/distribution rewrites. Exclusive child fanout and strict wire-order guards preserve all outputs, and every proposed rewrite asserts complete output-signature equality. Both AND/OR duals are supported. A distributive rewrite leaves an identity gate as physical slack. The author checked2683 macros on171,712 exhaustive scalar cases; independent Boolean/topology source review passed.

Completed run007 used seed14772946, target28, width256,40rounds,120seconds, --reject-singletons and --min-nontrivial-dirty 2. It inspected6,680,576neighbors in120.052834seconds and improved the positive-complete seed from49 to48negative errors. The saved artifact is INVALID and rejects every singleton. These restrictions guide a bounded heuristic beam and do not establish necessity or any lower bound.

SearchPhysicalRepairPairs differs from Macro only by accepting SearchAlternative6PairProblem. That module retains the complete24positive+64negative basis and adds19singletons+147nonedge-pair negatives, giving254fitness tests. The original88cases are still scalar-replayed for every purported exact witness. The completed007 seed has60 augmented search errors but48 raw errors. The next focused run008 uses this variant; no run008 outcome is included here.

The complete calibration failures are retained: the first macro harness had an unclosed parenthesis; its corrected002 harness passed without changing the source. The first pair harness mistakenly indexed the evaluate tuple as if it started with size; the corrected002 harness checks wp+wn and passed, again without a source change. These were diagnostic-harness errors, not accepted search results.

Example: `python3 SearchPhysicalRepairPairs.py --problem SearchAlternative6PairProblem --input run007-improved-2.json --output-dir /tmp/oec/pequalnp-pilot-29/physical-repair-alternative6-008 --seconds 120 --rounds 40 --width 256 --seed 14772949 --min-nontrivial-dirty 2 --reject-singletons`, with complete stdout/stderr redirected to a log.
