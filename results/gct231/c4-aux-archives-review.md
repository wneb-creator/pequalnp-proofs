# C4 auxiliary archive integrity and outcome review

Both frozen archives pass independent exact manifest coverage, SHA256, regular-file and UTF-8/text-only checks: `c4-U-route/` has 40 files under manifest `d96a269ec89ff2a1b3ea1f4b6be02d982a5b2e6cd6df523358909515cc398949`; `augmented-c4-small-batches/` has 19 files under manifest `1da49c356b698efec19b98ac2003649dc3672275b1ead8037c4a98a55bce0c11`. Both archived independent U-route reviews match their original files exactly.

The saved completed F1009 runs have unit output [1], matching input/output hashes, one thread, the recorded limits, and the previously reviewed binary/library hashes. The six comparison records were recomputed from the complete logs, confirming every round count, largest column count, elapsed time and maximum degree. The adjacent notes correctly restrict these results to finite-field computation and conditional U=0 algebra; no characteristic-zero unit conclusion follows from them.

Standalone source/full log: `/tmp/oec/pequalnp-pilot-75/gct231/c4_aux_archives_review.py` and `c4-aux-archives-review.log`, completed 2026-11-25T11:46:15.524976+00:00. The initial reviewer attempt assumed integer rather than string encoding for the basis coefficient; its diagnostic log is preserved and the corrected parser passes. No solver was rerun.
