# Completed triangle finite-field run: independent outcome and archive review

The frozen `triangle-native-r1/` archive passes independent verification against manifest `bc299060ea610658db39f0aa050a3fc6a12f5c3a53ef5dd9ec53281f7f561599`: exactly 19 listed files, 136546 bytes including the manifest, all hashes matching, regular UTF-8 text only. The source and input are byte-identical to those already independently reviewed.

The saved output is exactly the constant basis [1] over F1009. Result metadata records process exit 0, 8.945474994998222 seconds, peak RSS 38260 KiB, one thread, pair parameter 32, and the authorized 600-second/2048-MiB limits. The full log contains 108 completed rounds and final basis reduction. Its largest matrix is 4415×6170. Both computational-statistics blocks are preserved; the first records the solve, while the second follows cleanup and resets counters.

All 21 engine provenance hashes and the parent provenance hash match the reviewed engine files. The archived runner, launch command, executable and shared-library hashes agree, and the executable names the expected shared library with the expected engine directory as RUNPATH.

Both checkpoints parse completely and retain the exact original 26-generator prefix. The first has 52 rows/1372 terms; the final has 27 rows/687 terms, appending only the constant unit. Latest-checkpoint metadata, hash, sequence 2 and round 108 all agree. This checks the saved data and engine binding; the checkpoint is not an independent algebraic certificate.

The README accurately restricts the result to this finite-field computation and makes no characteristic-zero contradiction, rational ideal-membership certificate, or Lean proof claim. No solver was rerun.

Independent reproducer/full log: `/tmp/oec/pequalnp-pilot-75/gct231/triangle_outcome_review.py` and `triangle-outcome-review.log`, completed 2026-11-25T11:53:14.813863+00:00. All review outputs are outside the frozen archive.
