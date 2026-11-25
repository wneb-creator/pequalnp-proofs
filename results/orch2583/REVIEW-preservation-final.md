# Final L-meta-2583 preservation review after lease loss

Verdict: PASS for preserving the exact versions in `REVIEW-preservation-final.sha256`. This review authorizes no mathematical acceptance claim: the posted theorem remains unproved, and the local checker has not been run for the incomplete target.

Scope: all 220 files then present under `results/orch2583`, plus the named Lean file, for 221 hashed files totaling 2,959,496 bytes. The manifest and this review are additional text records and do not hash themselves. All files were stable at the final hash comparison. No proof/search work or Lean build was started during this preservation review.

The whole tree consists of UTF-8 text without NUL bytes. Credential-pattern scanning and source/diagnostic inspection found no credentials, private keys, authenticated URLs, executable binaries, compiled objects, or solver-state binaries. The archived DIMACS CNFs are ordinary text. The 50.9 MB public upstream source copies were not added; the pinned revision and 337 final-statement extraction are preserved instead.

## Named Lean checkpoint

The final named file is 519 lines and 21,917 bytes, SHA256 `390d65ae6bd3efe27b1a04ead0bfc540c17617ccab33a4666ae8513a602e1a41`. Its first 399 lines have exactly the previously reviewed geometry/deletion hash `eba26c08cfd4bc65b81c609fcc820eff7bd9df7264daaa0ff00aa4ac9306969f`. The remaining CounterExample namespace is byte-identical to the corresponding body of the separately reviewed `TwoJunkIrreducible.lean`.

`build-irreducible.stdout` is the final assembly build log, distinct from the earlier `build-twojunk.stdout`. It reports the named module built in 12 seconds and `Build completed successfully (5149 jobs).` Its stderr is empty. Root records exit 0. The three standalone TwoJunk compiler logs are also preserved; the reviewed strongest component has empty stdout and stderr. The P5 example establishes local irreducibility and explicitly proves nonminimality, not a counterexample to the posted projective-plane theorem.

## Search and research scope

The stopped stochastic logs now include complete final counters: 26,647,000 coordinate steps with best 27 live gates; 8,831,000 with best 20 OR gates; and 2,846,000 with best junk-objective score 108. The last value is an objective score, not a gate count. All three stderr files are empty. No 26-gate or 19-OR witness is claimed. The prepared fixed-size source was not started.

The four productive full-Fano first-gate cases all report UNKNOWN after their time limits. The new squarefree-proof encoder has validation results only: the pinned 27-gate circuit is SAT with all edge proofs, requesting a missing proof from that same pinned circuit is UNSAT, and the redundant 29-gate circuit is SAT with exactly three missing edge proofs. Its saved result reports full truth-table validation with zero errors. These are encoder tests, not an unrestricted lower bound or a refutation witness. The main squarefree search was not started.

The local block archive records one SAT sanity check for the known 11-gate baseline and three UNKNOWN searches, including explicitly ordered/productive restricted runs. Its notes state that the local read-one encoder was prepared but not run. Complete stdout/stderr, input data, and text CNFs are retained. Every entry in its archive manifest matched. The global search manifests also matched: ten input/data hashes and five program hashes.

The additional code contains local file access and local solver invocations, with explicit candidate verification; no credential access or network operations were found. The two-junk bypass JSON and Lean translation keep the nonleast scope explicit. Fresh proof notes report no new checked result. The one-hot note remains a pen-and-paper obstruction to a relaxation, not a full-gap refutation.

The upstream refresh is explicitly interrupted. All 337 final statements were extracted from `2af7128d0a59a3268ff1ca486e4beb6f9d616393`, but only screening and an initial sample were assessed. No exhaustive claim of irrelevance or new usable theorem is made.

## Lease and status records

The final NOTES, TIMELINE, validation record, search stop record, and complete HTTP response consistently report that work stopped on loss of the L-meta-2583 lease. The response contains HTTP 410 and the body:

```
no such live lease: it expired or was released. Ask /desk/next again.
```

The response does not distinguish expiry from release. No stronger explanation is inferred. The complete public response headers and body are retained without credentials. Root's final validation record says the assembly build had already been launched before the failed renewal response was inspected and was not repeated after the stop.

The correct delivery status remains: durable compiled partials and research diagnostics; exact posted theorem absent; no local checker acceptance; no complete Fano counterexample; no global UNSAT result.
