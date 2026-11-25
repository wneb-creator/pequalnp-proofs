# Independent review of ReaderBound

Verdict: PASS for the current corrected conditional contraction helper and preservation. This is not a proof of the posted L-meta-1884 statement.

Current reviewed source: `lemmas/ReaderBound.lean`,179 lines,12198 bytes. SHA256: `252337b6833eadddc4165cd6dbac32f87de9a9e746c70c4e7009d45251839715`.

Correction to the initial review: the earlier181-line source, hash `539e05e920c9a187680a12f748528d879407aaf7b65f562cabff493b8e0c533d`, set heartbeat and recursion limits globally. CONTRIBUTING requires each such limit to be scoped with `in` directly above its declaration, so the earlier format PASS was incorrect. The author removed exactly those two option lines and rechecked the helper. The current source has no options; the mathematical argument is unchanged.

The final `main` theorem explicitly assumes the sixteen-gate lower bound for all actual nine-input Monotone2 circuits computing `p9`. It concludes `16 + C.gates.countP r0 ≤ C.size` only for a Monotone2 circuit computing the exact Petersen function on the ten identity inputs plus the free negation of input0. It does not claim the result for arbitrary internal NOT gates, and it does not exclude all eighteen-gate circuits.

The contraction fixes primary input0 to false and supplied input10 to true. The symbol list preserves the original eleven-wire indexing, while the reduced circuit has nine primary inputs and a separate gate index counter. Constants are tracked separately from circuit wires. Every gate counted by `r0` reads one of those fixed primary positions and therefore produces no reduced gate; additional constant simplifications may remove more gates. The invariant bounds every live reduced reference by its current wire count, and its default-false cases cover forward or invalid original references. The final constant-output branch is correctly excluded using the all-false and all-true inputs of p9.

The finite `iso` identity supplies an explicit nine-variable reindexing of the x0=false Petersen cofactor. Its twelve edges match the intended graph. `r0` counts reader gates, not individual read occurrences, and for the Monotone2 theorem its unused NOT truncation branch has no effect.

Only `PEqualNP.Defs` is imported. The current source uses the correct target helper namespace and contains no additional axiom, sorry, native_decide, string literal, forbidden root qualifier, attribute, or option. No credentials or binary content appear. The initial version compiled/exported in session30354, exit0, with complete empty logs `/tmp/oec/pequalnp-pilot-103/1884-reader-third.stdout` and `.stderr`. The author also reported successful rechecking after the two option lines were removed. The independent reviewer inspected the source and exact current hash without rerunning a heavy test.

The concrete nine-input premise is separately supplied by the newly checked `NineCircuitFloor.lean` plus the elementary equality of its `edge` and this file's `p9`; that final integration is a separate check and is not assumed in this review of the conditional source.
