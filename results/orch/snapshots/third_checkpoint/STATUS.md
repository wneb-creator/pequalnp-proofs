This is a preservation checkpoint, not a proof of L-meta-650.

The exact target still requires a monotone circuit with at most63 gates. A64gate circuit is proved in Lean. The best current28gate six-row candidate accepts every required edge but also four extra edges, giving17 failed maximal-negative tests and255 false-positive assignments among131072 inputs. It is not a witness.

This checkpoint contains changed search sources, datasets, candidates and complete selected diagnostics. Files over500KB are gzip-compressed; MANIFEST records original and stored hashes. Earlier unchanged files remain in the first20min and second40min snapshots.

Search branches include exact core28, exact core29 plus a conditional outside-pair tap, and full-plane63 guarded merges. All candidate witness claims require independent full-basis verification. Timeouts are UNKNOWN, not global UNSAT. Bounded edit exclusions apply only to their recorded neighborhoods. Calibration outputs named BASELINE-WITNESS may exceed the target and are not target witnesses.

The large VerifierCalibration benchmark was stopped for memory; only VerifierCalibrationSmall is compiled/reviewed. The first AugmentedCandidate17 build was stopped before completion; its theorem is not yet checked. Its successful successor, if any, will be preserved separately with a review.
