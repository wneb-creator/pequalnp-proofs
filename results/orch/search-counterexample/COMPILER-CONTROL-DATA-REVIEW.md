# Independent compiler-control data review

The frozen Lean program contains exactly the 51 operations, 103 conjunction-reference lists, and final output references in `theta4-control-global51-compact.json`. Its 51 supplied OR masks and final result match `theta4-control-global51-masks.json`; the 26 input-mask literals match the same export. The literal Program syntax was parsed independently of its generator, and only nested tuples/lists and explicit `Fin` references occur.

The sample-data file defines masks; it does not by itself prove their interpretation. The supplied-mask certificate checks the 51 operations against those masks. The separate sample-bit benchmark proves all 52×26 positive input bits and only coordinate 0 across the 468 negative rows. The remaining 25 negative coordinates are still pending in this snapshot.

This is a 51-OR integration control, not a counterexample or a proof of the posted 51-OR lower bound. Exact source hashes and the complete comparison output are in `compiler-control-data-audit.json` and `.log`.
