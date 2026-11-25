These are computational search artifacts, not Lean proofs.

The selector model permits arbitrary free OR and counts AND gates. Core normalization uses L_meta_563; details are in ../counterexample.md. CNFs are stored compressed with complete metadata. Solver stdout/stderr logs are copied only after a run finishes.

Known outcomes: fooling-size4 with3ANDs UNSAT;4ANDs SAT and all256 inputs independently checked. Fooling-size5 with4ANDs UNKNOWN after60s. Plane12 baseline and row-cut variants UNKNOWN after600s each. Ordered fooling5/4 and flag-anchored plane12 also ended UNKNOWN after600s. All runs are finished; all complete solver logs are preserved. Original scratch CNFs were removed only after a successful SHA256 comparison with the decompressed archive; hashes are recorded in cnf-hashes.json.

The fixed new point-gadget placement (central0, short1/4/6/2) is UNSAT for cross-side code extension in0.44s with width4/pair cuts, and in0.34s with width12/no-pair-cuts. These are not circuits or Lean proofs. Complete solver logs, resource reports, compressed CNFs, and SHA256 records are preserved.
