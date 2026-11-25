# Finite-case investigation for L-meta-2448

These are exhaustive Python computations, not Lean-checked results.

- For 4 inputs, enumerated semantic AND/OR circuit states through depth 4. All 38 labelled triangle-free, four-cycle-free graphs had a minimum witness with a star profile. State counts by depth: 13, 126, 1102, 9279.
- For 5 inputs, enumerated through depth 5. All 291 labelled forests had a minimum witness with a star profile. State counts: 21, 330, 4750, 67005, 958669.
- The remaining 12 labelled admissible 5-vertex graphs are copies of C5. Every possible extra AND/OR gate from every depth-5 state was checked; none computes a C5 edge function. Thus the computation finds no C5 circuit with at most 6 gates. Standard star-cover circuits have 7 gates.
- A separate scan of every minimum output candidate arising from the chosen canonical state witnesses found no minimum circuit lacking a star profile. This is not exhaustive over ownership profiles, because equal semantic signal sets share one circuit representative.

Method: represent each signal by its full truth table, start with all input signals, and enumerate every new binary AND/OR of available signals plus a nullary AND for true. Constant false is freely available from an out-of-range wire, but gates involving it cannot produce a new useful signal. Duplicate semantic gates and unary gates cannot improve a minimum. State keys are sets of generated truth tables; each state stores one circuit witness. This merging preserves reachability/minimum gate counts, not ownership profiles. The star check uses each gate's ancestor set and tests the literal Owns condition at each graph edge.

Structural obstruction: ownership is not automatically star for arbitrary computing circuits (an irrelevant nullary AND owns every edge). In a minimum circuit, constants, unary aliases, and dead gates should disappear. An AND owning two disjoint edges has a false positive on a singleton/nonedge among the four endpoints, as already proved inside R_meta_2448_263; the unsolved exchange must remove/move such an AND without increasing size. This finite search found no counterexample.

Artifacts stay under /tmp/oec/pequalnp-pilot-75/finite/.

search.py SHA256 a621076064c49e96f7a929fc27c799f7fafe086042defeeeaedf490345ececde

search5.py SHA256 bde2d8cf88f63496dde605b9e66f9cbcaf67970786355fbef4ae720f8d85db11

search5six.py SHA256 5496fef9b054e8417f9c8a84a93417cd7e3e8965dfee0d70617289802368f06d

nonstar5.py SHA256 232b4b122949d162eca06d834828cae5b02206adac0944e3021c867f1d7e52ac

Updated 2026-11-25T07:08:47.241942+00:00
