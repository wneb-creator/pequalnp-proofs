# Eight-input computational supplement for L-meta-4675

All scheduled runs are complete. No new proof or refutation is claimed. Previous manifests and their files remain unchanged.

| Experiment | Status |
|---|---|
| eight-input-extremal-census | ASSERTIONS_PASS |
| eight-13726-known-star | SAT |
| eight-13726-one-below-bound | UNKNOWN_TIMEOUT |
| eight-3262-known-star | SAT |
| eight-3262-one-below-bound | UNKNOWN_TIMEOUT |
| eight-3510-known-star | SAT |
| eight-3510-one-below-bound | UNKNOWN_TIMEOUT |

The3+5 census finds10944 C4-free graphs. Its540 maximum-score graphs have |E|=8,tau=3 and form two classes: C6 with two leaves at one point (mask3262) or at different points (mask3510). The4+4 census finds18521 C4-free graphs. Its96 maximum-score graphs have |E|=9,tau=4 and form one class, theta(3,3,3), mask13726. All three classes have eight active inputs and cycles. Only maximum-score classes are canonized; this is not a blanket eight-input circuit claim.

All three pinned star controls are SAT and independently replayed on all256 assignments. All three one-below-bound searches returned UNKNOWN after their300-second limits. UNKNOWN is inconclusive, not UNSAT: no witness or new lower bound resulted.

The same full-truth encoding and existence-preserving gate normalizations from the seven-input supplement are used. No dirty-AND, TopForm, minimum, edge-activity, or pivotality restriction is imposed. Sources were independently reviewed; final preservation review is separate.

Complete original stdout/stderr and exact generated solver instances are in `counterexample-eight-input-logs/`; hashes and command arguments are in `counterexample-eight-input-manifest.json`. No credentials or binaries are included.
