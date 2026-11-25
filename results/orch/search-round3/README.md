# L-meta-1031 search checkpoint, round 3

This checkpoint contains an independently verified counterexample to a proposed auxiliary lower bound, not a refutation of L-meta-1031. The 8-vertex, 10-edge graph in `petersenminus01-synth.json` has no triangle or four-cycle and minimum vertex cover4. External count-only synthesis found a circuit using8 OR gates, strictly less than |E|-1=9. The initial expanded witness has15 total gates (7 AND +8 OR). Factoring two terms sharing the same AND operand yields the14-gate witness (6 AND +8 OR). Both compute the graph function on all256 assignments. Python validations and full solver stdout/stderr are preserved; these are not kernel certificates.

The14-gate witness has X=x1 OR x5, Y=x1 OR x7, Z=x5 OR x6, H=(X AND Y AND Z) OR x4. Its output is H AND (x6 OR x7), OR x0 AND X, OR x3 AND Z, OR x2 AND Y. AND ownership is cone-local. The initial AND at wire11 owns edges01,12,16,57, which have no common center; the next AND at wire12 owns no edge. Thus this nonminimum circuit has a bad ownership profile.

`counter_expand_count.py` expands charged-gate/free-cone witnesses with syntactic sharing. `counter_validate_binary.py` independently checks binary-circuit truth tables, triangle/four-cycle absence, minimum vertex cover and ancestor-based AND ownership. `counter_petersenminus01_or8_14_witness.json` is the shorter explicit gate list, output wire21. Its validation reports no errors and no short cycles.

Repository result `PEqualNP.Outside.L_meta_2036` already proves this same graph has no circuit of size12, even allowing NOT. The explicit isomorphism from this snapshot labels to that result is (0,1,5,6,3,4,2,7). The canonical star circuit has size13, so no further total-size counterexample search on this graph is justified. Our last size12/four-AND synthesis run returned UNKNOWN at180 seconds before that existing bound was discovered; it is not an independent UNSAT certificate.

The Lean-checked auxiliary counterexample is maintained separately in `../lemmas/setup_or_counter.lean`. The posted existential statement remains unresolved by this checkpoint.
