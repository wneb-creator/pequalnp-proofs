# Four-owner free-feature restriction: necessary kernel

`FourOwnerFreeRestriction.lean` proves `Arc.necessary_fourteen`: an 18-paid-gate circuit for the four-owner arc function, even with all 27 possible outside-row pair/triple OR features and a false constant supplied free, yields a 14-paid-gate circuit for the once-subdivided K4 kernel with three opposite-edge OR features supplied free.

This implication is necessary only. A 14-gate kernel witness does not automatically restore the four private-line terms, nor does it automatically prove L-meta-650. This research artifact uses project helpers outside the final gap's allowed imports.

The 14 raw inputs are full inputs `[0,1,2,6,13,14,16,20,21,25,15,22,23,24]`; the last four are private lines. Four sequential gate eliminations remove these in reverse order. Before each restriction, singleton free features are relabeled to their raw aliases and empty features to a false coordinate. The remaining nontrivial feature ORs permit direct raw-input dependency witnesses, so each restriction removes at least one paid gate. All normalization equations and dependency witnesses are checked in Lean.

The final kernel has raw inputs `[0,1,2,6,13,14,16,20,21,25]` and three extra inputs `[x5 ∨ x8, x4 ∨ x7, x6 ∨ x9]`, exactly matching `circuit_search/four-owner-private-zero-kernel.json`. Every remaining old feature is an alias of a raw input, one of these three ORs, or false. The constant coordinate is hardwired without increasing the 14-gate budget.

The theorem includes all 27 possible outside OR features, so it subsumes all seven generated prefix packets. Explicit maps in `four-owner-free-restriction-coverage.json` were independently checked on all 16384 raw assignments per packet, and the kernel mapping was compared exactly with the search packet.

Validation: `lake env lean .../FourOwnerFreeRestriction.lean` exited 0, with complete stdout/stderr saved in the adjacent validation log. The theorem permits arbitrary fan-in-two gates including NOT; no sorry, new axiom, native_decide, or new options occur.
