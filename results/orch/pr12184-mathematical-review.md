# PR 12184 independent mathematical review

Reviewed the read-only public source saved as `/tmp/oec/pequalnp-pilot-61/PR12184_L_meta_670.lean` on 2026-11-25. This review is independent of the author's proof construction. It does not claim a complete Lean build or local-checker pass.

Verdict: PASS for the circuit-to-live-run bridge, essential-input argument, and selection of the two whole-graph root statements.

- `raw_modes` splits on whether any circuit gate is NOT. With no NOT, the ordinary AND/OR model receives the full budget 15. If at least one NOT occurs, the count of non-NOT gates is at most 14, even when that NOT is unused.
- The signed model canonicalizes each truth table by complementing it exactly when its all-zero input row is true. Complementation is then free. The exhaustive `nrm_prime` identity translates each AND/OR operation into one of AND, OR, AND-NOT, or NOT-AND on canonical representatives. This costs at most one binary operation.
- `gate_rep` covers zero-input, one-input, and two-input AND/OR gates, repeated inputs, out-of-range reads (the library's false default), and NOT gates with the library's head-input semantics. `pull_gate` removes constants, duplicate results, and unused gates without increasing the counted budget. `extract` propagates that bound through the entire circuit.
- The target graph and the nine positive input truth tables are all false at the all-zero row, so canonicalization leaves them unchanged. The target is nonconstant.
- `orbitAllInputs` uses a pair of input rows for every vertex. Each pair changes exactly that input and changes the target. Consequently, any live run whose initial signals are drawn from the positive inputs must contain all nine inputs.
- `rootS` has mask 511, mode true, and cap 14. `rootM` has mask 1535, mode false, and cap 15. Mode is determined by the negation of mask bit 10. Both masks have the same low nine bits, so both graph targets are the posted graph. `index_root` independently checks that the selected decoded root state is precisely the nine-input set.
- `parentFromModes` applies the matching root exclusion after replacing the extracted initial set with the complete input set. The final theorem supplies the posted size bound and circuit semantics directly.

An independent Python truth-table calculation checked all 512 assignments against the literal `graph` bit vector and verified all nine essential witness pairs. Full structured results are in `/tmp/oec/pequalnp-pilot-61/pr12184-math-independent.json`.

Remaining validation belongs to the Lean kernel and repository checker: every numerical forest leaf, its soundness chain, resource limits, and final single-file format must pass on the exact submitted source. Public PR provenance and author attribution must be retained.
