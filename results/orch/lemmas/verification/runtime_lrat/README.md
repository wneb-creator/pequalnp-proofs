Independent runtime LRAT checking for two A5 CNFs

Both archived A5 UNSAT certificates were accepted by `Std.Tactic.BVDecide.LRAT.check` under Lean 4.36.0. The runner parses the original DIMACS file, validates the declared counts and literal range, converts literals to the checker's zero-based representation, validates consecutive LRAT addition IDs, then invokes the bundled checker. Parent/root independently reviewed the runner.

`receipt.json` records exact commands, source/CNF/proof/log hashes, counts and exit codes. The proof archives are preserved separately by lean_baseline; the 338 MB uncut LRAT is not duplicated here. Tiny controls accept contradictory units and reject the same purported proof against a satisfiable duplicate-unit formula.

This is runtime evaluation of an independently implemented checker with a general Lean soundness theorem. It is not a kernel proof of either concrete checker result or a formal circuit-to-CNF completeness theorem, and it is not a full L-meta-650 refutation. No native_decide is used.
