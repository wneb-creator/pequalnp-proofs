# Counterexample searches for L-meta-1896

This directory preserves small local counterexample searches and their complete logs. No counterexample or proof of the posted statement has been found. `unknown` means the stated wall-clock limit elapsed and establishes no impossibility.

`or_cover_cadical.py` is the strongest exact finite encoding. It uses Z3 5.3.3 only to construct and bit-blast the formula, then invokes the CaDiCaL bundled with Lean 4.36.0. The earlier scripts use Z3 directly. The scripts currently name the original task-scratch paths; adjust those paths when replaying elsewhere. Z3 was fetched from its public GitHub release at `https://github.com/Z3Prover/z3/releases/tag/z3-5.3.3`; no authentication data is part of these artifacts.

The model counts OR gates and permits arbitrary free ANDs. Every AND operand is canonically replaced by the conjunction of all available wires whose positive signatures contain the operand's signature. This preserves required positive behavior and can only remove unwanted negative outputs. An OR with a positive-signature-dominated branch can be removed, so both branches are required to contribute a positive sample.

The prefix cover cuts are necessary conditions: at a fixed negative sample, conjunctions cannot enlarge any available false wire's positive support. A new false OR wire has positive support covered by two earlier false wires. It can therefore lower the minimum number of false wires covering all required positives by at most one. A successful final conjunction requires that minimum to become one. Accordingly, after a prefix, a cover by current false wires of size at most one plus the number of future false OR gates must exist.

The first-OR orbit restriction for theta3 is independently checked against all twelve graph automorphisms and all thirteen projected generic negative maxima. It reduces 118 incomparable pairs of initial AND operands to eighteen representatives.

For CaDiCaL runs, the original SMT formula, DIMACS, named signature-bit mapping, solver command, complete solver output, and any model are preserved. Any reported SAT witness is reconstructed from the named bits and independently simulated on every encoded sample. Known satisfiable C4 and theta3 controls pass with all cover cuts.

Tiny UNSAT controls are results of the finite encoding, not Lean-checked proofs. All artifacts have hashes in `SHA256SUMS`; regenerate that file after adding later runs.
