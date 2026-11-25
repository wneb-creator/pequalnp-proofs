# Counterexample search for L-meta-4675

No counterexample to the posted statement has been found. The SMT results below are external solver results, not Lean-checked lower bounds. The encoders include symmetry and normalization restrictions that have not all been formally verified; UNSAT describes the encoded search, not an unrestricted Lean lower bound. Timeouts give no infeasibility conclusion. Elapsed times are wall times measured by the drivers. The heuristic iteration counts include rejected, repeated, and unchanged mutations; they are not counts of distinct circuits.

## Lean-checked baseline components

- `lemmas/Counterexample.lean`: a four-gate nonlinear P4 circuit satisfies the gap's concrete hypotheses and attains its proposed bound. It shows that a tight circuit can have an AND output and nested clean AND gates. It is not a refutation of the gap.
- `lemmas/FanoSanity.lean`: the 21-edge Fano incidence relation is C4-free, and an explicit 27-gate AO2 circuit computes its edge function with `tCount = 0`. Computation is proved symbolically.
- `lemmas/MatchingCover.lean`: any subset of `Fin (p+p)` meeting each diagonal point/line pair has cardinality at least `p`.
- Team extensions combine these with the clean-AND and unique-edge repair bounds. They also rule out saving a gate merely by computing the Fano line-neighborhood ORs with a shared AND/OR preprocessing circuit.

## Completed finite searches

| Target | Gates | Additional constraint | Result |
|---|---:|---|---|
| P4 | 3 | `tCount = 0` | Z3 UNSAT; MILP infeasible |
| P4 | 4 | `tCount = 0` | SAT; full truth table and coloring validated |
| P4 | 4 | Some dirty AND | MILP infeasible |
| P4 | 5 | Dirty AND accepting at least two edges | SAT; full truth table and dirty witness validated |
| C6 | 7 | `tCount = 0` | Z3 UNSAT in 26.13s |
| C6 | 8 | Some dirty AND | Original Z3 encoding UNSAT in 157.60s; optimized encoding UNSAT in 9.58s |
| theta8 | 11 | `tCount = 0` | UNKNOWN after 600.09s (timeout) |
| theta8 | 12 | Some dirty AND; auxiliary normalization query | UNKNOWN after 600.04s (timeout) |
| fano55 | 15 | Dirty AND accepting at least two edges | UNKNOWN after 600.12s (timeout) |
| theta10 | 15 | Dirty AND accepting at least two edges | UNKNOWN after 600.14s (timeout) |
| fano66 | 20 | Dirty AND accepting at least two edges | UNKNOWN after 600.18s (timeout) |
| Fano | 26 | `tCount = 0` | UNKNOWN after 3,603.39s (timeout) |

The independent MILP runs for C6 were stopped once the faster Z3 encoding was validated. An early unoptimized Fano SMT run was stopped when the optimized encoding was launched. These stopped runs give no infeasibility conclusion. A five-second trial of Z3's `qfbv-sls` backend did not solve the known satisfiable P4 sanity case, so it was not allocated a long run.

## Heuristic Fano searches

- Neutral Cartesian genetic programming: 1,800.000s, 44,290,630 mutations, best circuit remained at 27 live gates. No 26-gate witness.
- Bounded guided annealing at 26 gates: 1,800.000s, 94,162,988 mutations, best weighted truth-sample error remained one. No exact witness.
- An earlier unrestricted annealer was stopped because it drifted far from the target; its source and diagnostic output were retained.

All proposed exact witnesses are independently checked on the complete Boolean truth table, with valid backward gate indices and the original syntactic color condition. The multi-dirty variant additionally checks a false target input activating the AND gate and at least two accepted target-edge inputs.

## Graph censuses

- Complete 5×5 census with 12 edges and the fixed diagonal matching: 260 labelled graphs, exactly two isomorphism classes. There are 20 theta10 instances and 240 fano55 instances.
- Complete 6×6 census with 16 edges and the fixed diagonal matching: 720 labelled graphs, all isomorphic to fano66. Every row-degree multiset is `(2,2,3,3,3,3)`. The census explicitly reported `complete: true` and finished in 0.27s.
- Independent finite checks give minimum vertex-cover sizes 5 for fano55/theta10 and 6 for fano66. Their proposed gate lower bounds are respectively 16 and 21.

## Remaining runs at this checkpoint

- Refined Fano search: 26 gates and a multi-edge dirty AND, 900s limit. PAUSED after the desk returned HTTP 410 on renewal; pending desk recovery. Complete current output is preserved in the clearly labelled `fano-k26-z3multidirty.INTERRUPTED.*` snapshots. No result has been produced.

Full completed and early-stopped logs are archived alongside this summary. `counterexample-log-manifest.json` records the source and archive paths, byte counts, and SHA256 hashes. Source programs are under `lemmas/`; active logs are preserved in the job scratch directory until their completion and archival.
