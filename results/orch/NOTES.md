# Pilot 109 shared findings

Gap: L-meta-2592. Only root holds and renews lease. Target: Petersen graph Boolean edge function requires more than 19 fan-in-two gates if a NOT occurs. Three reductions are live.

Each strategy owns one note file in results/orch/lemmas; root consolidates here. No subagent git mutations or desk requests.

## 14:07 UTC consolidation

- Assigned statement permits any positive number of NOT gates, including unused gates. There is no malformed-wire shortcut: invalid reads are false.
- Checked existing proof L_meta_4725 establishes `15 + NotBracket.notCount C ≤ C.size`; a counterexample of size at most 19 has 1–4 NOTs. Porting this proof gives checked partial coverage of ≥5 NOTs.
- Standard Petersen star-cover construction has 20 gates. This is an upper bound; the monotone 19-gate exclusion is itself still open. Do not assume a proved 20-gate lower bound.
- Existing active reductions: R_meta_2592_271 (binary floor plus few-NOT exclusion), _318 (last-NOT decomposition plus monotone separator bound), _408 (normalization plus finite normalized exclusion). Three live reductions block an additional reduction.
- Open descendant bounds: L_meta_4727, L_meta_7391, L_meta_8297, L_meta_6062, L_meta_7229. Existing L_meta_8295 proves the last-NOT split; L_meta_7389 proves wire normalization. No solved-leaf assembly closes this step.
- Counterexample searches: Z3 19-gate CEGIS, initially exactly one NOT, and C++ simulated annealing seeded from 20-gate star-cover formulas. UNSAT on heuristic restrictions is not a proof of the target.
- Environment repair: official Lean 4.36.0 installed in task scratch; all 9,117 pinned Mathlib cache artifacts fetched. Defs build underway.
- Delivery: archive full outputs in branch history; final proof PR, if obtained, must have net addition of exactly the named Lean file.

## First strategy replan

- Named module `lake build +PEqualNP.Outside.L_meta_2592` passed. The file is a checked partial and has no posted target theorem. Local checker rejected it with REJECTED (no-theorem).
- Four preservation pushes succeeded through commit 6d45333ba120885d59cd055befe13decc31d6444. Every pushed diff had independent review.
- The near-circuit now differs on four assignments, all false positives; it is NOT a counterexample. Local two-gate repair was UNSAT in both SAT and exhaustive search. Restricted fixed-star architectures also returned UNSAT; none is a proof of the general claim.
- Keep broad searches for one, two and three NOTs; stop superseded slower encodings after their bounds expire. The four-NOT case is handled separately as fifteen binary nodes with bounded complemented wires.
- Four-NOT equality in a Least normalized circuit: all branch wires must have a first-input ancestor; a unary NOT cannot create such an ancestor after a branching source. New formalizations in progress connect this to stronger signed-circuit topology constraints.
- A new global route builds ABC from official GitHub source, synthesizes the full truth table, and optimizes node storage phases to count actual AND/OR/NOT gates. Every candidate must pass all 1024 inputs independently.
- No full proof or refutation. Three existing live reductions still block an additional reduction. Continue current lease only.
