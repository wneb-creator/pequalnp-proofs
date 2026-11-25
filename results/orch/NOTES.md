# pequalnp-pilot-64 — L-meta-2602

Lease is held and renewed only by the root agent. No other desk requests.

Exact statement: /tmp/oec/pequalnp-pilot-64/statement.txt
Desk metadata: /tmp/oec/pequalnp-pilot-64/desk-next-1.json

Goal: exclude 63–64 gate AND/OR circuits for the order-3 incidence graph whose formal derivatives in both directions of edge (0,0) vanish. Three reductions already live, so prioritize full proof or checked refutation.

All helper declarations must be inside the module namespace; final theorem fully qualified at top level, last. No strings, _root_, commands, new axioms, or native evaluation.

Agents append findings below; use distinct scratch lemma filenames. Root owns final Outside file and git operations.

## Structural attempt

- Double vanishing cannot be excluded semantically alone: separate gates g=xy, h=xy, then g AND h compute xy but both singleton derivatives vanish. Distinct input wire indices do not forbid this.
- Exact general lower bound for unrestricted monotone circuits of a C4-free graph is not an immediate biclique-cover argument; nested AND gates permit cancellation of unwanted monomials by absorption.
- Existing reduction R_meta_2602_2 separates a 56-gate bound on the endpoint-deleted face from a path theorem. R_meta_2602_926 has reusable evaluation, derivative-trace, and collision induction proofs. R_meta_2602_415 separates a generic monotonic guard lemma and a hard face/cut statement.
- Added unverified geometric helper candidate results/orch/lemmas/Structural.lean: degree 4, 52 incidences, 45 after deleting endpoints, no rectangle, diagonal matching. Awaiting toolchain for Lean checking.

## Existing reductions and checked descendants (reductions agent)

- `R_meta_2602_2`: exact goal follows from a 56-gate lower bound on the face with point 0 and line 0 false, plus a path theorem saying enough fresh gates on every incidence face force a singleton-sensitized path from one endpoint to output. Its proof provides a general face compression construction and sensitized-path derivative propagation.
- `R_meta_2602_415`: splits off an elementary monotonicity/guard fact; the other hypothesis is a 63–64-gate cut obstruction using fixed independent-set masks. No checked proof of that obstruction found.
- `R_meta_2602_926`: 4 cases on AND gates blocking the two derivative directions. This is a partition of the remaining hard obstruction; no completed descendant identified.
- Parent `R_meta_1482_3` would reduce our problem to unconditional size ≥64, no junk AND in a least circuit, and no nested AND when junk is absent. The third is checked in `L_meta_2393`; the first two remain core obstacles.
- `L_meta_2067` proves a derivative is true when `andPairs = 0`. `L_meta_2069` proves one directional derivative true if every AND gate is below the output function.
- Checked lower bounds `L_meta_4803`, `L_meta_1751`, `L_meta_2059`, `L_meta_5158` require no nested AND / `andPairs = 0`; they do not establish the unconditional bound.
- `L_meta_1961` gives shrinking with at most one nested AND pair and size <64. `L_meta_3799` gives shrinking when every AND has at least two readers, again size <64. They do not cover the critical 64-gate case.

All these Outside proofs would need inlining: the allowed project import is only `PEqualNP.Defs`, which gathers definitions rather than these results.

## Independent audit 2026-11-25T03:09:20.084655+00:00

- The posted gate condition enforces both operations and strictly earlier inputs, so derivative witnesses are unique on all real wires. A draft general proof is in `results/orch/lemmas/Audit.lean`, with wire length and output range lemmas; awaiting restored cache to compile.
- No direct semantic contradiction from two vanished derivatives: the 3-gate circuit a=x AND y, b=a OR z, c=a AND b computes xy with both derivatives zero at the singleton bases, despite distinct operand wires. Thus the size condition and global incidence structure are essential.
- Current repository format adds helper namespace discipline: all helper declarations under the module namespace, final theorem fully qualified at top level and last.

## Derivative route

- Both existential traces are exactly linear coefficients on the edge (0,13); no semantic/index loophole.
- Generic two-gate wrapper: A=C.output OR z; output=C.output AND A. It preserves the Boolean function and adds exactly two gates. If C and z reject both singleton base inputs, both derivative outputs become false. Thus a <=62-gate incidence circuit gives a target counterexample after padding.
- Distinct collision gates do not force three AND gates: x AND y; previous OR z; first AND second has 2 AND gates and both derivatives vanish.
- Draft generic wrapper lemmas: results/orch/lemmas/Derivatives.lean. Uses only PEqualNP.Defs.ReadK; awaits toolchain/cache validation.

## Counterexample audit and finite tests

The exact statement has no immediate output-index or trace-freedom loophole: output is forced valid by accepting input {0,13}; valid wire traces are unique. Ordinary star circuits do not satisfy either vanished derivative.

Exhaustively enumerated the 8192 point subsets and their forced line covers for the order-3 incidence graph. Minimum vertex cover is 13 with exactly two minimizers (all points; all lines). Thus a minimum ordinary edge partition into stars uses one entire side; all its edge derivatives are nonzero. The same two-minimizer result holds for orders 1 and 2. This does not prove a lower bound for general circuits.

Exact BFS through reachable truth-table/derivative signatures with distinct earlier input wires found minimum sizes for a vanished derivative pair at xy: xy = 3; x(y OR z) = 4; x(y OR z OR w) = 5; xy OR yz OR zw = 5; xy OR zw = 4; 4-cycle = 5; triangle = 5. In particular a universal +2 reread penalty is false: (z OR xy) AND (w OR xy) computes xy OR zw using only 4 gates and repeats both x and y. Full program and output: /tmp/oec/pequalnp-pilot-64/counterexample_search.py and counterexample-search.log.

A full-plane stochastic search is running for 20 minutes from star64 and double-read66 circuits with two gates removed, with exact monotone equivalence tested on all 52 minimal true assignments and every maximal independent set. Program /tmp/oec/pequalnp-pilot-64/plane_local_search.py; live best plane-best-64.json; complete output plane-search-64.log. No counterexample yet.

- Research checked 2026-11-25: Jukna, Disproving the Single Level Conjecture, https://eccc.weizmann.ac.il/report/2005/021/download/ . General quadratic circuits cannot be flattened without cost: linear circuits versus nearly quadratic one-AND-level circuits exist. This does not itself settle the C4-free/order-3 case, but rules out using a universal flattening assertion.

Independent audit update 2026-11-25T03:15:27.411594+00:00: `Audit.lean` compiled via `lake env lean` exit0. Derivative witnesses agree on every real wire under fixed initial values and topological recurrences; any circuit accepting some input has its output in range. Full logs are scratch `audit-build-3.stdout.txt` and `.stderr.txt` (both empty).
