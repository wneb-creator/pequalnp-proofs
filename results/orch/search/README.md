# Computational diagnostics for L-meta-2583

These are exploratory computations, not Lean proofs of the posted statement or its negation. No counterexample has been found. An UNSAT result below is an unverified solver diagnostic, not a kernel-checked certificate.

## Fano target and encoding

The seven point-line neighborhoods are `{l,l+1,l+3}` modulo 7. Inputs 0 through 6 are points; inputs 7 through 13 are lines. The exact monotone target is characterized by its 21 positive edge-pair assignments and 37 maximal independent sets. A complete Python truth-table check covers all 16,384 assignments.

`counterexample_sat_nofirst.py --gates 26 --out fano26-full.cnf` regenerates the corrected encoding: 5,928 variables and 164,819 clauses. Each gate is AND or OR with two distinct earlier operands. All gates feed the final output, and right-operand indices are nondecreasing. These restrictions preserve the existence of a circuit of at most 26 gates by redundancy elimination, topological reordering, and absorption padding. No read-1 condition is imposed.

Independent audit corrected a symmetry error in the historical `counterexample_sat.py`: forcing the first nonincident pair `(0,8)` can conflict with right-operand ordering. The corrected generator removes all first-pair restrictions. Its SHA-256 is `5a0c17171f2b07a2a303ae1e6db8a82927a183a86bba4d16b3e33a052f035f2c`. The old search remains a sound search for witnesses but is not complete. No UNSAT conclusion was drawn from it.

`counterexample_sat_validate.py` validates the known 27-gate star circuit against every one of 175,949 CNF clauses and all 16,384 truth-table inputs. `known-27-gate-witness.json` is that positive control, not a counterexample.

## Completed initial searches

- CaDiCaL 3.1.0: `cadical -t 600 fano26.cnf`. Result UNKNOWN after 600.02 real seconds, 446.10 CPU seconds, 5,985,100 conflicts. Complete output: `fano26-sat.log`. This used the historical restricted encoding.
- Fano stochastic walk: `python3 counterexample_walk.py --seconds 600 --seed 76`. Evaluated 33,823,394 mutations over 2,254 restarts. Best circuit differed on 36 full truth-table assignments, consistent with a missing edge. Complete output: `fano26-walk.log`.
- C6 diagnostic: `python3 counterexample_c6.py --gates 8 --out c6-8-nonread1-full.cnf`, then `cadical -t 120 c6-8-nonread1-full.cnf`. The encoding additionally requires edge `(0,1)` to have no read-1 proof tree. All six positive pairs and five maximal independent sets are enforced. With no first-pair symmetry restriction, solver result UNSAT in 23.42 real seconds and 7.23 CPU seconds. This does not establish a Lean theorem. `c6-8-nonread1.log` is an earlier, more restricted run; `c6-8-nonread1-full.log` is the corrected diagnostic.

The C6 diagnostic excludes repeated operands. This exclusion is justified for a least-size circuit because repeated-operand gates are redundant, but removing such a gate can change the read-1 property. Without a separately established eight-gate lower bound, read the result only as UNSAT for the encoded distinct-operand class.

## Structured repair and larger-case walk

`counterexample_repair.cpp` uses incremental CaDiCaL, loading `fano26.cnf`, `fano26.seed`, and `fano26.phases`. A deterministic seed-76 shuffle frees 8 through 16 gate positions per trial; all other operations and operands are fixed by assumptions. Each solve has a 20,000-conflict cap, and the entire run has a 600-second wall-clock cap. The archived first repair run uses the historical restricted base and is only a heuristic neighborhood search. Future runs should use `fano26-full.cnf`, whose variable numbering is identical. The phases and seed do not contain credentials.

The order-3 plane has neighborhoods `{l,l+1,l+3,l+9}` modulo 13, 26 inputs, 52 positive edge pairs, and 704 maximal independent sets. Its star circuit has 64 gates. The 63-gate walk targets a possible improvement. The ordinary walk optimizes boundary mismatches; the positive-priority walk weights each missing positive edge by 1,000, above all possible 704 false-positive boundaries. Commands use 600 seconds and seeds 76 and 77 respectively. These walks are weak diagnostics and are not exhaustive searches.

`snapshot.json` records when the log copies were taken and which runs were ongoing. `source-hashes.json` hashes the archived programs. CNFs, solver binaries, third-party source code, and large build artifacts are deliberately omitted; instances are reproducible from the programs.

## Results of the first repair and order-3 walks

The first Fano repair finished 600 seconds with 294 neighborhoods: 167 UNSAT and 127 UNKNOWN, no witness. These counts do not exhaust all circuits. The ordinary order-3 walk ended at one incorrect boundary pattern, the trivial missing-edge obstruction. The positive-priority order-3 walk ran 600 seconds and 44,851,315 mutations; its best candidate accepted all 52 edges but also 197 maximal independent sets. The walks are not being extended because this diagnostic has weak calibration.

## Smaller structural counterexample

`counterexample_c5.py --gates 7` found a five-cycle circuit with seven gates that is not read-1 on edge `(0,1)`. Its Boolean formula is

`x4 AND (x0 OR x3) OR ((x1 OR x3) AND (x2 OR (x0 AND x1)))`.

All 32 assignments and the missing read-1 tree were checked independently in Python. `c5-7-nonread1-witness.json` gives the circuit. The file `../lemmas/counterexample_c5.lean` additionally kernel-checks its exact truth function, size, AO2 condition, prime pair, and failure of read-1. It does not prove minimality. This is not a counterexample to L-meta-2583: the five-cycle is not a projective-plane incidence graph and is not bipartite.

The mixed OR gate in this circuit reads a wire below the edge function and a wire not below it. `counterexample_c5_normal.py` imposes the stronger normalization considered by another strategy: OR operands have the same below-function status, neither AND operand is below the function, and every gate is true on an edge pair. Under these additional constraints the seven-gate diagnostic is UNSAT. Therefore this small counterexample does not invalidate that normalized route.

The analogous C8 eleven-gate non-read-1 diagnostic ended UNKNOWN at 120 seconds. All solver results in this section remain computational diagnostics; only the explicitly named Lean component has been kernel-checked.

## Structured order-3 repair

`counterexample_q3_repair.py` replaces the unstructured walks with SAT and counterexample-guided refinement. It chooses four, five or six lines from the lowest-concurrency quarter of line subsets, places their stars last, deletes one OR gate in a chosen star, and frees the connected cone consisting of those stars, their downstream OR tail, and one preceding OR. This gives exactly 20, 25 or 30 free gate positions. All other gates are encoded directly. Free gates can use either AND or OR and any two earlier wires, including repeated operands. There is no first-pair or global operand-order restriction.

Each query always enforces all 52 positive edge pairs and initially about 40 negative maximal-independent patterns. Any SAT candidate is independently evaluated on all 756 boundary patterns; up to 24 newly violated negative patterns are added per refinement. A zero-error candidate would be saved as `witness.json`. Per-query limits are 15 seconds and 150,000 conflicts; each neighborhood has at most six refinement rounds, and the overall run has a 600-second cap with seed 76. Every neighborhood and round records its exact seed circuit, free positions, patterns, solver status, and complete solver log.

Before this search, the known 64-gate star witness passed all 6,757,597 clauses of a 30-free-gate calibration instance with 97,957 variables and all 756 patterns. The program also checks the plane axioms and all 8,192 point-subset closure cases, verifying coverage of all independent inputs by the 704 maximal independent sets. `q3-64-calibration.json` and `q3-repair-calibration.log` preserve this control. The large calibration CNF is not retained.

## Corrected Fano repair and normalized non-read-1 diagnostic

The corrected-base repair completed 600.026 seconds over 512 neighborhoods: 285 UNSAT and 227 UNKNOWN, no witness. Full output is `fano26-full-repair.log`. This remains a restricted neighborhood search, not an exhaustive lower-bound certificate.

`counterexample_charge_probe.py` builds a 32-gate Fano circuit by replacing point input 0 in the known 27-gate star by `(x0 OR x1) AND (x0 OR x2) AND (x0 OR x4)`. The triple `{1,2,4}` is a line not through 0. All 16,384 truth-table assignments agree with the Fano function; all gates are pair-useful and satisfy the proposed strong OR/AND normalization. Exactly the three edges through point 0 lack read-1 trees. This circuit has three uncovered star edges, no centreless tops, two junk AND gates, and six non-top-closure OR gates, so the candidate weighted inequality holds as 12 <= 24. These are Python diagnostics only; no Lean verification or minimality claim is made for this 32-gate circuit. Full circuit and counts are in `fano32-charge-probe.json`.

## Prepared next-phase search programs

`counterexample_phase_solve.cpp` supplies CaDiCaL phase hints from a complete seed assignment. `counterexample_q3_seeded.py` adds these hints, pair usefulness, OR-operand positive-support incomparability, and the requirement that all gates be used. `counterexample_q3_singleton.py` additionally evaluates all 26 singleton inputs and requires each gate accepting singleton v to accept a positive edge away from v. The last condition excludes gates replaceable by input v without changing any positive edge pair. The lower-bound strategy has separately Lean-checked these two minimality necessities. These programs were prepared at 09:38 UTC but have not yet run; their presence does not imply successful calibration or a search result. The next intended run first uses --solver-calibrate on a known 64-gate witness.

The initial connected-cone order-3 run has completed: 41 neighborhoods in 601.4005703920002 seconds, all solver queries UNKNOWN. No SAT candidate was obtained, so no CEGAR refinement occurred. `q3-repair-run.log` and `q3-repair/` preserve the complete logs and exact per-query circuit/position/pattern seeds. The large current CNF was deleted after the completed run and is reproducible.

## Actual phased solver calibration

At 09:43 UTC, `counterexample_q3_singleton.py --solver-calibrate` passed: CaDiCaL with phase hints found SAT in 0.563 seconds on 21,145 variables and 911,367 clauses with 20 free gates. The decoded 64-gate circuit independently passed all 756 boundary inputs with zero errors. Full solver output and circuit are preserved under `q3-seeded-control/`. This is an actual solver positive control including all added minimality constraints.

`counterexample_q3_adaptive.py` starts refinement with only the two monochromatic maximal independent sets and the 26 singleton rows needed for the singleton-away cut. Each successful but incorrect candidate adds up to eight violated maximal independent sets; a neighborhood permits up to 24 rounds. The planned cap is 600 seconds, with 30 seconds and 500,000 conflicts per query, seed76. Like all fixed-cone searches here it is heuristic. In particular, adding leastness constraints at exactly63 gates does not justify coverage of every smaller circuit by padding.

Additional tiny boundary probes show normal non-read-1 circuits satisfying both OR incomparability and singleton-away: a 30-gate Fano circuit and a 67-gate order-3 circuit. Their candidate weighted charges still hold (12 <= 18 and30 <=36 respectively). These only demonstrate that the local cuts do not individually imply read-1; no minimality or new gap result is claimed.

## First adaptive run completed

The phase-guided adaptive order-3 run completed 601.0239543389998 seconds over 17 neighborhoods: 38 solver queries, 22 SAT and 16 UNKNOWN, no exact witness. The best candidate still accepted 140 maximal independent inputs. All candidates accepted every positive edge. Full logs and exact query data are under `q3-adaptive/`; `q3-adaptive-summary.json` records counts. In the first SAT candidate, 17 raw gate tuples changed, but 15 changes were only operand swapping; the two functional changes introduced six false cross pairs.

`counterexample_q3_minimal.py` prepares a finer refinement: carry each preceding SAT circuit as the next phase seed and add one inclusion-minimal false input per round. `counterexample_q3_nonread1.py` additionally tracks three exact read-1 statuses for one positive pair and requires the output pair status false. The pair is the edge missing from the original deletion seed and remains fixed within a neighborhood. This further restricts the heuristic search. `nonread1_encoding_c5_calibration.py` validated all 4,128 clauses of this tracking against the already Lean-checked seven-gate C5 non-read-1 witness. No run result for the newly prepared targeted search is claimed yet.

The targeted non-read-1 solver positive control passed at 09:55 UTC: SAT in 0.737 seconds on 68,140 variables and 938,243 clauses. The decoded known67-gate q3 circuit passed all756 boundary patterns and had no read-1 tree on the forced pair (0,13). Full control logs and witness are under `q3-nonread1-control/`. The next600-second targeted search uses seed76 and30-second/500,000-conflict queries.

## First targeted non-read-1 run completed

The 600-second targeted search completed 601.1693619170001 seconds: 64 queries, 55 SAT and 9 UNKNOWN, no exact witness. Best false maximal-independent count was 266. Minimal false cuts had sizes {"2": 53, "3": 2}. Exact program, fullstdout and per-query seeds/models are retained. The one-pair encoding and phase-carry/minimal-cut logic passed independent read-only audit.

The prepared concurrent-family driver starts from a known exact66-gate non-read-1 circuit, using g=(x0 OR xp) AND (x0 OR yT), replacing x0 byg and omittingp fromTstar. It deletes three star OR gates and frees20 positions comprising the mixedcore, four concurrent lines through0, and downstreamORs. It initially includes the16 punctured double-star maximal-independent patterns attached to those four lines; all52 such patterns get priority in refinement. Every fourth cut uses a full maximal-independent pattern, other cuts are minimized. This is a distinct restricted heuristic; no result from the prepared next run is claimed yet.

The actual concurrent66 positive control passed at10:05 UTC: SAT in0.678seconds on20,532variables/916,864clauses,23 freegates, the same16 geometricinitialnegatives, and requirednonread1 pair. Thedecoded66-gate circuit independentlypassed all756boundaryinputs andfailedread1 onforcedpair(0,23). Fullcontroloutput is retained. A600-second concurrent63 run nowusesseed76,30-second/500,000-conflict querycaps andmaximal-period4; itsactivelogs remaininscratchuntilcompletion.

## Concurrent search and prepared incremental driver

The concurrent-family run with16 initial geometric punctures completed 602.2049752370003 seconds and 21 queries, all UNKNOWN. No witness was found. Full logs and query data are archived under `q3-concurrent/`.

The prepared incremental driver retains one CaDiCaL process per neighborhood, adds fresh truth-table rows without changing old selector IDs, freezes selectors/operations/truth, and retains learned clauses. It clears streamed Python clause buffers to reduce memory. Four point0-centered punctures are the default initial geometry; all52 punctures receive priority during refinement, and every fourth cut remains maximal. Two additional solves are allowed after an UNKNOWN result. Full solver stdout/stderr is logged per trial, with per-query offsets. Models are explicitly labeled OEC_MODEL_FROZEN_ONLY and report exactly the circuit choices needed for decoding; omitted auxiliary truth values are recomputed independently from the decoded circuit. The driver/server and this output convention passed independent audit.

The prepared global-shape wrapper frees all operands while fixing the operation at every gate position. Its63-gate seed has14 AND and49 OR gates, but its scope is this fixed operation sequence, not every circuit with those counts. It is not yet a completed search.

The actual incremental66 control passed at10:16 UTC in0.447seconds total: initial SAT with zero756-boundary errors; add a fresh negative input row and SAT again with zero errors; then add a contradictory truth unit and obtainUNSAT. All new-row clauses were additionally evaluated against the known complete semantic assignment before submission. Full protocol output and modelspans are in `q3-incremental-control/`.

## Incremental local search completed

The local incremental run completed 600.430869931999 seconds over 7 neighborhoods and 21 queries. All queries were UNKNOWN despite retaining learned clauses and allowing90 seconds per neighborhood. It used4 initial centered punctures. Full protocol logs and exact query data are under `q3-incremental/`.

The prepared global mixed-family wrapper alternates the66-gate distributed core minus3 ORs with a65-gate direct core minus2 ORs. The latter uses g=x0 OR (xp AND yT), omits p fromTstar, and forces the hidden edge(p,T) to lack read1. Both63-gate families have14 AND/49 OR gates at fixed operation positions; all operands are free. The65 control is intentionally not in the strong mixed-OR normal form, which is not an encoded condition. Both positive controls are run before the global search.

Both actual global fixed-sequence controls passed:66 gates in0.665seconds and65 gates in0.953seconds. Each protocol returned SAT, SAT after another negative row, and UNSAT after a contradictory truth unit; both decoded SAT circuits passed all756 boundary inputs and their forced non-read-1 condition. Their initial CNFs had about1.7million clauses. The authorized global63 search alternates these two families, frees every operand, fixes each operation position, starts with only monochromatic/singleton negatives, prioritizes geometric punctures and uses a full maximal cut every2 refinements. Its cap is600seconds with seed76,30-second queries and2 UNKNOWN retries.
