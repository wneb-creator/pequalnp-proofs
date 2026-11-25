# Fano single-core SAT search

Encoder: `/tmp/oec/pequalnp-pilot-71/structural/fano_sat.py`. Independent decoder: `decode_sat.py` in the same folder. CaDiCaL at the installed Lean toolchain bin/cadical; documented `-t 300` wall limit used. All stdout/stderr and witness outputs saved under structural/.

Encoding: 14 Fano inputs, AO2 choices with commutative operand ordering, all nonroot gates used later, root AND, root false on all 37 maximal independent sets, root accepted-edge cardinality, exact READ1 singleton/pair recurrence, one accepted edge lacking READ1, one root operand true on some maximal independent set. For fixed support, every listed input is used and no other input is allowed. Exact support of size equal to number of gates yields one repeated wire; explicit onehot repeated-wire and fanout-at-most-two clauses strengthen this.

Target: selected residual vertex cover Y satisfies all unaccepted edges. For g gates, q accepted edges, require q+7 > g+1+card Y. Encoded as cardinality q+(14-card Y)>=g+9. This is the exact target violation for one maximal core with the whole circuit as its cone. Appending an independent canonical exact graph circuit supplies a lift-fixed output without altering the dead core.

Validation: positive calibration (4-gate P4 core, no violation requirement) returned SAT; decoded circuit checked against every CNF clause and independent full truth-table evaluator.py.

Finished so far:
- S2975={0,1,2,3,4,7,8,9,11}, g9, accept all10 induced edges: UNSAT exit20,75.96sec.
- S959={0,1,2,3,4,5,7,8,9}, g9, accept>=9 with exact target: UNSAT exit20,48.88sec.

Ongoing: S1951,S1967,S1979,S2975 general9-edge-or-more target cases. A separate initial S2975 run forced repeated edge(0,7); it is only a restricted test because fixed-support stabilizers are not edge-transitive. The replacement S2975 uses an existential repeated edge and includes the fanout strengthening.

No SAT result is being described as a Lean theorem. UNSAT outcomes are computational search evidence only.

Further completed: S1951 UNSAT154.08sec (minimum8, therefore covers all necessaryq>=9); S1967 UNSAT50.08sec; S1979 UNSAT58.59sec. Initial biasedS2975 timedout300sec, no verdict.

Remaining S2975 has10inducededges. Caseacceptall10 alreadyUNSAT; exactly9accepted can be split by omitted-edge orbit. Representatives(0,7),(0,11),(1,7). Short-edge omission(1,7) UNSAT38.48sec; outer/inner stillrunning. General existential-repeatS2975 also running.

All five necessary support orbits for a 9-gate single-core Fano violation now returned UNSAT. General S2975 finished187.05seconds; its omitted outer/inner splits also returnedUNSAT53.70/43.42seconds. Summary with CNF hashes: structural/fano-sat-summary.json. This is a complete computational search under the independently enumerated support/orbit reductions, NOT a Lean proof.

Important search-direction update: every one-edge omission from S2975 raises residual tau from4to5. Thus a 10-gate/9-input violation must accept the full induced graph on each relevant support. For genuine higher-support flexibility with two extra fanout uses, next promising case is11gates/10inputs on S3007 (12inducededges).

Ten-gate phase: original9-input casesS959/S1951/S2975 eachtimedout300seconds; ordered-onlyS959 also timedout. First11gate/10inputS3007 timedout300seconds. No verdict inferred from any timeout.

Stronger search encoder now optionally orders gates lexicographically by(maxinput,mininput,op), projects truthrows to exactsupport and removes dominated projected independentsets, and adds minimal accepted-edge patterns determined by exact residual-cover computations. Every residual cover computation constructs a matching and an equally sized vertex cover and checks both certificates. The projected/ordered positive calibration passed and its fulltruth-table evaluator agreed.

Full10-input orbit queue started with workerlimit1, now2 afterolder jobsfinished; totalconcurrent solversneverexceeds5. ControlS3007 (10gates/10inputs) UNSAT49.07seconds. Queue logs:structural/sat-control-queue.log; control summary:structural/sat-control-summary.json.

All12 ten-input support controls returnedUNSAT (3–49seconds percase). Results:structural/sat-control-summary.json. Three10gate/9input cases remain unresolved; earlier runs timedout, currentfinal pattern-pruned runs ongoing.

The generic fanout budget is r=g-m+1 extra operand arcs beyond one per used nonroot wire. New optional forward-threshold encoding limits their sum to r; independently reviewed and validated on a pinned6gate/5input positive core with one input readthree times. FullCNF and independenttruth-table checks pass. After parentrenewal06:50:18(expiry07:10:18), launched budget-pruned g11/S3007 and g10/S2975, each300secondcap.

## Completed ten-gate exclusion and sharing search, 06:59 UTC

All fifteen necessary support-orbit cases for a single ten-gate Fano core have now returned UNSAT. The twelve ten-input cases are in `sat-control-summary.json`; the three nine-input budget cases are S959 (31.64 seconds), S1951 (33.77 seconds), and S2975 (43.52 seconds). The eleven-gate budget searches S3007, S1983, and S3999 each timed out after 300 seconds. Those timeouts have no UNSAT interpretation. A consolidated manifest `fano-all-search-summary.json` records statuses, parameters, wall times, and CNF SHA256 hashes.

New encoder `fano_multi_sat.py` supports multiple designated maximal cores. The last r gates are outputs and are forbidden from reading one another; every earlier gate is read later, so the union of output cones contains all g gates and the designated roots are exactly the maximal cores. Every root independently meets the core conditions. Accepted edges are unioned across roots. The strict target is q+7 > g+r+card Y; the extra-reader budget is g-m+r. Symmetry ordering applies independently to the internal-gate prefix and root suffix. Independent initial review found these changes sound.

Pinned positive control `fano-multi-calibration` has seven gates, six inputs, two P4 cores sharing their central AND, five accepted edges, and target margin 4. Both full CNF checking and independent truth-table/core evaluation pass. `pin_multicore_control.py` reproduces its CNF byte for byte; the metadata records the 19,551 base clauses, and pinning adds 21 unit clauses, giving 19,572 clauses in the CNF header.

Two-core S2975 with nine gates returned UNSAT in 13.41 seconds. Three two-core ten-gate searches on S3007, S1983, and S3999 are running with 300-second caps. These target actual sharing between incomparable cores; they are separate from the completed single-core exclusion.

## Sharing phase update, 07:12 UTC

Two-core ten-gate S1983 returned UNSAT in 152.21 seconds. S3007 and S3999 timed out after 300 seconds. The eleven-gate two-core S3007 case also timed out after 300 seconds. A larger thirteen-gate two-core case is running on S4031, with eleven inputs, fourteen induced edges, and four extra operand arcs; its 300-second cap ends around 07:12:30 UTC.

The independent reviewer checked the positive multicore control with all 16,384 truth assignments and direct capped read-vector sets, and exhaustively tested 4,805 fanout-threshold cases. Results are in `fano-multi-calibration-independent-review.json` and repository `sat-review.md`.

`summarize_searches.py` regenerates the complete search manifest directly from solver logs and metadata. At 07:09 UTC the manifest had fifty runs: five SAT positive controls, twenty-six UNSAT cases, eighteen timeouts/unknown outcomes, and one running case. All SAT cases so far were deliberately satisfiable controls; no strict-inequality witness has been found.

## Cyclic positive control and next construction search

The default thirteen-gate two-core S4031 run timed out. An identical-CNF retry with documented CaDiCaL options `--sat --seed=71` began at 07:13 UTC, capped at 300 seconds, after renewal confirmed expiry 07:31:56 UTC.

The new `pin_cyclic_control.py` control computes the six-cycle on vertices `{0,1,2,7,8,13}` in eight gates, then adds `(f OR x0) AND f` in two gates. Its sole maximal core has U=10, D=6, tau(D)=3, and residual cover number 6. It has stronger margin 2 and target margin 4. The reviewer independently checked all 35,686 CNF clauses, all 16,384 truth assignments, and all 210 gate/edge read-vector cases. This confirms the unchanged encoder handles cyclic accepted-edge graphs. Exact replay is in `fano-cyclic-calibration-independent-review.json`.

Prepared, not yet launched: `fano-cyclic-g8` and `fano-cyclic-g9`, seeking a core on exactly these six inputs accepting all six cycle edges, without the ambient strict-violation requirement. A positive eight-gate core would be a tight cyclic seed for gluing; a nine-gate core would have one unit of stronger slack. These are construction searches, not refutation claims.

At 07:15 UTC the nine-gate cyclic construction returned SAT in 8.99 seconds. The independent decoder checks every CNF clause and the full truth table. Writing `e = x7 AND (x0 OR x1) OR x13 AND (x0 OR x2)`, the root is `(e OR x8) AND (e OR x1 OR x2)`. Its accepted graph is exactly the six-cycle, with U=9, mc=1, tau(D)=3, stronger margin 1, and ambient target margin 3. The exact gate network is in `fano-cyclic-g9-decoded.json`. This is an actual synthesized construction, distinct from the pinned controls, but it does not violate the target.

The eight-gate cyclic-core case returned UNSAT in 9.74 seconds. Thus this finite exact-support search provides a margin-one cyclic seed and excludes a margin-zero seed at eight gates. No inference from this finite result to arbitrary graph size is claimed.

Additional cyclic searches completed at 07:19 UTC. The nine-gate single-core case restricted to exactly four AND and five OR gates is UNSAT in 44.93 seconds; the discovered seed instead has three AND and six OR gates. The seven-gate two-core C6 case is UNSAT in 1.31 seconds, excluding another possible zero-strong-margin seed. The large S4031 seed-71 retry timed out at 300 seconds. The manifest now records 56 runs: seven SAT cases (six controls and one synthesized C6 construction), 29 UNSAT cases, and 20 timeouts. No solver remains active from this phase.

## Exact-function search and reconnect correction

The C6 nine-gate core subcase requiring an internal AND gate that accepts a maximal independent set returned UNSAT in 55.41 seconds. Thus the tested minimal C6 core cannot use such a filtering AND.

`exact_graph_sat.py` adds an exact-function AO2 encoder with no core requirement and an unrestricted output operation. It rejects all maximal independent sets and accepts every edge; monotonicity makes these constraints equivalent to computing the graph function exactly. Every gate is live, every nonisolated input is used, and the previously reviewed ordering and operand-arc budget apply. The exact eleven-gate theta query with four AND and seven OR gates timed out at 300 seconds. Its pinned canonical twelve-gate positive control passed all 25,800 clauses and all 256 truth assignments.

An exact 26-gate circuit for the Fano graph would improve the canonical 27-gate circuit by one gate. Three disjoint copies, two combining OR gates, and the two-gate absorption wrapper would produce one core with U=82, D=63, and minimum cover 21, contradicting the target as 84 > 83. Both 26-gate queries therefore leave the AND/OR counts unrestricted.

The baseline 26-gate query started at 07:28 and the symmetry variant at 07:31. An environment reconnect interrupted both; their surviving process entries were zombies, not live solvers. Their status is **INTERRUPTED, no verdict**, not UNSAT or a completed 900-second timeout. Full partial logs remain at their original names, and explicit `.status.json` files record the correction.

After renewal at 07:42:52, both queries were restarted at 07:43:15 under `persistent_solver.py`, using separate process sessions, SIGHUP handling, full output files, and supervisor status JSON containing child PID, return code, and wall time. New stems end in `-resume1`; original logs were not overwritten. Each retry receives a full 900-second cap, ending around 07:58:16. Supervisor PIDs are 18509 and 18508; solver PIDs are 18510 and 18511, independently observed in running state.

The optional `fano_first_orbit.py` symmetry rule restricts the first gate's input pair to one of `(0,0)`, `(0,1)`, `(0,7)`, `(2,7)`, retaining both operations. The reviewer validated the minimum-orbit argument, all 336 graph automorphisms and all 105 unordered input-pair orbits. The transformed canonical 27-gate control passed all 351,935 clauses and all 16,384 assignments. The baseline canonical control also passed its 351,922 clauses. The pruning changes neither the unrestricted gate-type budget nor the target function.

`sat-all-search-summary.json` now includes exact-function searches and explicit interruption/supervisor states; `fano-all-search-summary.json` remains the Fano-only subset. At 07:43 UTC there were 65 recorded runs: ten SAT cases (nine controls and one synthesized non-refuting C6 core), thirty UNSAT cases, twenty-one timeouts, two interrupted runs, and two running retries.

## Final computational status, 07:58 UTC

Both persistent retries completed after their full 900-second limits, with solver return code 0 and UNKNOWN. The baseline wall time was 900.068 seconds; the first-pair orbit variant used 900.085 seconds. Neither produced a 26-gate circuit or an UNSAT verdict. All supervisors finished and no solver remains active. The final 65-run manifest counts ten SAT cases (nine controls and the non-refuting C6 seed), thirty UNSAT cases, twenty-three completed timeouts, and two interrupted runs. The interrupted originals remain distinct from the completed retries. The posted general inequality is still unproved, and no strict counterexample was found.
