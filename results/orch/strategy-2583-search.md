# L-meta-2583 counterexample search

Actual definitions checked: IsAO2 means AND/OR only, exactly two earlier input wires per gate. IsReadK is joint proof-tree multiplicity on every prime implicant, not global read-once usage. No obvious definition loophole was found.

Use the cyclic Fano plane: q=2,N=7,I(p,l) iff p=l or p=l+1 or p=l+3 in Fin7. Points are wires0..6; lines7..13. The identity is an incident perfect matching. Existing checked L_meta_7639 gives read1 size>=27; a 26-gate AO2 witness would refute the assigned statement. Agent gate_elimination is preparing the matching lower-bound formalization.

There are21 minimal true edge assignments and37 maximal false assignments; independent computations agree. Monotonicity makes these58 rows sufficient for exact truth-table correctness. All16384 rows will still independently validate any candidate.

Prepared a27-gate star circuit. Its function was verified over all16384 rows, its fixed positive-control SAT query was SAT, and the extracted model passed independent wiring, full-function, and joint-read1 checks on all21 implicants. Data and source: /tmp/oec/pequalnp-pilot-121/fano-sat/fano-data.json, star27.txt, fano.py.

A bounded26-gate58-row exact synthesis run is prepared, awaiting the root lease beat. No witness yet. No new large search before the definitions and read1 lower-bound threshold were checked.

## Fano26 route closed by existing checked proof

2026-11-25 about14:58UTC: gate_elimination found and I independently inspected the stronger helpers hidden in L_meta_7997. Atline9341, heawood_lb_27 proves27≤size for every Monotone2 circuit computingHeawood. Atlines9406and9428, fano27 andao27 transfer exactly our cyclic incidence convention. The advertised final theorem usesao27 and ignores its reread hypothesis. Thus a26-gate Fano witness is mathematically excluded by an already checked proof, not merely absent from search.

The single300-second26g SAT run finished UNKNOWN(timeout), not UNSAT. No further Fano26 query was launched. All SAT processes stopped naturally. Stochastic agent was told immediately to stop as well. New exploration must use a larger plane or a proof strategy; audit hidden helpers before starting another large synthesis run.

## q3 Singer13 work before second lease loss

N=13, difference set {0,1,3,9};52 incident edges and704 maximal false assignments, hence756 critical rows. Geometry, identitymatching, and complete boundaryset were independently checked by status_review. Data file SHA256e46876bc469fd9743e0b2c98ab65af85390c0bbd021295792a8acbd6bebf02f2. Explicit64-gate star seed is joint-read1 onall52edges. Its fixed SATcontrol passed onall756rows, and extractedmodel verification foundzero errors; not_elimination additionally verified the seed onall67,108,864 assignments by bit-parallel C++.

A single63-gate search used97 initial criticalrows: all52 positives and45 negatives drawn from canonical-badedge stabilizer representatives plus extreme pointcardinalities. It was a CEGAR witness search, requiring independent full756-row validation forany model. Included joint-read1 failure atedge(0,13), hoisted clean/dirty form, cleanwire fanout<=1, and singletonpositive-profile atomicAND normalization. For samplednegatives, cleanlabels only implied sampledzero, so sampledcleanliness was not mistaken for trueBelowF. No Fano-specific SingleRead condition was transferred.

At15:10:09UTC root reported the second lease410 and ordered stop. Exactsolver PID14583 was terminated withSIGTERM, exit143, beforeany verdict. There is no q3 SAT/UNSAT result and no counterexample. Allqueries, fullstdout/stderr, source, datasets, positivecontrols, verifier andlease-stop.json are preserved under /tmp/oec/pequalnp-pilot-121/plane3-sat. No solver remains active; no new work was launched after stop.
