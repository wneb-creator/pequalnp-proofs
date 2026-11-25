# Counterexample search for L-meta-2592

2026-11-25T13:50:44.111561+00:00

## Definition audit

FanInTwo allows only AND, OR, NOT with at most two operands. Every gate counts. Out-of-range/forward reads are false. Zero-arity AND and NOT produce true at a gate cost. No semantic loophole found.

## Verified baseline

A 20-gate monotone circuit comes from a six-vertex cover: assign each of the 15 edges to an endpoint in the cover, build six star expressions, OR them. Vertex cover [1,3,4,5,6,7] gives 15 gates in stars plus 5 combining ORs. Explicit JSON is /tmp/oec/pequalnp-pilot-98/search/known20.json and all 1024 inputs were checked in Python.

## Search

One CPU stochastic bit-parallel search examines legal 19-gate circuits against all 1024 inputs. C++ source /tmp/oec/pequalnp-pilot-98/search/stochastic.cpp. First best has 10 errors and an unused NOT; an active-NOT variant adds a penalty for unused NOT and maintains exactly one NOT. These are heuristic attempts, not exhaustive lower-bound evidence. No valid witness yet.

A stronger near-witness has 18 active monotone gates plus one unused NOT and only four false positives: input masks 138,385,521,770. Its explicit gates are best19.json in scratch, sent to exact_synthesis for local repair. Factoring its formula gives x4*H OR x2*B OR x6*E OR x5*J OR (H AND B AND E AND J), where B=x1 OR x3 OR x7, E=x1 OR x8 OR x9, H=x0 OR x3 OR x9, J=x0 OR x7 OR x8. The four bad points are independent triples. This indicates reusable neighborhood sums compress the residual matching to within two gates of the known optimum, but does not establish a counterexample.

## Reduced multioutput search

Following root/exact_synthesis decomposition, now searching 11 gates on six inputs a,b,c,d,e,f. Outputs b∨c∨e, a∨c∨f, a∨d∨e, b∨d∨f need be correct only on the 27 assignments where M=(a∧b)∨(c∧d)∨(e∧f) is false; M itself must be correct on all 64 assignments. Such a network plus four satellite ANDs and four ORs gives a 19-gate Petersen witness. Source multi-relaxed.cpp, complete log run-relaxed11.log in scratch/search. Mandatory-NOT penalty enforces presence; validity is checked independently before reporting any witness. Earlier searches were interrupted to keep CPU usage at one process.

2026-11-25T13:59:35.640355+00:00 Completed relaxed11 search: 1,474,300,000 candidates across 3,686 restarts over 300 seconds, best8 mismatched constrained rows, no witness. One-gate local repair around19gatebest4 candidate tested7,872 cases, no improvement. Two-gate local repair is running.

2026-11-25T14:14:02.626515+00:00 Lean candidate results/orch/lemmas/approximation.lean passed (69-line source). Full successful compiler output copied to results/orch/approximation-build.log. The proof isolates a10Bool identity checked by decide (349ms), then simplifies the concrete18gate circuit symbolically (1.11s), avoiding expensive direct Circuit.eval reduction. It proves exact approximation and explicit counterexample to that approximation being exact; it does NOT refute L-meta-2592.

Active-one-NOT full19 search completed300s:867,200,000 candidates,2,891 restarts, best18 realerrors, no witness. Earlier local2gate repair completed56,123,136 candidates40.0s, best4unchanged. All heuristic processes are stopped while rootchecker runs.

## Prepared ABC strategy (not run)

Official source reviewed 2026-11-25: https://github.com/berkeley-abc/abc states, “To compile the ABC executable, run `make`.” Its Makefile https://github.com/berkeley-abc/abc/blob/master/Makefile confirms ABC_USE_NO_READLINE and ABC_USE_NO_CUDD switches. Source download/build is paused pending root disk clearance.

Prepared scratch/search/known20.blif, unitbasis.genlib, and blif_to_circuit.py. The mapper library assigns AND2/OR2/NOT cost1, NAND2/NOR2 cost2 (expanded to actual counted gates), constants false0/true1, buffer0. The independent BLIF converter round-trips the known20 seed to20 gates, zero NOT, and all1024 correct rows. Any optimized candidate must pass the same exact check before Lean work.

Official ABC CI artifact14744518622 (master bd23a971519f70b1a8dbb8d0a2c0574eeb69af69, successful workflow44998854903) was found at44.8MB. Download through gh failed at an external artifact-storage redirect with Forbidden; no binary bytes downloaded. Diagnostic URL parameters were redacted from the saved error file. No alternate client or host retry attempted.

2026-11-25T14:26:51.378489+00:00 New C6-core strategy running:13gates, seven inputs [0,2,3,6,7,8,9], outputs for satellites [1,4,5] on C6=false plus exact C6. Current best6 core errors are three false opposite pairs with either common-input value. Independently lifted candidate has19gates/twoNOTs but15 wrong Petersen inputs; rejected. Positive validation baseline14core gates lifts to20 and passes all128/1024 rows. Validator scratch/search/lift_core13.py; baseline cycle14-baseline.json. The prepared exact/core13.py SAT model will run after this heuristic phase.
