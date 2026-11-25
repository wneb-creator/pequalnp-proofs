# Petersen search checkpoint for L-meta-1884

No counterexample or UNSAT proof of the gap has been found in this checkpoint. All completed exclusion searches returned UNKNOWN/timeouts. Every actual SAT model saved as a `-model.json` file is a positive control with more than18 gates, independently checked on all1024 inputs. The partial-row SAT candidate in the prefix CEGIS history failed250 inputs and was rejected.

## Model and scope

The target is the exact fifteen-edge Petersen function in the posted statement. Inputs0..9 are identity projections, input10 is the free complement of input0. A virtual false input is encoded internally at index11 and translated to actual out-of-range wire999; internal virtual wire indices shift down by one on extraction. This matches the circuit definition, where forward/out-of-range references readfalse. Gates are AND/OR/NOT with at mosttwo arguments; NOT uses one effective argument. Constanttrue can be represented by NOT(false) for onegate, the same cost as an emptyAND. These searches cover the free-complement case; no completed global exclusion is claimed for the other three unary functions.

Commutative gate arguments are sorted, the output is last, everygate is used, and adjacent independent gates are ordered by operation/arguments. Coverage of the adjacent ordering follows by choosing the lexicographically least key sequence among topological orders: swapping an inverted independent adjacent pair preserves bothkeys and all earlierkeys, so later renumbering cannot prevent a strict lex decrease. Smaller circuits can be pruned and padded with idempotent AND output gates. These normalization arguments were independently reviewed mathematically, not encoded in Lean here.

AO-only searches use38 cofactor-extremal assignments, exact because the circuit is monotone in the othernine variables after fixing input0. General searches use CEGIS: seedrows constrain a subset of assignments, but everycandidate is evaluated on the complete truth table and everyfailure is added. Later case searches seed108 rows: the extrema, everyfalse targetinput, allones, and each allones-minus-one input. UNSAT on anyseed set would imply the corresponding restricted search class is empty; no such UNSAT occurred.

Accepted L6194 justified the earlier budget of at mostthree paidNOT gates. Stronger accepted L6581 gives at least16 non-NOT gates after prepending the free complement, hence at mosttwo paidNOT gates in an18-gate candidate. Accepted Petersen-minus-vertex exclusion L670 implies at mosttwo distinct readers of inputs0/10 combined, and at mostthree readers of everyother primaryinput, by restriction and constantpropagation. The case queries use these mathematically reviewed necessary conditions.

## Completed results

- AO-only size18 and size19 with freeNOT0: UNKNOWN after180.020s and180.062s.
- General size18, at mostthree paidNOTs: UNKNOWN after300.079s.
- General size18 with readerbounds, at mostthree paidNOTs: UNKNOWN after180.029s.
- Nine fixed pure-OR gates from the standard20-gate circuit plusnine arbitrary gates: first38-row model SAT in7.283s but failed250 fulltruth inputs; refinement to288rows returnedUNKNOWN. Total180.503s.
- Both010 case (oneOR reader of raw0, oneAND reader of freeNOT0), at mosttwo paidNOTs, rawreaderfirst: UNKNOWN after180.139s; auxiliaryreaderfirst: UNKNOWN after180.135s.
- Full only10 case (raw0unused, auxiliaryreadatmosttwice; NOT10 allowed), at mosttwo paidNOTs: UNKNOWN after180.169s.

Positive controls:
- Standard20-gate circuit: fixed AO query SAT0.005s; fixed general query SAT0.122s, fulltruth verified.
- Both010 rawreaderfirst23-gate circuit: SAT0.511s, fulltruth verified.
- Both010 auxiliaryreaderfirst23-gate circuit: SAT0.508s, fulltruth verified.
- Only10 circuit with21gates and a NOT10 reader: SAT0.415s, fulltruth verified. This specifically checks that the encoding permits reconstructing raw0 from the free complement.

The three longer case queries with at mostone paidNOT are stillrunning at this checkpoint and are not listed as completed results. Their programs are included, but active logs/SMT snapshots are excluded until they finish.

## Reproduction and integrity

Scripts use Python3 and Z3 5.3.3 from the same officialGitHub wheel documented in results/orch/search/VALIDATION.md. No solver binaries, archives of solver software, environment dumps, or credentials are included. Complete stdout/stderr logs are preserved. SMT files are gzip-compressed to conserve disk; `SMT_UNCOMPRESSED.json` records exact uncompressed hashes and sizes. `MANIFEST.sha256` covers everybundled file exceptitself.

Examples: `python3 petersen-ao-synth.py 18 180000`; `python3 petersen-general-cegis.py 18 300000 not`; `python3 petersen-both010-cegis.py 18 180000 not rawfirst`; `python3 petersen-only10-cegis.py 18 180000 not`. Paths to generated artifacts are session-local scratch paths. The optional fixed-control arguments and controls script reproduce the validation models. Later source versions add optionalcontrols and size-qualified output filenames; the original SMT assertions remain preserved exactly.
