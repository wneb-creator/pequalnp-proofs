# Counterexample search for L-meta-2592

## Semantics audit

Circuit evaluation is ordinary acyclic straight-line AND/OR/NOT evaluation. Missing wire indices read false; constants provide no evident loophole. FanInTwo excludes other operation kinds. No malformed-index exploit found.

## Combinatorial baseline

Enumeration of all 1024 vertex sets gives minimum vertex cover 6, with exactly 5 minimum covers. One is {0, 1, 3, 7, 8, 9}. Assigning each of the 15 edges to a cover endpoint, grouping the edges into six stars, and OR-combining the stars gives a 20-gate monotone circuit. This explains the stated upper bound, not the arbitrary-circuit lower bound.

## Encoders

- `counterexample.cpp` selects two earlier operands and AND/OR/NOT at each gate. It requires at least one NOT and last-gate output. A virtual false source represents an invalid wire. One-hot selectors and operation clauses are checked by an independent reviewer. Ordinary source indices must be translated before constructing a Lean circuit: source 10 is false, source 11+g is gate g.
- `counterexample_aig.cpp` uses AND nodes with complemented edges and an output phase. It checks every SAT candidate on all 1024 assignments and adds every mismatching input. Any full witness is converted to AND/OR/NOT by exhaustively optimizing internal node orientations; one NOT is charged per source needing its opposite polarity.
- The AIG encoder optionally constrains the number of actual NOT sources directly in SAT. A connected-topology constraint ensures every binary node is read later. Unused capacity can be padded by output-copy AND gates, so at-most-n witnesses remain representable.
- Initial AIG rows are the 15 positive edge pairs, 15 maximal independent negative sets, and both endpoints. The ordinary unrestricted run began with all 76 independent-set negatives, 15 positive edges, and the all-true endpoint.

## Validation

A pinned 21-gate ordinary circuit (known 20-gate monotone circuit plus a dead NOT) is SAT and independently matches all 1024 inputs. A pinned 20-node AIG is SAT, also matches all inputs, and orientation optimization recovers zero necessary NOTs. The same baseline passes with NOT budget zero and connected topology enabled. The independent reviewer found no sign, source-index, or cardinality defects in the original encoders. Later budget constraints and new structural pruning are awaiting review.

## Search status at 2026-11-25 14:27 UTC

No counterexample or UNSAT result has been found.

- General 19-gate ordinary search: stopped, inconclusive.
- First gate NOT(input 0), sorted maximum source: stopped, inconclusive.
- Exactly 4 NOT gates and 15 binary gates: stopped, inconclusive; the combinatorial team has since found a 16-binary lower bound.
- Exactly 1 NOT with essential-polarity orbit h({0,1}) = false, h({1,4,5}) = true: stopped, inconclusive.
- Local repair fixing the first eight baseline gates: reached its short wall cap, inconclusive.
- Unrestricted signed 18-node AIG: paused after about 3 minutes, inconclusive.
- Signed 17-node AIG with at most 2 actual NOTs: paused after about 6 minutes, inconclusive.
- Unrestricted signed 17-node AIG: paused, inconclusive.
- Signed 17-node AIG, first pair (0,1), both first input literals negative, every later read of either input negative, and at most two distinct binary readers per primary input: currently active, 10-minute cap. The few_nots agent supplied checked necessary restrictions for minimum unrestricted signed circuits in this case. The nonadjacent first-pair representative (0,2) remains to be searched.

Only one SAT process is active because the container has three CPUs. Complete logs are under `/tmp/oec/pequalnp-pilot-104/counterexample/`. CaDiCaL was fetched from github.com/arminbiere/cadical and compiled there. Compiler objects were removed to save disk; the static library and executables remain.

These are computational searches, not Lean lower-bound certificates. Restricted searches do not establish completeness outside their stated class. Any emitted witness still needs an independent truth-table check and a Lean proof before submission.

The next minimum-circuit search version additionally removes constant/identity binary gates (distinct sources, no false-source operand) and forbids later duplication of the first pair. The latter is being formalized by few_nots. These changes are not in the currently running binary yet.

2026-11-25T14:27:58.029082+00:00: the active restricted signed-17 search found a SAT model for the 32 extremal rows. Independent full-table evaluation rejected it on 487 other inputs; all were added, bringing the instance to 519 rows. This shows the 32-row restriction alone admits a signed 17-node separator under current structural constraints. The first partial model was not printed; new encoder versions log all candidate topologies. The deterministic seed 113 run can reproduce it if needed.

2026-11-25T14:30:06.449675+00:00: paused the adjacent-pair instance at519rows. Started the nonadjacent first pair(0,2), both negative, global readercap2, no constant/identity binarynodes, and no duplicatefirstpair. New CEGAR refines with up to32 Hamming-diverse bad inputs per model rather than all failures; every model is still checked on all1024 inputs. Candidate topologies are now printed into complete logs. One SAT process active.

2026-11-25T14:30:28.543926+00:00: stopped all superseded paused AIG runs as inconclusive, freeing their memory. Only the new nonadjacent-pair diverse-refinement search is running. Complete prior logs and reproducible source/binaries remain.

2026-11-25T14:36:50.733162+00:00: started guided nonadjacent signed-17 search with65 cofactor bounds (10 singleton-zero,45 pair-zero,10 mixed vertex-one/neighbors-zero restrictions). A three-valued constant-propagation encoding counts eliminated binary gates and enforces the certified residual lower bounds using sequential counters. Known20baseline passes all65 cuts; an intentionally impossible all-inputs-fixed residual lowerbound1 is UNSAT, as expected. New structural bans prevent any first-output consumer from directly reading either first input; the proof was independently derived by counterexample/combinatorial agents and is being formalized by few_nots. The initial64 truth rows include32 failures preserved from an earlier candidate. Full1024 validation and diverse32-row refinement remain active. One SAT process,15-minute cap.

2026-11-25T14:44:33.986457+00:00: root requested immediate pause due to desk lease error. Active SAT process suspended. No full signed17 witness or target counterexample; no UNSAT result for the target search. Complete search/build logs and data copied to counterexample_checkpoint.txt for preservation. No new runs started.
