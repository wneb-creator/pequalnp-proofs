# Independent local synthesis

The source `anneal.cpp` implements simulated annealing over fixed-budget backward binary AND/OR netlists. It is separate from the SAT search. Gate operands always refer to primary inputs or earlier gates; the output may be any wire.

Search starts from every way to delete one gate from the accepted star baseline and redirect its uses to one operand. Mutations alter one to three gate fields. Scores are errors on the positive two-variable edge inputs and negative maximal independent-set inputs, with positive/negative weights varied between restarts. Neutral moves and annealing allow exploration across equal-score netlists. Good candidates seed later restarts.

All extremal rows fit in one 64-bit word (K4 incidence: 24; Fano: 58). A perfect extremal fit is verified by a separate ordinary Boolean evaluation on all assignments, then written to a witness file. The monotonicity of the AND/OR network also means these extrema determine the whole target. Search failure gives no lower bound.

Inputs and baselines are supplied by the independent SAT agent and are exhaustively rechecked before search. Baseline text uses op0=AND, op1=OR; gate g outputs input-count+g. Candidate output files append an explicit `output n` line, since the selected output need not be the last gate.

First run: K4 incidence, 14 gates, seed2583104, 240-second limit, one CPU. Full stdout/stderr and best candidates remain at `/tmp/oec/pequalnp-pilot-104/counterexample2583/anneal-k4-01.*`. No witness has been claimed without all-assignment verification.

Stopped on root instruction after an unexpected lease-expiry response. The final flushed checkpoint was 220.125 seconds, 1,721,040,896 mutation proposals and 57,369 restarts. Best error stayed at one of the 24 extremal rows, already reached by the initial one-gate deletion; no exact witness was found. The process was terminated with SIGTERM (exit143), so no final exhaustive score was generated. Complete stdout/stderr and best net are preserved under `anneal-logs/`.

Independent reviewer checked mutation bounds, deletion remapping, extremal generation, score polarity and exhaustive evaluator. The candidate loader was then hardened to read explicit output records, and the verifier now checks output/capacity bounds. These source-only robustness changes were not rebuilt before the pause; the active search had used the verified last-output baseline and was unaffected.

`anneal_readone.cpp` is a prepared, unrun extension with read-1 guidance, neutral topological swaps and an optional frozen prefix. A16-gate K4 seed begins with protected OR(4,9), followed by the original15-gate star circuit with internal wires shifted by one. Deleting an unprotected gate and freezing gate0 targets the shared-output15-gate gadget proposed by the SAT agent. The saved readone build log predates the loader/frozen-prefix/swap additions; the latest extension source is UNCOMPILED and UNRUN. No claim is made about that experiment.
