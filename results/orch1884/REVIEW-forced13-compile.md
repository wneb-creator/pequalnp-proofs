# Independent review: Forced13Compile

UTC: 2026-11-25T16:45:23.516417+00:00

Verdict: PASS as a conditional actual-circuit construction. Source SHA256 `4fd60a4daa1d764e013c0c3efd713202f33366a7fb4906ddc3923f276412015f`, 5269 bytes/129 lines. Author reported Lean exit0; complete forced13-compile.stdout/.stderr beside the source are empty. This reviewer did not rebuild.

inputMap maps the original11 input positions to false at0, the new nine primary wires at1–9, andtrue at10. seed gives exactly the corresponding evaluation input. input_invariant checks all11 positions and the out-of-range defaults against the existing Elim invariant.

compile assumes both surrounding gate lists are AND/OR with fan-in≤2, the selected replaced gate is AND[], original total≤18, and an explicit charge of at least4 reader gates across prefix/suffix. The counted sets are rails{0,10} in the prefix and those rails plus the selected gate's original wire11+prefix.length in the suffix. ElimManyCount charges those four distinct gate positions and the selected true-constant gate itself, proving emitted size≤13. Gates reading multiple selected wires are counted once. No semantic reader-count premise is silently inferred.

The existing Elim invariant proves exact evaluation on every natural nine-variable input. Explicit nonconstancy rules out a constant status for the output, so an actual outputwire is available without adding a constant gate. The separate operation-preservation induction proves the emitted circuit is Monotone2; general Elim fan-in correctness supplies the arity bound. This is an actual semantic construction, not just a count on a simplified list.

The input import ElimManyCount is a scratch dependency, not a permitted standalone final import. Correct L_meta_1884 namespace; no options, attributes, strings, forbidden constructs, new axioms, unsafe declarations or secret-like content; below512KiB. The hypotheses still need to be derived from the one-NOT candidate, and this file does not prove the25-row specification or the full posted statement.
