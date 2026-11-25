# L-meta-2590 counterexample search

Started 2026-11-25T15:14:07.483763+00:00.

The target is the Petersen edge function on10 inputs with15 edges. There are15 maximal independent negative assignments; together with the15 positive edge assignments, these30 rows completely determine correctness of an AND/OR circuit by monotonicity. Every candidate is additionally checked on all1024 assignments.

The known20-gate star-cover circuit passes the SAT encoding, all1024 truth values, and read1-vector checks on all15 edges. It is not a counterexample.

Current search: at most19 AND/OR binary gates, earlier-wire reads, no first-gate pin, colex topological ordering, and dominance-normal minimum prefix followed by optional identity-padding gates. The source is copied from the independently reviewed monotone encoder. Generic Monotone2 constants and invalid reads are not directly represented; this is a witness search for the ordinary well-formed binary subclass.

One SAT CPU is active. The annealer has the same graph, baseline and extremal rows in `/tmp/oec/pequalnp-pilot-104/counterexample2590/`.

Prepared, but not yet run: a Petersen symmetry mode restricting the first pair to(0,1) or(0,2), while leaving AND/OR free. These represent adjacent/nonadjacent input pairs under the graph automorphism group; the nonadjacent AND is excluded automatically by positive-row relevance. The current process does not use this extra mode.

No counterexample or target UNSAT result yet. Complete logs remain in task scratch.

At 2026-11-25T15:20:07.482279+00:00, stopped the initial run after more than3.2 million conflicts, with no witness or UNSAT. Complete log: search19-dominance.log. Started a stronger19-gate run using the prepared Petersen first-pair symmetry, exact singleton/pair READ1 flags constrained on the last active gate before identity padding, and ten singleton-false constant-propagation cuts allowing at most3 eliminated gates. READ1≥20 has now compiled in the team proof; cofactor cuts use the accepted ordinary nine-vertex floor16. The new CNF was independently audited by status_review. Known20-gate baseline passes all cuts and flags. An identity-padded baseline is correctly rejected by nonREAD1 before padding, while a duplicated two-input AND is accepted as nonREAD1 without dominance. These are computational checks, not a Lean certificate for SAT infeasibility. New full log: search19-read1-cofactor.log.

Stopped all SAT at2026-11-25T15:23:44Z on root instruction after the third unexpected lease failure. Strong run reached20 completed100,000-conflict budgets and at least211 seconds; no witness or UNSAT. Initial run also remained inconclusive. All20 complete logs/data files are copied into counterexample-logs with hashes in counterexample_checkpoint.txt. The smaller free-OR search was prepared but NEVER STARTED; only its pinned17-gate baseline was validated on all512 inputs and all94 inherited zero-cofactor cuts. The optional READ1 pruning for this smaller target remains a mathematical observation, not a checked theorem yet.
