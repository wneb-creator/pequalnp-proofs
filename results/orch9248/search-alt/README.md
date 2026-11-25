# Alternative constructive search for L-meta-9248

The target is a refutation of PHP(5,4) using at most12 RUP-learned clauses, including the empty clause. No such target witness has been found here. The independently checked16-clause candidate is a partial upper bound only; lean_setup has also compiled its Lean certificate.

All JSON runs here are oldest-first. A signed integer literal is `sign * (4*pigeon + hole + 1)`: positive means true and negative means false. This differs from the encoded literal convention used by the Lean emitter. Convert signed `l` to `2*(abs(l)-1)+(l<0)` for that emitter, and reverse the clause list only when constructing IsRUPRun's newest-first list.

Initial clauses are the five pigeon rows, followed by negative same-hole pairs in loops pigeon p, pigeon q>p, hole h. PHP does not include at-most-one-hole clauses for a pigeon.

`rup_tools.py` independently replays each candidate with ordinary unit propagation and records an actual known clause falsified by the propagation. Tautological candidate clauses are rejected; contradictory assumptions are not treated as an independent RUP axiom. `baseline20.json` is extracted and validated from library L_meta_9250, whose displayed bound24 contains an actual20-step proof.

`cdcl_search.cpp` generates randomized CDCL refutations using first/last/decision UIP variants, minimizes each learned clause by actual RUP tests, and drops redundant learned clauses from complete runs. The5-second diagnostic completed9,588 solver trials and found16 clauses. The20-minute control started2026-11-25T17:11:00Z after root's17:10:35 renewal. Every better complete trace is flushed immediately; `watch_log.py` independently validates and archives each improvement with its UTC time.

`proof_opt.cpp` explores a population of complete valid refutations: valid adjacent reordering, literal strengthening, RUP pair intersections, insertion of minimized RUP clauses or resolvents, and greedy redundant-step removal. It retains variants up to two clauses longer than the best. Its5-second diagnostic completed51,608 mutation trials without improving16. A long optimizer run has not started as of this note; status.json and logs record any later run.

All long diagnostics preserve complete stdout and stderr. Root owns the desk lease and all git/PR operations. On any lease-loss notice, stop both solver and watcher processes, validate the final complete log, and freeze artifacts before further work.
