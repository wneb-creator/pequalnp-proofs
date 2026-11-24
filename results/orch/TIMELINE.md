# Pilot-39 timeline (UTC)

- 2026-11-24T17:57:13Z: first environment inspection.
- 2026-11-24T17:58:25Z: acquired L-meta-2584 lease; initial expiry 18:18:25Z.
- 2026-11-24T17:59:08.603926+00:00: launched independent combinatorial, circuit, and counterexample strategies.

- 2026-11-24T18:00:48.873760+00:00: counterexample_search completed exhaustive 2x3 and 2x4 graph checks; no counterexample to star-cover cost lower bound.
- 2026-11-24T18:01:18.935322+00:00: combinatorial_route drafted prime-implicant and biclique-star helpers; awaits pinned Lean/cache.
- 2026-11-24T18:03:38.450119+00:00 circuit_route: generic flat-circuit read-2 candidate completed; toolchain cache still downloading; no checked claim.
- 2026-11-24T18:03:46.653926+00:00: pinned Lean recovered; all 9117 prebuilt Mathlib files downloaded; started first named-module partial build. Lease expiry renewed to 18:23:38Z.

- 2026-11-24T18:04:55.976297+00:00: counterexample_search found no non-read-2 optimal 2x3 circuits among 471 exhaustive cases; Z3 excluded six/seven-gate C6 circuits and found checked eight-gate read-1 control.
- 2026-11-24T18:04:57.391658+00:00: three root helper lemmas compiled; independent partial review passed; committing first checkpoint.
- 2026-11-24T18:06:07.939296+00:00: integrated and built prime-implicant/read equivalences and biclique-star lemmas; independent review passed.

- 2026-11-24T18:06:09.348742+00:00: counterexample_search completed C6 optimum/read2 SMT checks; all eight-gate minimum circuits satisfy read2 in solver encoding. Began C8 and stronger read1 tests.
- 2026-11-24T18:07:13.993006+00:00 circuit_route: first CoverRead component Lean compilation successful; root notified for immediate checkpoint.
- 2026-11-24T18:08:51.705706+00:00: integrated flat and canonical star-cover read-2 proofs; build and independent review passed; checkpoint 3.

- 2026-11-24T18:09:08.629267+00:00: counterexample_search kernel-checked explicit C6 eight-gate circuit, exact incidence function, AO2, C4-free relation, and full read2; root notified for integration/push.
- 2026-11-24T18:10:14.746961+00:00: structural route checked TopForm + exactly one dirty AND => read-2.
- 2026-11-24T18:11:32.378946+00:00: checkpoint4 integrated graph/support/certificate/C6 components; build005 and independent review passed.
- 2026-11-24T18:11:36.601444+00:00: combinatorial_route checked graph bridge, generic support lower bound, both one-star degree bounds and active-input lower bound.
- 2026-11-24T18:12:01.256934+00:00: structural route extended checked theorem to at most one dirty AND.

- 2026-11-24T18:12:51.696195+00:00: counterexample_search excluded two-dirty-AND top cones in minimum C6 circuits by SMT; confirmed no dirty AND among all471 optimal2x3 cases; larger searches timed out without conclusions.
- 2026-11-24T18:14:14.646837+00:00: combinatorial_route checked full replacement theorem for arbitrary disjoint point-star forests.
- 2026-11-24T18:14:29.730474+00:00: structural route checked sharp two-dirty auxiliary obstruction and smaller read2 replacement.

- 2026-11-24T18:15:57.613710+00:00: counterexample_search closed larger finite search after CaDiCaL time cap; delivered checked C6 component and finite evidence, no general proof/refutation.
- 2026-11-24T18:16:10.511951+00:00 circuit_route: checked general star-cover certificate, both singleton-side constructors, and6-gate structural counterexample; per-top leastness route remains unresolved.
- 2026-11-24T18:17:32.137743+00:00: structural route checked local one-dirty-per-top criterion for read-2.
- 2026-11-24T18:17:39.850163+00:00: checkpoint5 builds/review passed. Replanned around private common-factor gate surgery, pure-OR sharing restrictions, and per-edge joint witness repair; stopped bulk known-subcase copying.
