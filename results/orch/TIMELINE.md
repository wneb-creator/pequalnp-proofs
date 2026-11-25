# Timeline

2026-11-25T14:54:50Z job started
2026-11-25T14:55:38Z desk returned L-meta-2583 and a lease
2026-11-25T14:55:52Z initial renewal succeeded, expiry 15:15:52Z
2026-11-25T14:56:03.868675+00:00 upstream updated to 94b1f7f9
2026-11-25T14:57:25Z lease renewal succeeded; expiry 15:17:25Z
2026-11-25T14:58:29Z construction and lower-bound routes identified; no full proof
2026-11-25T15:01:13.641387+00:00 Construction.lean compiles; independent static review passed; preparing first partial push
2026-11-25T15:02:17.377588+00:00 library-route necessity package compiled successfully
2026-11-25T15:02:47.183240+00:00 Necessity.lean compiled; independent review passed; preparing partial push
2026-11-25T15:03:49.914620+00:00 Structure.lean compiles; independent review passed; preparing partial push
2026-11-25T15:03:54.213313+00:00 library-route exact replacement/size-bound equivalence compiled
2026-11-25T15:04:30.251401+00:00 Equivalence.lean compiles; independent review passed; preparing partial push

2026-11-25T15:08:05.201012+00:00 Counterexample strategy pivot: stopped duplicate neutral-drift Fano search after progress trials=3700000000 restarts=3700 best=1 seconds=370.913. No witness; nonexhaustive. Started exact14gate SAT on subdivision K4 (10inputs,12edges,24boundary tests,1484vars,23467clauses), 600-second cap. Canonical15gate positive control verified all1024inputs and fixed SAT instance accepted.

2026-11-25T15:10:38.252294+00:00 Counterexample searches stopped on root instruction after lease410. No26gateFano witness and no14gateK4-subdivision witness found. Exact finite design enumeration:30 Steiner triple systems on7 labeled points, each37 maximal independent sets. Search statistics: {"fano-search.stdout": {"recorded_lines": 242, "last_progress": "progress trials=5950000000 restarts=23800 best=1 seconds=759.595", "status": []}, "fano-neutral.stdout": {"recorded_lines": 41, "last_progress": "progress trials=3700000000 restarts=3700 best=1 seconds=370.913", "status": []}, "subdiv-k4-14-solver.stdout": {"recorded_lines": 1072, "last_progress": null, "status": []}}. Complete logs and source retained in /tmp/oec/pequalnp-pilot-147/. No Lean proof or refutation produced by this route.
2026-11-25T15:11:15.010783+00:00 work stopped after HTTP410; complete artifacts preserved for push before any lease re-request
2026-11-25T15:11:24.320313+00:00 construction agent stopped allSAT searches on root HTTP410 instruction; no witness found
2026-11-25T15:12:27.054869+00:00 preservation diff independently reviewed; pushing complete artifact archive
2026-11-25T15:13:32.846186+00:00 same pre-existing L-meta-2590 lease returned twice with held-limit note; stop under shared-handle rule
