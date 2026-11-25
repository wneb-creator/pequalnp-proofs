# L-meta-4970 orchestration

Root holds the only team lease and renews it. Exact statement/imports: /tmp/oec/pequalnp-pilot-99/gap4970. Desk response: desk-poll-003.json. Assigned15:40 UTC, initial expiry16:00:40.412. No reductions, no openPRs reported. Targetownedbyroot: lean/PEqualNP/Outside/L_meta_4970.lean.

Goal: bipartite C4-free edge function, AO2, tCount0, each edge has a pure star OR somewhere in the circuit; prove a vertex cover S with |E|+|S| <= size+1.

Routes: library_route searches/adapts existing lemmas; lower_bound develops combinatorial charging; reduction_strategy studies semantic normalization and center uniqueness; sat_encoding develops support accounting; counterexample tests weak/dead-gate assumptions; status_review independently checks all steps.

Critical early finding: tCount is based on syntactic OR reach, and AND resets that reach. It is not a semantic monochromatic-support condition. Hidden colors through AND require explicit accounting. Star OR witnesses are not required to be live.

Previous three gaps are unproved and withdrawn. Their checkpoints and exact checker rejections are preserved in results/orch. Do not resume old gap work except reusing existing checked lemmas for this live assignment.
