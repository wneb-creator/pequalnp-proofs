# L-meta-2583 working notes

New lease assigned at about 2026-11-25 14:43 UTC, after the previous L-meta-2592 lease returned HTTP 410. All old results were pushed first. Root alone manages the lease and git. Six subagents have separate notes files; shared facts are summarized here.

The statement asks for an AO2 read-1 replacement for a projective-plane incidence circuit, with no greater size. Read-1 means one squarefree proof tree per prime implicant, not a globally read-once circuit. Known checked constructions and lower bounds identify the optimal read-1 size as N*(q+2)-1. Thus a q=2 Fano circuit of size26 refutes the statement, whereas a general unrestricted lower bound proves it. The new desk response has reductions_open=false.

Prior open PR13723 contains partial results only; it does not prove the target. Its source is available in scratch for comparison. No prior result is assumed without Lean verification.

Replan 2026-11-25T15:01:09.460249+00:00: geometry partials are now compiled and preserved. General proof routes remain blocked at quantitative minimality/shared-cone accounting. A one-hot-only relaxation has a pen-and-paper small-circuit obstruction, so it cannot prove the desired sharp bound. A new computational strategy searches subfunctions made of3 or4 point stars: a one-gate saving in any such block extends to a26-gate full Fano circuit. status_check owns this distinct search; counterexample continues full-function SAT and circuit_search stochastic optimization.

STOP at15:07UTC: desk returnedHTTP410. Current conclusion: exacttargetunproved; no26gateFano witness. All agents stopped, rootheartbeatstopped. Geometric helpers and nine-gate P5 local-irreducibility example compiled in the named file; these are partial results only.
