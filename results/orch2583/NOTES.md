# L-meta-2583 working notes

New lease assigned at about 2026-11-25 14:43 UTC, after the previous L-meta-2592 lease returned HTTP 410. All old results were pushed first. Root alone manages the lease and git. Six subagents have separate notes files; shared facts are summarized here.

The statement asks for an AO2 read-1 replacement for a projective-plane incidence circuit, with no greater size. Read-1 means one squarefree proof tree per prime implicant, not a globally read-once circuit. Known checked constructions and lower bounds identify the optimal read-1 size as N*(q+2)-1. Thus a q=2 Fano circuit of size26 refutes the statement, whereas a general unrestricted lower bound proves it. The new desk response has reductions_open=false.

Prior open PR13723 contains partial results only; it does not prove the target. Its source is available in scratch for comparison. No prior result is assumed without Lean verification.
