# L-meta-2592 orchestration

Assigned Petersen graph lower bound for circuits with NOT; at most 19 gates. Only PEqualNP.Defs project import. Three live reductions already exist.

Strategies: counterexample search; NOT-elimination/lower bound; existing reductions and library search; toolchain setup. Each agent writes its named note file here and communicates findings. Final proof must be exactly lean/PEqualNP/Outside/L_meta_2592.lean; only root edits it.

Progress: L_meta_6581 gives full Petersen binary floor16 and includes deleted-Petersen free-complementation floor15. Two independent reviewers approved adapting it for >=4-NOT exclusion; named file currently holds only this partial. Remaining original cases:1..3 NOT. Root/descendants/lower_bound developed first-gate retention: retained input plus new constant after first AND gives binary floor18; first OR gives17. Duplicate nonconstant wires cannot generally be charged as constants. SAT search is witness-only; UNSAT is not a proof of the unrestricted statement.
