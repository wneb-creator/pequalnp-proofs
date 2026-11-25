# Independent review: ClosedOrSet

UTC: 2026-11-25T16:41:59.665660+00:00

Verdict: PASS as a dependency-tested helper. Exact source SHA256 `1f45e4239020b1583991a5ed484ea56be723359d71000f8905e8c3df21825ace`, 3896 bytes/84 lines. Author reported Lean exit0; the complete fourth-run stdout has one if_pos deprecation warning and stderr is empty. This reviewer did not rebuild.

`or_read` derives the final value of an OR gate from a true operand using actual circuit semantics and explicit ReadsBack. `closed_true` iterates PB: each selected gate is output or feeds another selected OR gate; ReadsBack makes the successor index strictly larger, so induction on remaining gate positions terminates. This establishes truth propagation along the closed OR set without assuming a graph target or circuit minimality.

`excludes_safe_or` uses PC with an explicitly satisfiable, output-implying operand. Its other operand is true on an explicitly rejected row. PC places the gate in the closed set and the preceding propagation yields contradiction. Both satisfiability and the rejected-row premise are necessary and present. `normalize` instantiates the existing function-generic LiftFix.main at emptyT, returning the exact same circuit function and no larger size. `no_copy` uses an explicit minimum-over-all-equivalent-Monotone2-circuits premise and the checked deletion transformation: an earlier wire semantically equal to a gate output makes that gate deletable, contradicting minimum size.

Imports are existing LiftFixMain and LowMergeWires helpers, so this file is a dependency test and cannot be submitted under the job's Defs-only import restriction without assembling its dependencies. Namespace and source syntax are otherwise clean: no options, attributes, strings, forbidden constructs, new axioms, unsafe declarations, or secret-like content. The file is below512KiB. No full relaxation lower bound or L-meta-1884 theorem is claimed.
