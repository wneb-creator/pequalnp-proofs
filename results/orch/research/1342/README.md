# L-meta-1342 research handoff

The posted21-gate circuit remains unresolved. The proposed reduction separates a generic three-gate prefix constructor (closed in Lean in ../../lemmas/PrefixConstructor1342.lean) from a conjectural18-gate continuation. No normal-form completeness claim is made. The second child restricts to exactly two junk AND gates, as assigned by shard0.

A nearby22-gate construction with the proposed prefix has a checked19-gate continuation and exact junk set {2,7}; see ../../lemmas/TwoJunk22Stratum1342.lean. The standalone compile log is complete and empty on exit0. There are five externally checked first-unit seeds of this size. Searches did not produce a valid21-gate witness. The best21-gate candidate accepts four additional inputs; it is explicitly an invalid near candidate.

Directories retain complete scripts, diagnostics, outputs and findings. direct contains algebraic gadget enumeration. sibling contains the closed Lean components and complete trial logs. structural contains the graph sieve, public source census and referenced sources, with authors and unverified claims distinguished in STRUCTURAL_REPORT.md. searches contains genetic and symbolic runs with a hashed manifest; counterexample contains bounded SAT repair experiments. Timeouts are not impossibility results. UNSAT results apply only to the stated encodings and neighborhoods.

Only the final R_meta_1342_46.lean file is proposed in the PR. These research artifacts are retained in checkpoint history on the same branch.
