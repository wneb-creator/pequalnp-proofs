# Independent review: ClosedRelaxOr

UTC: 2026-11-25T16:45:23.516417+00:00

Verdict: PASS as a conditional dependency-tested actual-circuit exclusion. Source SHA256 `feba4203e7cca2b0460f374403fe8cdc8413174043edacbc72ae4ac1737b7c99`, 3282 bytes/68 lines. Author reported Lean exit0; complete1884-closed-relax-third stdout/stderr are empty. This reviewer did not rebuild.

prefix_value proves persistence of any wire already present before the chosen gate, using append-only evaluation. sole_or_impossible takes an actual OR[t,a] decomposition, explicit a≠t and absence of rawt from both surrounding gate lists, output≠t, Monotone2, ReadsBack, global equivalent-circuit minimality, and the complete PA/PB/PC fixed-point assumptions. It also explicitly supplies the exact false cofactor, positive acceptance, accepted exceptional277 row and rejected singletont, for t2 or8.

ReadsBack bounds the partner to the prefix, allowing SoleReader.partner_independent and factor_or to discharge the abstract safety theorem's hypotheses. Global wire monotonicity provides partner monotonicity. partner_safe gives partner≤target; positive acceptance gives target≤G. ClosedOrSafety then handles either satisfiable safe partner (closed OR-path contradiction) or unsatisfiable partner (minimality/copy deletion). The singleton input wire is evaluated directly, so the contradiction is on an actual rejected row.

This closes the semantic sole-OR application without presuming a graph-exact global function. It does not establish the structural decomposition, minimality, fixed point, row hypotheses, or the reader-count bound for arbitrary candidates. The imports ClosedOrSafety, SoleReaderFactor and StrongRelaxOrSafety are scratch proof dependencies and would need assembly under allowed final imports. Correct namespace and no options, attributes, strings, forbidden constructs, new axioms, unsafe declarations or secret-like content; below512KiB.
