# L-meta-1884 orchestration

Own lease de68ce60-fb13-4311-8e7e-e64ffc779aa1 assigned around16:35UTC. Root renews every four minutes. Scratch gap1884/STOP signals withdrawal and all agents must stop. Exact statement/imports: /tmp/oec/pequalnp-pilot-99/gap1884. Only root holds lease and submits.

Goal: arbitrary fan-in-two Circuit with <=18 gates, ten permuted/possibly repeated inputs x6 composed with x2 plus one unary x3(x6 0), cannot compute Petersen edge function. Imports only Mathlib and PEqualNP.Defs. No current proof. Existing checked Petersen normalization and17 non-NOT lower bounds may be reused. Reductions are marked open, but reductions_live=3 already; investigate existing cuts before considering another.

Six routes: library_route searches exact existing theorems/cuts; lower_bound develops input normalization and small-support exclusion; counterexample searches genuine small circuits with the free unary literal; sat_encoding develops exact finite encoding and useful checked lemmas; reduction_strategy seeks mathematical lower-bound strategy and permissible smaller pieces; status_review independently audits claims and incoming proofs. Use separate scratch and notes paths, do not edit named target. Preserve compiling components promptly and notify root. No work on previous withdrawn gaps.
