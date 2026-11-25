# L-meta-2592 orchestration

Lease held only by root. Other agents must not contact desk.
Statement and allowed imports: /tmp/oec/pequalnp-pilot-99/desk-first.json
Exact statement: /tmp/oec/pequalnp-pilot-99/statement.txt
Only allowed project import: PEqualNP.Defs.
Target: no fan-in-two circuit of at most 19 gates containing a NOT computes Petersen edge function. reductions=true, reductions_live=3.
Use scratch under /tmp/oec/pequalnp-pilot-99; put strategy reports in results/orch/lemmas/<strategy>.md. Root consolidates NOTES. Do not edit target Lean file unless assigned.

13:50 UTC findings: existing three reductions fill cap; full proof must tackle 1–4 NOTs after existing >=15 non-NOT certificate. Library agent adapting certificate; reduction agent has 91-line candidate general last-NOT factorization. Root installing official Lean 4.36.0 because no prepared lake or cache exists in supplied environment.

13:54 UTC: stronger existing L_meta_6581 gives >=16 non-NOT gates. Partial16 adaptation excludes >=4 NOTs, remaining1–3. Reviewer independently approved both partials conditional on build; neither contains final posted theorem. Counterexample search includes stochastic full1024 truth-table checking and exact SAT1NOT19 (connected normalized search only, not exhaustive original model proof).

14:06 UTC: target503lines compiles CutLast, monotone endpoint lemmas, unused-gate erasure, connected representative, and essential-NOT boundary witnesses. None closes1–3NOT cases. New sat_encoding agent has compiled direct bounded four-op circuit model and is connecting NOT preservation and CNF.
