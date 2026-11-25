L-meta-2592 orchestration notes

Exact task remains unproved: no fan-in-two AND/OR/NOT circuit of at most19 gates, with at leastone NOT, computes the Petersen edgefunction.
Allowed project import: PEqualNP.Defs. Desk reductions=true, reductions_live=3: no fourth reduction allowed.

20-minute replan (2026-11-25 14:06 UTC)
- Reusable checked upstream bound L_meta_4725: 15 + NOTcount <= size. Original circuit needs at most4 NOTs under budget19, but canonicalization can add NOTs when replacing empty AND, so fixed-NOT search is only a canonical subclass until further normalization is proved.
- Generic last-NOT decomposition is already known as L_meta_8295; our re-derivation compiled and was preserved without novelty claim.
- Three new normalization components compiled and pushed in82ed8f67. Complete legal-final-output composition and exactbudget padding also compile and are being preserved.
- Namedfile partial integration will establish a formal bridge from any posted counterexample to exact19 legal gates on10 inputs plus a freefalse wire. Main no-circuit statement is absent, not assumed.
- Generic91row SAT search timed out without a verdict. Two firstgate cases and exact4NOT case continue; heuristic search found no counterexample.
- Change of emphasis: finish/audit complete normalization, devote searches to long SAT cases, stop repeatedly running unsuccessful heuristics. Any UNSAT result still requires a Lean certificate and the encodedclass proof before a full-gap claim.
- Full local checker loads all Mathlib. Current cache supports project/partial builds; full-cache disk limitation remains unresolved. No checker acceptance is claimed.

Preserved checkpoint commits
652bb90bdc0aeef9508bf733f6139d2e8f0e7faf: known lastNOT component.
82ed8f67d7c9d14e660177b1936c5eeb5754c9e1: normalization components.

Root alone holds, renews, releases lease, pushes branch, and opens any PR. Per-agent source/notes remain in lemmas/; validation.txt records exact artifact hashes and complete compiler outputs.
