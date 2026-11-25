# Pilot111 outcome

The posted gap L-meta-2592 remains unproved. No proof PR was opened.

The portable checked partial is `lemmas/PetersenPartial.lean` (4889 lines,299494 bytes). It proves that every fan-in-two AND/OR/NOT circuit computing Petersen has at least17 AND/OR gates, in addition to its NOT gates. Thus a circuit of size at most19 with at least3 NOT gates is impossible. `TightBudget.lean` further fixes the remaining at-least-two-NOT case to exactly19 total gates,2 NOT gates and17 other gates, with an extracted normalized derivation beginning with OR. One-NOT and two-NOT circuits remain unresolved.

Validation:
- `lake exe cache get` succeeded for the pinned Lean4.36.0/Mathlib environment.
- `lake build PEqualNP.Defs` succeeded (5147 jobs).
- `lake env lean ../results/orch/lemmas/PetersenPartial.lean` succeeded; complete output is in `petersen-partial.stdout` and `petersen-partial.stderr`.
- The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; full output is in `combinatorial-axioms.stdout`.
- Independent review passed for each preserved checked component; scope and hashes are in `REVIEW.md`.
- The complete posted theorem was not produced. The named-module build and `tools/check-lean.mjs` for that theorem were not run. No full-proof cleanup pass was applicable. Portable partial line count before/after:4889/4889.
- Searches produced no fully validated counterexample and no complete UNSAT certificate.

The desk advertised lease expiry14:54:27 UTC, then returned HTTP410 at14:38:04 UTC. Its exact body was:

    {"error":"no such live lease: it expired or was released. Ask /desk/next again."}

The complete retry headers and body are preserved in `desk-410-response.txt`. All proof/search work stopped, and checked work was pushed before re-requesting. Both recovery calls returned the same pre-existing L-meta-2583 lease with this exact message:

    you hold 5 gaps, the most one handle may hold at once; release one to get another

No distinct owned lease was obtained on the permitted retry. The user requires stopping in this situation. L-meta-2583 was neither worked nor released. This pilot sent no release request for any lease. Desk null responses:0.

Sub-agents: 7 — checker/diff review, combinatorial proof, counterexample search, finite certificates, environment setup/gate elimination, negation theory, and a fresh gpt-6.2-astra strategist.

TIMING total=42 subagents=7

Acknowledged message:msg-5c7918d273d5f8de4a6f018e
