# Pilot 166: L-meta-13150

False: for the monotone six-input f with table 4277075690 * 2^32 + 4276944616: each AND/OR/NOT circuit of fan-in at most two has an AND/OR one no larger

Statement file: /tmp/oec/pequalnp-pilot-166/statement.txt

¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276944616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276944616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))

Only root holds/renews the lease. Agents use distinct scratch Lean filenames and append findings here. Do not edit target file without assignment.

## Independent review 2026-11-25T17:51:41.587786+00:00
The assigned negation is false. Exact table integer is 18369900215343578856. Existing lean/PEqualNP/Outside/V_meta_9933__k9.lean proves AND/OR/NOT minimum 9 (theorem `PEqualNP.Outside.V_meta_9933__k9`, lower helper line 2564). Its witness `PEqualNP.Outside.V_meta_9933__k9_aux.wit` line 2557 has 9 gates, all AND/OR. Python truth-table check over all 64 inputs confirms this witness computes the assigned target. Thus for every HasCircuitSize bound s, existing lower gives 9 <= s and the same monotone witness suffices. L_meta_13031 has a different low word 4277074666 and is not directly applicable. The full existing proof has 2572 lines; if importing its module is not allowed, helpers can be copied/renamed into target own namespace, with helper theorems changed to lemmas under the one-theorem rule.

## Lean strategy / submission route

L-meta-13150 truth table is 18369900215343578856 (hex feeefeeafeecfee8). Its minimal true inputs are pairs {0,1}, {0,2}, {1,2}, {0,3}, {1,3}, {2,3}, {1,4}, {0,5}: graph K4 with two pendant edges. Existing L_meta_13031 uses different low limb 4277074666, so it is not directly this function. Status reviewer located exact table in V_meta_9933__k9.lean.

Submission caveat: outside-guard.mjs lines 159–163 only accepts kind refute when the public gap row itself posts kind refute; absent/check maps to check. authoritative.yml lines 155–158 enforces equality before Lean. Therefore checker refute acceptance of the negation of this prove-kind row is evidence, but does not make its PR eligible. A valid positive proof would require the desk to lease the positive twin L-meta-13149; do not repurpose another lease.

## Independent computational review (circuit_search)

The assigned table equals 18369900215343578856 exactly. Parsed V_meta_9933__k9_aux.wit directly from existing Lean source, independently evaluated all 64 inputs in Python, and obtained that exact table with zero mismatches. The witness has 9 gates, all AND/OR with exactly two inputs; output wire 14. Existing V_meta_9933__k9_aux.lower asserts 9 <= t for every HasCircuitSize 6 f t, where f is definitionally the posted table function (tableIndex unfolds to the same sum). Hence a 9-gate monotone witness works for every general size bound, and the assigned negation is false. Independent witness output: /tmp/oec/pequalnp-pilot-166/circuit-search/independent-witness.json. Lean checking still required for copied adaptation.

Refutation artifact results/orch/lemmas/Refutation.lean contains the existing general-size lower bound and monotone witness, all in L_meta_13150_aux, with final double-negation of the exact assigned statement. Positive twin artifact results/orch/lemmas/Positive.lean uses namespace L_meta_13149_aux and the positive universal statement obtained by removing assigned outer negation. Original source evidence: witness line 2557, upper 2559, lower 2564, combined theorem 2569. Original allowed Mathlib imports restored; only project dependency PEqualNP.Defs. Both scratch files need root build/check and desk statement verification before submission.

## Independent red-team review (2026-11-25T17:53:21.298234+00:00)

Refutation.lean format guard PASS (exit 0), 142395 bytes, regular non-executable UTF-8 file. One final target theorem; exact syntactic negation of saved posted statement. No forbidden raw text or >20-digit numerals. Complete diff against merged V_meta_9933__k9 retained under scratch independent-refutation.diff: substantive mathematical helpers are copied unchanged, with namespace/section names and theorem-to-lemma presentation adjusted. Independently evaluated witness on all 64 Boolean assignments: PASS; exactly 9 gates, all AND/OR, fan-in at most 2. Proof combines general-circuit lower bound 9 with this witness to prove positive simulation, hence refutes posted negation. Still needs local build and kernel checker; desk-kind guard rejects its PR as refute while row remains check.
