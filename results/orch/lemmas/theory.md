# Theory strategy — L-meta-2592

## 2026-11-25 initial audit

- The exact circuit model is the straight-line list in `Defs/CircuitLowerBounds.lean`: every gate appends one wire; invalid indices read false; NOT uses only its first operand. `FanInTwo` restricts the operations to AND/OR/NOT and the list length to at most two.
- The parent lower bound is still a hard open problem; even the monotone sibling L-meta-2590 has several live reductions. There is no obvious general monotone-elimination theorem to apply.
- `Outside/L_meta_4725.lean` (3224 lines; 142188 bytes) proves the exact useful bound `15 + PEqualNP.NotBracket.notCount C ≤ C.size` for the full ten-vertex Petersen function. The generic portion counts at least six branch wires using twin-class deletion of the graph and combines this with a binary-gate accounting bound. Thus every circuit of size at most nineteen has at most four NOT gates.
- The full-Petersen version is also repackaged by `L_meta_6194.lean`; `L_meta_8127.lean` adds one prescribed first gate. The many similarly named Petersen certificates mostly concern the NINE-vertex graph obtained by removing one vertex, so their 13/14/15/16 lower bounds should not be confused with the ten-input task.
- The three checked reductions for our task are `R_meta_2592_271` (binary floor plus few-NOT exclusion), `R_meta_2592_318` (cut at last NOT plus suffix separator), and `R_meta_2592_408` (normalization plus finite legal-circuit lower bound). There is currently no reduction slot.
- Reduction agent identified remaining open children L-meta-4727 (one through four NOT), L-meta-7391 (normalized finite bound), L-meta-8297 (last-NOT separator).

## Important dead end

Monotonicity alone does not imply that an individual NOT gate can be replaced by one constant. For instance, majority of a,b,c can be represented as `ab OR ac OR ((NOT a) AND (a OR bc))`; the NOT is essential under replacement by either constant. This representation is larger than an ordinary monotone majority circuit, so it is not a size counterexample, but it invalidates the simplest NOT-removal proof.

## Potential computational route

For a size-19 search it is enough to consider one through four NOT gates after proving/copying the checked binary floor. A small initial truth-table constraint set is the empty assignment, all ten singleton assignments, and all forty-five pairs: the target is true exactly on the fifteen edge pairs. UNSAT on those 56 rows already suffices for a lower bound. A SAT result can be tested on all 1024 rows and counterexamples added incrementally.

## Independent partial review (2026-11-25)

Reviewed `reductions_many_not.lean` against checked upstream `L_meta_4725.lean`. Changes are a namespace rename, renaming the original theorem to helper `binary_floor`, and a five-line arithmetic corollary `many_not`. The corollary follows from 15 + notCount ≤ size ≤ 19 and notCount ≥ 5. File has 3229 lines, 147572 bytes, no executable bit, allowed imports, no forbidden `_root_`/quotes/sorry/axiom/native_decide tokens, four allowed local-simp attributes, and two allowed limit options. This is a valid partial candidate once Lean compiles it; it is not a complete proof of L-meta-2592. For eventual PR, move the two fully-qualified helper lemmas inside the helper namespace and add the exact posted theorem as the last declaration.

## LRAT route and prepared formal component

The NOT-capable encoding is `PEqualNP.Library.LRAT.LinkN.enc2`, not the monotone-only `PEqualNP.Defs.LratEncoding.enc2`. `notes/data/lrat-link/gennot.py` mirrors the former. Existing LinkN/LinkN2 proofs establish completeness of padding, last-output, used gates, ordered sources, no double-NOT gates, and lexicographic ordering of adjacent independent gates. The normalization may erase NOT gates, so requiring a positive NOT count in the final normalized CNF needs a separate preservation argument. The unmodified encoding avoids that issue and an UNSAT certificate would establish the stronger full size-19 lower bound.

Prepared `theory_lrat.lean` from the checked library code (Checker, the needed prefix of Shannon, LinkN, LinkN2): approximately 95 KB, 2236 lines. Imports only Mathlib.Tactic, Mathlib.Data.Tree.Basic, and PEqualNP.Defs. All helpers are inside L_meta_2592_aux. Local width-discharge macros were expanded inline; comments removed; helper theorems spelled lemma. The private trie datatype was replaced by Mathlib's BinaryTree (Option Nat), which has matching constructors/recursor; the Model.pad decision instance was eliminated by making pad reducible. The remaining three structures Model, Valid, NF currently require manual-format handling; they can be rewritten as a product and conjunctions if needed after baseline compilation. Compilation awaits the restored cache.

The checker evaluates LRAT via `checkW_sound` and `decide +kernel`, not native code. Packed numeral tokens and optional segments are supported. The baseline leaves about 400 KB for a certificate under the 512 KiB limit, but certificate size for the 19-gate problem is not known. The existing P4Not trial proves a much smaller four-input three-gate UNSAT with 159 LRAT steps/1893 hints; it is not evidence that the Petersen certificate will fit.

## Independent boundary artifact review

Reviewed semantics_boundary.lean logically and verified its data independently on all 1024 assignments: fifteen maximal negative masks are exactly the maximal independent sets; their downward closures cover all 76 negative assignments. Fifteen minimal-positive edge masks cover every positive assignment. The sole-NOT separator proof is sound: the monotone prefix must be true on some maximal negative assignment and false on some minimal positive assignment if both constant replacements change the output. This remains a necessary condition, not a gate-count lower bound.

## Stop on lease withdrawal

Root reported HTTP 410 on renewal at 14:39:36 UTC, confirmed by the diagnostic call around 14:40 UTC despite an earlier returned expiry of 14:54 UTC. Stopped proof and compilation work immediately on instruction. Preserved the already-written `theory_lrat_products.lean` variant (96802 bytes, 2238 lines), replacing the remaining Model/Valid/NF structures by standard products and conjunctions. The variant has not been fully Lean-compiled; only its isolated product/projection interface was checked with the installed core Lean. The original `theory_lrat.lean` likewise awaits full compilation. No complete gap proof or LRAT certificate was obtained by this strategy.
