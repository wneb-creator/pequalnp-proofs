# Petersen search: L-meta-2590

Exact target: no monotone fan-in-at-most-two circuit with at most 19 gates computes the 15-edge Petersen graph function on 10 inputs.

## Existing reductions and their children

The desk reports reductions_open=true but reductions_live=3; the user caps three live reductions per step. No fourth reduction should be submitted.

* R_meta_2590_1 (PR4786): splits after the first AND/OR gate, leaving an18-gate tail and 30 decisive input rows. Children L-meta-5685 (AND) and L-meta-5687 (OR); twins5686/5688. Both positive children remain conjectures with no L_ proof in the repository. Each has a further reduction that merely splits the remaining gates into some AND, some OR, or no gates; no closed substantive branch was found.
* R_meta_2590_932 (PR7763): three normalized semantic-circuit cases with first edge-OR, nonedge-OR, or edge-AND gate. Children7103,7105,7107; all remain conjectures and have no repository L_ file.
* R_meta_2590_491 (PR8191): compress a hypothetical19-gate circuit to a16–18-gate circuit with one modified input, then exclude the AND/OR guard cases on decisive rows. Children7889,7891,7893; all remain conjectures and have no repository L_ file.

Statuses checked in the public content-addressed data feed on2026-11-25, using map overview19017e9fc624 and meta program19f60113d54f. Search index2 lists the exact child IDs under key2590. Public L-meta-2590 record e52ef820c846 still says conjecture. These are snapshots; root owns live desk renewal.

## Promising structural route

Structural agent observed: a live minimal binary circuit with19gates has at most20 input occurrences. If each of the10 variables has at least2, all20 occurrences are inputs and each nonoutput gate has exactly1 reader: the circuit is a formula with at most20leaves.

L_meta_531.lean gives exactly the needed formula lower bound: for every triangle-free,C4-free graphG and monotone DMFormula computing its edge function, there exists a vertex coverT with |E|+|T|<=leaves. Petersen has15edges and minimum cover6, so needs at least21leaves. The checked proof is only454lines/24KB and imports narrow Mathlib modules plus Defs. The complete transplant and Petersen specialization now compile in PetersenFormula.lean (exit 0, empty /tmp/oec/pequalnp-pilot-144/petersen-formula-compile-3.log). Main interface: PEqualNP.Outside.L_meta_2590_aux.Formula.leaves_ge_twentyone, with DMFormula monotonicity and correctness against Formula.target as hypotheses. Structural agent owns converting circuits to formulas and the complementary single-read-input case.

No direct unrestricted Petersen monotone20-gate lower bound was found in the repository. Many checked descendants instead concern the9-vertex deleted graph or circuits with free derived inputs and restricted NOT counts.

## Search coverage

All 712 locally checked L_meta files associated with Petersen by the public search index were inspected at the final-theorem level (scratch all-petersen-finals.json). No unrestricted lower bound of 18 for the 14-edge Petersen-minus-edge graph was found. The deleted/removed indexed candidates L1664, L2496, L5120, L2509, L2191, L2036 and L2040 concern smaller 8- and 9-input cofactors. This is absence from the inspected corpus, not a mathematical impossibility claim.

## Essential input helper (compiled)

PetersenEssential.lean imports only PEqualNP.Defs and compiles with exit 0 and an empty essential-compile-3.log. The generic fold induction proves changing an unread input cannot change circuit evaluation when that input is not the output wire. The Petersen specialization proves output is not an input wire, using singleton false rows; every input is essential, using the three spoke-edge witnesses. The result Essential.petersen_input_count_pos requires only correctness and gives 1 <= (C.gates.flatMap Gate.inputs).count i.val for every i : Fin 10. Essential.target is definitionally equal to Formula.target.

Public child L-meta-7889 exact formal statement is saved in scratch statement-7889.txt; full metadata lemma-7889-public.json. Public record has no imports field; its parent reduction imports only PEqualNP.Defs. No child lease requested.
