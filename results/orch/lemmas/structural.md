# Structural route

2026-11-25: inspected CircuitLowerBounds and MetaComplexity definitions. Circuit semantics are sequential, missing reads false, fan-in at most two, only AND/OR/NOT. No loophole found. The gap allows arbitrarily many NOT gates (presence, not exactly one).

Petersen graph is triangle-free and C4-free, has 15 edges and vertex-cover number 6. Its usual monotone edge-function construction gives an UPPER bound of 20 gates: 15 - 6 = 9 OR gates inside stars, 6 AND gates, and 5 output OR gates. A lower bound for arbitrary circuits does not follow from the monotone bound: negation can change circuit sharing and cancellation.

Checked source L_meta_4725.lean gives 15 + notCount(C) <= size(C). The 3224-line proof counts six required first branching groups using graph twin classes; then binary gate count >= input count - 1 + groups = 9 + 6 = 15. This restricts a 19-gate counterexample to 1--4 NOT gates. It does not establish the desired 20-gate bound.

The three live reductions are R_meta_2592_271 (binary bound plus 1--4 NOT exclusion), R_meta_2592_318 (last NOT cut plus separator bound), and R_meta_2592_408 (normalization plus finite normalized circuit bound). Agent finite_bound is handling last-NOT cut, so this route avoids duplicating it.

An attractive but unsupported shortcut would claim every monotone graph function admits free NOT elimination. This is not established by the definitions or local library and cannot be assumed. One-NOT multi-output monotone elimination is explicitly suspected false in the user special task. Single-output structure needs a separate argument.

Correction: the 20-gate monotone lower bound is itself open (L2590). Star-cover size is only an upper bound for unrestricted monotone circuits. A normal-form theorem turning all monotone circuits into star-cover circuits cannot be assumed.

## Checked partials (2026-11-25 14:15 UTC)

- `/tmp/oec/pequalnp-pilot-109/structural/Endpoint.lean`: 82 lines, checked with `lake env lean`, exit 0, empty final log. Generic monotone wire/evaluation preservation and impossibility of negated monotone circuit false-at-zero/true-at-one endpoints.
- `/tmp/oec/pequalnp-pilot-109/structural/BranchBudget.lean`: generic tight branch-slot counting lemma, checked, exit 0, empty log. If list length equals distinct wires plus branches and each branch occurs at least twice, every branch occurs exactly twice and every other wire once.
- `BranchCovered.lean` / `BranchCovered-snippet.lean`: CHECKED exit 0, inherited source linter warnings only. Uses checked roots-required result with an erased branch to show a least Petersen circuit with at most 15 binary gates has a nonempty first-input class at EVERY branch.

## Equality-case consequences

A normalized minimal 19-gate counterexample with four NOT gates must have exactly 15 binary gates. There are exactly six branch wires, every branch is read exactly twice, and all other nonoutput wires exactly once. This follows by equality in the checked slot-count inequality. An internal shared wire reached only from already-branched inputs would have empty first-input class and hence be impossible (formal snippet pending).

Do not transfer the fanout-two constraint naively to a signed circuit after collapsing NOT gates: a source can be read positively once and negatively twice. In a signed model, require positiveUses(source) + indicator(negativeUses(source)>0) <= 2 and negativeUses(source) <= 2 for the exact-four-NOT case, with output handling separate.

## Restriction recurrence attempt

Implemented exhaustive recursive first-gate elimination lower bound on all restrictions (`restriction_bound.py`). Generic controls remove two gates for nonconstant cofactors, noncontrols one; base support lower bound n-1. Petersen result only 11, cofactors 9, so this simple route is substantially weaker than existing15. This is a computed exploration only, not a checked theorem.

2026-11-25 14:21 UTC: BranchCovered checked. Every branch has a first-input ancestor in a least Petersen circuit with at most15 binary gates. UnaryBranch.lean also checked: unique-flow path cannot reach a unarysuccessor of an already-stopped node. Consequently a NOT branch cannot have an already-branching operand. Together with exact_branch_reads, collapsed signed fanout is at mosttwo in the15binary case (the potential onepositive/twonegative exception is now excluded). Fullcircuit NOT linkage remains to be written if used for a formal global certificate.

Explicit six-round maximal active-twin sequence: roots0,1,3,7,8,4; classes{0},{1},{3},{7},{8},{4,6}; newly isolated after rounds4,5,6 are respectively{2},{5},{9}. Before the final round, vertices4 and6 both have residualneighbor{9}. First nontrivial active twinclasses appear only after four rounds. Distinguish active maximalclasses from actualfirst-inputclasses, which may also contain already-residual-isolated vertices.

## Stronger topology constraints under test

`BranchLocal.lean` (separate stable revision) adds: every internal branch in a least15-binary Petersen circuit reads at least one nonbranch wire; hence a unarygate wire and its operand cannot both branch. `FreshCount-snippet.lean` is the explicit size-independent corollary that at least six branches have a first-input ancestor. Both are short consequences of the checked cover-count theorem; BranchLocal is CHECKED exit0 with inherited linter warnings only; FreshCount has been handed to root as untested for a combined build.

For b binary gates, total fanout excess is b-9, so the sum of (fanout excess above2 among branches) and (number of empty first-input classes) is at most b-15. In particular the16-binary search can allow only one unit of either defect. A source shared positively and negatively, whose NOT wire is also shared, creates an empty first-input class at that NOT wire. This gives the cheap search constraint expandedBranchCount - doubleNeg >=6, without computing every class mask.

## Signed-search audit

Reviewed finite/synth_signed.py read-only. The first-input mask propagation and residual-twin tests match the checked topology results after canonical NOT expansion. Independence of a nonbranch mask follows because it is a subset of the eventual boundary class along its unique forward path. A future formal signed-model bridge must explicitly justify banning a gate that reads both a source and its complement: it computes a constant and should disappear by minimal constant propagation, but predecessor-Nodup by itself does not exclude these two distinct expanded wires. Duplicate NOTs and NOT pairs should similarly be eliminated using existing alias normalization. The searches remain computational evidence only until this bridge and solver certificates are checked.
