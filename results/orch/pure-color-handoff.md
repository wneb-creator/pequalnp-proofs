# Pure-color handoff

Updated 2026-11-24T19:27:16.019831+00:00. This is a checked local result, not a proof or refutation of L-meta-2584.

## Latest checked result

`results/orch/lemmas/PureColorAlias.lean` imports the frozen main proof file and includes all required new components. It compiled with pinned Lean, exit0, empty stdout/stderr (`pure-color-alias-001`). Frozen SHA256: `4518980ee4ed024eef1f75894ea71ffe85ac16d1e1c18aca1a87dd3cb8d09805`; 482 lines,22491 bytes. The complete source and author compiler logs are archived. Independent review passed: review-pure-color-alias.txt, including compilation and standard-axiom audits of all ten lemmas; factor/wire components also passed review-pure-color-factors.txt. It remains outside the main file because of the source budget.

`PureColorFrontier.erase_two_dirty_pure_colors` constructs a STRICTLY SMALLER exact AO2 circuit when: the graph is bipartite and C4-free; C is TopForm and only G/H can be dirty; both are dirty; G=(OR A) AND (OR B), H=(OR C) AND (OR D), all four factors are genuinely OR-only; A,B,C lie on the point side and D on the line side; |A intersect B|>=2; and the Boolean product G*H is below the graph function. It permits arbitrary shared uses of these gates and OR factors. Thus this configuration is impossible in a least circuit.

The proof chooses one existing G operand E. Dirtiness of H and product soundness force an A/B-covered line; C4-freeness makes that center unique because A intersect B has at least two points. E*H is sound, and E is adjacent to every singleton input accepted by any opposite clean-top operand. Other opposite AND frontiers are necessarily H. Replacing G by E therefore remains sound at every affected AND frontier, even through shared OR contexts; the replacement increases values, so old true outputs survive. Deleting the resulting alias saves one gate.

Earlier `ColorErase.least_guarded_or_pure_side` removes mixed line inputs from H's first OR operand when G already has two pure-point OR operands, H has empty singleton support, its second operand is pure-line, and its first operand contains a point. This now combines with the new erasure once the product-soundness and common-intersection premises are supplied. These hypotheses remain explicit.

## What is proved versus what still needs extraction

- Least-circuit and TopForm normalization are checked. Zero/one dirty gate, or at most one dirty ancestor per top, give checked read2 conclusions. `two_dirty_in_some_top_of_not_read` finds two dirty ancestors of a top in a non-read2 circuit.
- For an EXPLICIT opposite-operand four-clause configuration, the checked word/signature bridge turns a failed joint read2 witness into an exclusive 3/1 or1/3 endpoint signature. Four-clause double-star classification, CommonLine replacement, private alias-plus-star repair, and the new pure-color erasure each have checked, stated premises.
- There is no checked theorem saying these premises exhaust every least circuit with at most two dirty gates.

The remaining <=2-dirty case split is:

1. **Comparable dirty gates:** G lies in H's cone or conversely. Four pure-OR factors cannot simply be assumed. Existing guarded/choice erasures apply only when their reader and soundness premises are established; no general nested-case extraction is proved.
2. **Incomparable dirty gates:** first extract an actual bad-edge top whose two operands use the two distinct dirty gates. Merely finding both dirty gates somewhere in a top's cone does not establish this opposite placement; they may occur in the same OR region. Under suitable placement, OR purity of their factors follows from TopForm and absence of further dirty ancestors, but the complete bridge is not yet packaged.
3. **Four-clause orientation and support:** the pure-point and pure-line clauses can belong to the same dirty AND or to different dirty ANDs; swapping operands is allowed, regrouping clauses is not. Mixed parts, singleton-empty cases, and literally shared OR roots must be routed to the exact checked interface. CommonLine and private-star repairs have additional center/private-reader premises, and the new color erasure assumes G's two operands are already pure-point. No exhaustive routing proof is present. Both-empty singleton support is likewise not discharged by citing the new theorem, whose G support is nonempty.

These are missing proof bridges, not claimed counterexamples. A remaining case may turn out impossible; that impossibility must be proved rather than assumed.

## Unrestricted posted statement

The posted theorem allows arbitrarily many dirty AND gates. The checked non-read2 extraction only finds two inside a top; it does not say that they are the ONLY dirty gates globally, nor that other dirty frontiers can be ignored. All new global sharing proofs use the only-G/H hypothesis essentially. Even a complete <=2-dirty normalization would therefore need a further extraction/induction or replacement argument covering arbitrary dirty count. No such argument has been established, and no full-gap theorem, checker acceptance, or authorized reduction should be claimed.
