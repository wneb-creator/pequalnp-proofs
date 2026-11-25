# Petersen certificate audit

Read on 2026-11-25 by global_bridge. This is research evidence, not a completed Lean proof.

## Existing checked lower bound

`L_meta_670.lean` proves that Petersen minus one vertex needs at least 16 ordinary
AND/OR/NOT gates. Its `directSplit` uses two finite live-wire certificates:

- `monoRoot`: no monotone binary circuit with at most 15 gates.
- `signedRoot`: no zero-preserving signed binary circuit with at most 14 gates.

The signed primitives are AND, OR, AND-NOT, and NOT-AND. Ordinary NOT gates are
absorbed into wire phases, and their original gate cost supplies the one-gate
difference between the two budgets. L-meta-4033 is another checked proof of the
same nine-input lower bound. The ordinary ten-input Petersen bound at 18 gates,
L-meta-4031, remains unresolved in the inspected repository.

`R_meta_4031_23.lean` explicitly reduces the ordinary Petersen lower bound to this
nine-input bound plus a three-gate false-restriction normal form. That normal
form is still the substantive open part. `ReadersExport.fanout_step` alone does
not supply it: its alternative is a four-gate saving at a true restriction.
For Petersen, a true vertex restriction is OR of its three neighbors plus the
edge function of an induced six-cycle; this has a canonical 11-gate circuit.

## Generator availability and certificate scale

No matching certificate generator was present in the local repository. A complete
recursive tree census of the PR12203 head fork contained 3667 entries and reported
`truncated: false`; it also contained no generator for these live-wire tables.
Its only Python scripts were the unrelated LRAT-link scripts already in the base.

[PR12203](https://github.com/open-goat/pequalnp-proofs/pull/12203) has an empty
description. Its visible checker comments report three exit-124 timeouts, followed
by closure because another proof was merged first.

[PR12680](https://github.com/open-goat/pequalnp-proofs/pull/12680), the checked
L-meta-2446 proof reused by L-meta-670, reports a Windows build time of 19m18s and
an independent kernel replay time of 24m35s, checking 5118 constants. The PR names
PR12203 and L-meta-1667/1674/1677 as sources; it links no generator artifact.

The L-meta-670 tables contain 1471 monotone forest states and 698 signed forest
states, each spread over stored depths zero through six. The checker encodes:

- complete truth tables as `BitVec 512` for nine variables;
- selected Karchmer-Wigderson comparison samples as 152-bit words;
- each stored instruction in 10 bits: two operation bits and two four-bit wire indices.

Adapting to ten variables requires 1024-bit truth tables and regenerated samples,
restriction rules, state tables, symmetry indices, and packed data. Four-bit wire
indices may also need widening if the raw inputs plus stored depth exceed 16.
The search-tree growth and ten-input replay time are **UNVERIFIED**: no generator
or full ten-input certificate was available to run.

## Potential additional reduction

The following argument appears to give signed-binary Petersen complexity at
least 17, but has not been Lean-checked here.

Take a least zero-preserving signed circuit with at most 16 binary gates. If
some input has two distinct readers, fixing it false eliminates those two gates:
each allowed signed binary primitive with a false argument becomes zero or a
copy. The result computes Petersen minus that vertex with at most 14 signed
binary gates, contradicting `signedRoot` after a vertex automorphism.

Otherwise every essential input has one reader. After removing copy/constant
gates, the first binary gate combines two distinct source variables. Each allowed
primitive has three equal entries in its two-input truth table. Since both
variables occur only through that gate, the output has a pair funnel. The checked
Petersen pivotal property excludes this.

If this normalization and funnel argument are formalized, an actual 18-gate
AND/OR/NOT circuit with the free complemented input can contain at most one
ordinary NOT gate: two NOTs would leave at most 16 binary gates. The free
complement of input zero is absorbed into that input's phase. This reduces the
remaining synthesis/rigidity work to zero or one ordinary NOT, but does not by
itself prove the posted 18-gate exclusion.
