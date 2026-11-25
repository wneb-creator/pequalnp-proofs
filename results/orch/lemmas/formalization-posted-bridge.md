The integration is a conditional refutation bridge for L-meta-1479, not an unconditional refutation.

`posted_to_heawood` converts the exact posted 27-gate witness to an accepted Heawood-labeled StrictLive DAG with the same gate count and both quiet raw derivative traces. The ordinary 27-gate lower bound establishes minimality. Destructive normalization is used only for arbitrary competing circuits in the lower-bound argument; the actual witness uses the previously checked direct gate-for-gate conversion. No gate deletion, operand collapse, or trace-preservation assumption enters that conversion.

`posted_to_canonical` then applies an actual graph automorphism, transporting the marked endpoints and both trace functions. It retains the empty ineligible-set case separately because the accepted `canonI` list contains only nonempty independent sets.

`posted_refutation_of_canonical` and `posted_refutation_of_universal` each retain the missing no-double-quiet structural assertion as an explicit premise and conclude the literal negation of the posted existential. A bytewise comparison verified that `Posted1479` and the existential body in both final conclusions exactly match statement.txt, with no changed hypotheses, size, or derivative orientation.

The standalone source copies the accepted L_meta_6659 prefix through its ordinary Heawood lower bound (first 9308 lines), closes the namespace, then appends the reviewed integration tail. It imports only PEqualNP.Defs. Cached development and flattened permitted-import standalone builds both exited 0. Independent source review passed; the matching receipts preserve the exact hashes and complete logs.
