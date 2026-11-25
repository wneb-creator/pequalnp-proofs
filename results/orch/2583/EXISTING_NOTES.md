# Existing-results audit for L-meta-2583

- Checked L_meta_7684 supplies a READ1 star-cover circuit of size at most |E|+|A|+|B|-1.
- Checked L_meta_4897 supplies the converse cover budget for an existing READ1 circuit on a C4-free bipartite graph. It requires READ1; it is not an unrestricted monotone lower bound.
- Checked L_meta_7639 specializes the READ1 lower bound using a perfect matching, yielding |E|+N<=size+1.
- General C4-free no-size-loss READ1 normalization is the unresolved L-meta-4895. Its reductions R_meta_4895_1, _215 and _628 all retain an unrestricted matching/cover charging premise; their construction and structured-read1 premises are checked.
- Thus plane normalization reduces to the unrestricted scalar bound N*(q+2)-1<=C.size. For q=2,N=7, a 26-gate monotone Fano incidence circuit would refute the statement; READ1 needs27 gates. For q=3,N=13 the threshold is64.
- Checked L_meta_3706 gives a cover bound with a deficit for edges satisfying Core.ReadTwiceAt. Checked L_meta_3700/L_meta_3653 handle exactly one junk AND under additional lifted normal-form assumptions; a general multi-junk block charge was not found.

## Checked construction partial

`lemmas/existing_star_builder.lean` copies L_meta_7684 under the target auxiliary namespace and adds:

- incidenceEdges_card: degree(q+1) on each line gives N*(q+1) edges.
- lineStarUpper: a correct AO2 READ1 circuit exists with size<=N*(q+2)-1, using all lines as the star cover.
- normalize_of_budget: if N*(q+2)-1<=C.size, the exact requested replacement conclusion follows.

The partial compiled with exit0. Complete stdout/stderr are preserved under logs. It does not establish the missing scalar lower bound, and it does not prove the full posted statement.

Recorded 2026-11-25T14:50:41.477993+00:00

## Checked cyclic Fano lower bound

`lemmas/existing_fano_lower.lean` copies L_meta_7639 under 2583_aux.FanoLower. It proves the cyclic incidence p=l or l+1 or l+3 in Fin7 has21edges, line degree3, unique joins, no rectangles and identity matching. `readOne_lower` proves every correct AO2 READ1 circuit has size at least27; `no_small_replacement` rules out a READ1 replacement of size at most26. Full source compiled exit0, with warnings inherited from the checked source. It does not assert that a26gate correct circuit exists. Full log5 is preserved under logs, and reusable scratch module ExistingFanoLower.olean is available.

Recorded 2026-11-25T14:55:34.985015+00:00
