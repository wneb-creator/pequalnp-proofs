# Checked restricted cases of L-meta-1735

The two self-contained Lean files in ../lemmas compile with the installed Lean/Mathlib project environment:

- nested_two.lean: Ustar.card <= 4*(size+1), assuming girth at least five, IsLeastAO, TopForm, exactly two junk gates, and a nested junk pair.
- at_most_two.lean: a single universal constant bounds Ustar.card/(size+1) for all such circuits with at most two total junk gates. This combines the nested case with the accepted L1880 internal edge bound for pairwise incomparable junk gates, which also applies to zero/one junk gates.

These are supporting partial results. Neither proves the full posted L-meta-1735 statement; arbitrary three-or-more nested junk gates remain unresolved. They are not new reduction submissions.

Both files received independent source/math/format review PASS. Standalone axiom audits report only propext, Classical.choice, Quot.sound. The successful build and axiom logs are retained here in full.

Source reuse: checked repository L_meta_2074 (support size), L_meta_5242 (four-vertex neighborhood cover for exactly two nested junk gates), R_meta_1882_1 (girth-five neighborhood edge count), and L_meta_1880 from upstream d7dd149881faedf1819d7ca0ca51130327f5a9bb (parallel-junk edge bound). Copied namespaces were renamed to L_meta_1735_aux subnamespaces; no Outside imports are used. All imports are ordinary Mathlib modules plus PEqualNP.Defs.

For final canonical embedding, place the standalone Support helper declaration inside the enclosing auxiliary namespace and write all helper declarations with lemma. The final posted theorem, if later established, must be the sole top-level theorem named for the leased gap. No claim is made that these archive files themselves satisfy a final PR's sole-theorem format.

The JSON/text census records exact checked statements and prevents accidentally dropping case restrictions. Fresh metadata still marks L1768, L1770, L1882, L2076 and L2579 as conjectures.
