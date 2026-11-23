# Full-state Huffman API (fixed radix snapshot)

Use these sources in order:

1. `Huffman982RadixDecoder.lean` (omit its import if already importing Mathlib).
2. `Huffman982StatesAppend.lean.txt`.
3. `lemma982-huffman32-radix-books.lean`.
4. `Huffman982CommonWrappers.lean.txt`.
5. For each case N, `lemma982-huffman32-radix-coreN.lean`, `Huffman982CoreNInputs.lean.txt`, and `Huffman982CoreNStateWrappers.lean.txt`.

The input-literal files are optional if the semantic bridge already defines exactly the same `HuffmanData.cNInputs : List Nat` and `HuffmanData.cNK : Nat`.

All per-core definitions are in `PEqualNP.Outside.L_meta_982_aux.HuffmanData`. The main API is `cNCount : Nat → Nat` and `cNStates : Nat → Nat → List Nat`; its arguments are remaining gate budget and sorted-layer state index. `cNRecords` gives the incoming parent-index/tag pair. State index zero at the maximum budget is the sorted initial input list. States below/above the count are not intended lookup targets.

The stored words use the new bit-sliced encoding. Parent/tag reconstruction performs no symmetry operation. Every reconstructed state is insertion-sorted by its actual raw Nat words; each layer follows the same lexicographic order, so exact raw-key binary search can be used. The input order is original vertex order; `cNRoot` sorts it once.

`Huffman982Radix3StateCache.lean.txt` is an optional alternative. After including it, replace `state cap cNMask cNRoot cNRecords` with `cachedState cap cNMask cNRoot cNRecords cNCount`. It uses three levels of radix32 arrays for state layers. The ordinary wrappers share a lazily decoded 32-record block; both definitions are pure. Kernel benchmarks measured a small benefit for the explicit state array, but they do not establish global caching guarantees.

The canonical manifest records hashes and tested sample points. The standalone checks prove only concrete decoding equalities. They do not prove complete transition closure or any posted lower-bound statement.
