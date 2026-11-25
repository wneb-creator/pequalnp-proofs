# Witness codec prototype

This is a measured candidate-data codec, not a complete Lean search certificate.

The original real weak-case stream is765,028bytes (c539de6a9c37303c1c71a39fcc77010ed72641a74a33afc767d671e89ad0769d). The improved per-node-shortlist stream is394,253bytes (c99a645e1337e3ea0a04cda950552dfad549fd5c8e99be53449eff465c4f7650). Both input files and exact layouts are preserved here. Their semantic boundaries, checker/prior dependencies and rectangle cost proofs remain separate obligations.

The pure Lean LZ decoder uses literal runs and overlapping byte copies. Candidate generation tries512,2048,8192,32768byte independent chunks; all complete streams round-trip in Python. At32768byte chunks, the old stream becomes459,900compressed bytes and920,179bytes of Lean payload source. The shortlist becomes270,165compressed bytes and540,608bytes of Lean payload source. Neither plain LZ payload fits512KiB.

A static packed Huffman tree over the shortlist LZ bytes reduces the actual Lean payload source to457,711bytes (ShortlistHuffmanPayload.lean). The two decoder source files add2,264bytes, leaving64,313bytes below524,288 for every other proof/data/checker dependency. This does not establish whole-source feasibility. An ordinary LZMA reference measurement on the old stream is262,548binary bytes; reference compressors are size comparisons only and have no Lean decoder in this archive.

All four finite equality benchmarks compiled with decide +kernel, with complete empty diagnostic logs and recorded wall times including the launcher:

- Original first2,048bytes,512byte chunks:2.254s.
- Original first16,384bytes,2,048byte chunks:4.403s.
- Shortlist first32,768bytes, one LZ chunk:10.837s.
- Same32,768bytes, one Huffman/LZ chunk:23.643s.

The expected Nat/list literals in these four proofs were separately parsed back to bytes and compared to the exact input prefixes; hashes and module sizes are in kernel-samples.json. Full payload decoding was checked in Python, not in Lean. No complete semantic finite predicate was run on decoded payloads. No extrapolated full-certificate timing is claimed.

Both decoder definitions merely construct candidate data; malformed offsets, truncated bits, unexpected tree paths or exhausted fuel need no abstract correctness theorem. A final consumer must kernel-check the resulting finite witness predicates. Existing finite equality benchmarks establish only their explicit byte outputs. No strings, custom data types, new axioms or native execution appear in the Lean decoder/benchmark proofs. The standalone benchmark modules reuse the same namespace declaration names and should be compiled individually, as recorded, rather than imported together.

The first Huffman compile was started before its generated source existed and failed with a missing-file error; that complete attempt log/status is retained. After generation completed, the decoder and finite benchmark compiled successfully. Production compilation was not affected.

The prototype was bounded to one local experiment; no network, credentials, external service or solver was used. Sources, exact inputs, payloads, complete compile output/status, scripts and manifests are preserved. Independent decoder mathematics reviews are ../review-witness-decoder.txt and ../review-witness-huffman.txt; archive integrity review is separate.
