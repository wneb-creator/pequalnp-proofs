# Lower-bound progress for L-meta-1884

All results below are partial progress; the posted universal exclusion at18 gates is not proved.

Checked components:

- Unary17Check.lean: for arbitrary map of the10 variables and arbitrary free unaryh(x0), correct FanInTwo computation requires17 + paidNOTcount ≤ size. This is a dependency test importing the previously checked Binary17 certificate. Defs-only Unary17Standalone.lean is generated but not yet checked.
- MonoBase.lean (orch2590): the pruned nine-variable monotone cofactor certificate, including actual Lower false16, compiled standalone and exported under the current1884 lease. Complete logs are mono-base-checked.stdout/.stderr.
- MonoExtensionCheck.lean: ordinary monotone Petersen size≥18 and normalized firstAND size≥19, importing MonoBase. Complete logs mono-extension-checked.stdout/.stderr.
- Unary18Check.lean: arbitrary map and free unaryh(x0), Monotone2 computation requires size≥18. This imports the checked MonoBase and uses positive sensitivity to force rawx0 when free¬x0 is live, then charges both constant roots under x0=false. Complete logs unary18-checked.stdout/.stderr.
- ZeroNot.lean: zero NOT count plus FanInTwo implies Monotone2; combines the preceding two floors into total size≥18. Complete logs zero-not-checked.stdout/.stderr.
- ReaderBound.lean: Monotone2 constant propagation yields16+effectiveReaders≤size from the actual9input monotone cofactor lower16. The two unscoped options from its first draft have been removed; the corrected source compiles with default limits. Corrected complete logs reader-scoped-checked.stdout/.stderr.
- NineCircuitFloor.lean and ConcreteReaderBound.lean (lean_setup): public Reach compiler discharges that cofactor premise and concludes at most2 effective readers at size≤18. Independently reviewed by lower_bound.
- GeneralReaderBound.lean: the same16+effectiveReaders inequality for arbitrary FanInTwo, conditional on total9input cofactor lower16. Complete logs general-reader-checked.stdout/.stderr. The signed semantic bridge and concrete general reader wrapper are now checked by lean_setup, proving at most2 effective readers for every FanInTwo candidate of size≤18.

ReaderStandalone.lean combines the checked monotone components under only Defs. Its first build was deliberately interrupted with exit130 after independent review found the two global option lines; logs are preserved as reader-standalone-interrupted.*. The corrected assembly is pending full compilation while the stronger general assembly is prepared.

GeneralReaderBase.lean retains both signedRoot14 and monoRoot15 from L4332, with safe lexical pruning reviewed by status_check. It is505234bytes, SHA2568242ee789c29d292de4d5c50bde66241f8de54356a1df1ac9ad6f559531604dd, retaining the needed isNot definition. It has not separately compiled. Both modes can share one finite certificate, avoiding duplication of Binary17.

The exact18 cases remain open. All currently checked models permit nullary/unary gates and invalid/default reads as the posted Circuit semantics require.

GeneralReaderStandalone.lean is the stronger final assembly currently building: both certificates plus shared mode compiler, general contraction, and concrete reader bound. It is523379bytes, SHA256fe3aba339859099b2b5f38b9ad44ab8b41f5072079b12cf7d059160e9104d55e. Ten collision-free helper renames save4745bytes, with an exact reverse-token roundtrip verified by its generator. Independent assembly review passed. The full build began after the16:12:13 lease renewal and PASSED exit0 at16:34:43UTC. Complete logs are archived as general-reader-standalone-checked.stdout/.stderr (warnings only; stderr empty). The exported olean is also present.

OneGateAfterNot.lean separately checked the functional core of the penultimate-NOT pruning argument; no circuit-index or deletion bridge is claimed. Independent review passed. A512-assignment Python obstruction in two_and_both_triads.json shows that both unsafe triads plus productive edge-pairs still permit a2AND auxiliary function, so semantic arguments alone cannot strengthen its AND floor to3.

A fast independent Python XOR polarity realizer is archived as polarity_realizer.py. It constructs at most one paidNOT for a signed trace with one free complemented primary. Tests passed1000 random traces (8644 exhaustive truth rows for641 realizations) and200 cross-checks against exhaustive output-polarity enumeration. This is search tooling, not a Lean proof or a counterexample.

## 16:46 UTC — Eight-variable floor checked

`lemmas/EightExtension.lean` (151 lines, 6371 bytes, SHA256 `32c56c28b9d4ed667b887aa8a8bdf0a07642cad0a349c6f850e411a8b4eacbd2`) passed Lean with exit 0 importing the fully checked `GeneralReaderStandalone`. Its `eight_floor` proves every FanInTwo circuit for the Petersen graph with original vertices 0 and 3 deleted has at least 12 gates. The proof remaps the eight inputs into the known nine-input cofactor and restores the deleted degree-three vertex with four gates. Default reads and output validity are handled explicitly. Complete logs: `eight-extension-checked.stdout/.stderr`. This is a dependency check, not an independently assembled Defs-only file.

## 16:50 UTC — Eight-input restriction and unique reader checked

`RestrictionEight.lean` (127 lines, 4895 bytes, SHA256 `fc349a6226f76fc768893622c3e1e93dd19d6cbfe3bd7089adccddb7573c0690`) passed and exported its olean. For a monotone nine-input circuit correct on the input2=false cofactor, it proves `12 + count(raw2 reader gates) ≤ size`. The input map is `[wire0,wire1,false,wire2,wire3,wire4,wire5,wire6,wire7]`. `compiled_floor` also exposes the lower bound12 for the actual eliminated circuit, supporting the separate two-gate deletion lemma. Complete logs: `restriction-eight-checked.*`.

`UniqueReader.lean` (71 lines, 2508 bytes, SHA256 `a43f943861d9971e1c06f2ed36dc1d84243f0299478f8263e18772fd82c5f030`) passed and exported its olean. It converts count≤1 plus existence into an exact prefix/reader/suffix split with no other raw2 reader. Complete logs: `unique-reader-checked.*`.

## Remaining whole-gap obstruction

No full L-meta-1884 proof has been derived. The incidence bound on uniquely read nonzero inputs and paid-NOT fanout does not by itself force two sole input readers to be direct AND filters of the NOT output. Ordinary sole AND readers and larger OR partners remain possible topologies. For a sole positive reader AND(v,A), graph correctness forces A to accept all three neighbor singletons. This gives two OR operations along the singleton paths, but proving those operations cannot also help the 16-gate cofactor requires a genuine sharing lower bound; previous local pivotality and no-garbage shortcuts do not establish it. A potentially useful finite strengthening is a cofactor floor16 even when a nonedge neighbor-OR is supplied free. This is a proposed route, not a proved fact.
