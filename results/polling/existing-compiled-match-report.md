# Existing checked-result match search

Read-only inspection; no active lease and no proof or Lean source created.
Public snapshot generated 2026-11-25T15:28:15.485Z.

Finding: no open posted statement was found that is literally or definitionally the statement of one of the frozen compiled helpers inspected. No candidate currently qualifies for `have=proof`. Pending Floor17 and Floor18 assemblies were excluded entirely.

The second pass also considered immediate compositions without a new mathematical lemma. No qualifying open target was identified in this pass. This is a bounded discovery result, not a claim that every public statement has been exhausted.

## Closest exclusions

- [L-meta-1015](https://data.pequalnp.com/data/lemma/L-meta-1015.e27141d60521.json), status conjecture: `Petersen two-drop`. Posted target saves four gates for arbitrary FanInTwo circuits. The frozen helper saves two gates for monotone circuits.
- [L-meta-397](https://data.pequalnp.com/data/lemma/L-meta-397.b8870913d081.json), status conjecture: `ConstantReadersStageChecked`. Posted circuits use arbitrary two-input Boolean operators in BinaryCircuit. The frozen simplifier is for Circuit with AND/OR/NOT gates.
- [L-meta-399](https://data.pequalnp.com/data/lemma/L-meta-399.3482d046954b.json), status conjecture: `ConstantReadersStageChecked`. Posted replacement uses BinaryCircuit and a stronger arbitrary-operation representation; no literal theorem or definitional interface match.
- [L-meta-422](https://data.pequalnp.com/data/lemma/L-meta-422.e3a0d065ad21.json), status conjecture: `UniqueReaderChecked`. Posted target derives an AND partner factorization and independence under consumed-read semantics. The helper only propagates equalities in CleanL circuits.
- [L-meta-423](https://data.pequalnp.com/data/lemma/L-meta-423.616617e2ae1a.json), status conjecture: `LeastLivenessChecked`. Posted target forces AND-only usage of an input reader in a least arbitrary circuit, stronger than liveness.
- [L-meta-4383](https://data.pequalnp.com/data/lemma/L-meta-4383.98c00f3f9ffd.json), status conjecture: `PrimeReplacement`. Posted target is a graph-specific FactorSubst.substReads rewrite. The checked semantic prefix/suffix replacement does not already provide the needed substitution and graph bridges.
- [L-meta-4748](https://data.pequalnp.com/data/lemma/L-meta-4748.d03474bdf72a.json), status conjecture: `PrimeReplacement`. Same substitution-interface mismatch for the star-form rewrite. Additional mathematical bridge not already compiled.
- [L-meta-3722](https://data.pequalnp.com/data/lemma/L-meta-3722.70e32618fd7b.json), status conjecture: `LeastLivenessChecked`. Posted target jointly normalizes lift-fixedness, AND usage, dead gates and double rereads. Liveness alone covers only one conjunct.
- [L-meta-2425](https://data.pequalnp.com/data/lemma/L-meta-2425.116ef2abe8f0.json), status conjecture: `PetersenReadOne`. Posted target is a general incidence read2 bound, not the checked read1 no-four-cycle theorem.
- [L-meta-1882](https://data.pequalnp.com/data/lemma/L-meta-1882.90e440f6d4ef.json), status conjecture: `SingleLevelChecked`. Posted TopForm case assumes at least two junk gates and comparable junk gates, whereas the helper requires junk empty.
- [L-meta-2704](https://data.pequalnp.com/data/lemma/L-meta-2704.3b92fd2a6cd1.json), status conjecture: `SingleLevelChecked`. Posted G11 inequality assumes exactly two comparable junk gates; the empty-junk hypothesis is absent.
- [L-meta-4704](https://data.pequalnp.com/data/lemma/L-meta-4704.50c4f3851f39.json), status conjecture: `SingleLevelChecked`. Posted minimal plane-incidence target has no read1 or empty-junk premise.

## Scope and limitations

Search used the public meta program map and inverted term shards for Petersen, read/readers, top form, junk, boundary, constants, least circuits, primes and related terms. Existing saved node payloads retain the exact formal statements. All eight open library-program nodes (113,119,120,121,123,124,125,126) were outside relevant circuit/read/Petersen/prime/junk indexed terms. Three old meta node payloads (71,72,73) were UNVERIFIED because their advertised hashed public URLs returned non-JSON Not Found pages; no mathematical conclusion is based on those pages.

Compiled sources used as the comparison catalog include MonoFirstChecked, MonotoneTwoDropChecked, MonotoneResidualChecked, UniqueReaderChecked, ConstantReadersStageChecked, LeastLivenessChecked, SmallCircuitStructureChecked, PetersenReadOne, PetersenReadOneEdges, PetersenBoundary.v2.checked, PetersenCNF, SingleLevelChecked, PrimeReplacement, BoundaryReplacement and DeletePrimeDeadChecked. The independent counterexample-agent bounded read1/composition check also found no qualifying open target. Its open Petersen/read intersection was only L2112/L2113, L2311/L2312 and L3584/L3585, all nine-input reader-budget statements. Petersen/junk and Petersen/topform intersections were empty. It likewise excluded L1009 (light-input-only agreement), L2425 (read2 incidence bound), and L4704/L4705 (partial-sound plane target). No Lean files were created or compiled during that check.
