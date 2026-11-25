Status: SOURCE ONLY, UNCOMPILED. No Lean process or solver was run for this draft.

Source: results/orch/lemmas/MarginalCoverFinite.lean, SHA256 bdeb3d0cc2af3b6d0a3eb40bd545eaaf10acb2364efca6957ad19b1a4c25df7b, 138 lines. It imports only PEqualNP.Defs and has no custom datatype, attribute or option declaration.

The selected negative input is mask 3735587: Singer points 0,1,5 and lines 3,6,7,8. The source contains the twelve audited maximal positive-support masks. Instead of enumerating 4096 subsets in Lean, it uses the nine flags

{0,39,14,4,25,29,10,13,12}.

Each of the twelve maximal supports hits at most one of these flags. Eight flags are private to eight different supports: flag0 to support0, flag39 to4, flag14 to5, flag4 to6, flag25 to7, flag29 to9, flag10 to10, and flag13 to11. Flag12 appears only in supports1 and8, separate from those eight private-support indices. A cover of all 52 flags must therefore have at least nine supports. Python confirmed these data directly from the audited masks; Lean verification is pending.

Planned closed finite certificates are witnessFlags_card, maximal_hits_at_most_one, table_lengths, and false_wire_dominated, each written with by decide. The general union-cardinality argument derives nine_le_maximal_cover_card and small_maximal_subsets_fail. The latter covers all subsets of Fin12 of cardinality at most eight without a 4096-case kernel computation.

The generic API nine_le_cover_card takes an arbitrary finite selected-wire set s, a positive support for each wire, and a map dominator into Fin12. Its assumptions are that every selected support is contained in its assigned maximal support and that the selected supports cover all 52 flags. It concludes 9≤s.card.

The file also contains all 98 audited wire-support masks, their Boolean values at the chosen generic row, and explicit dominating-maximal indices for false wires. The source-only theorem false_wire_dominated checks that table relation. The specialization nine_le_table_cover_card has exactly the minimum-cover hypothesis needed by CanonicalExtensionCover: all selected wires are false under wireBad, and their wireGood values cover every flag. eight_le_appended_or_count converts an asserted cover of size≤k+1 into 8≤k.

Required connections outside this source: identify wireGood/wireBad tables with the actual functions of the fixed 48-OR base circuit; and, if claiming a result for arbitrary raw Circuit extensions, formally normalize such extensions to CanonicalCompiler.Program while preserving OR count. The current generic extension source directly quantifies Program. No target 51-OR statement is proved by this draft.

Metadata and Python-only checks are recorded in results/orch/marginal-cover-finite-source.json. The earlier independent full mask audit remains in results/orch/pg3-marginal48-cover-audit.py and its log.
