# Lower bound library reconnaissance

- Time: 2026-11-24T21:52:15.058133+00:00
- No directly applicable theorem for 14-gate impossibility found.
- `MetaComplexity/Helpers/EdgeFnFinal.lean`: `stmtLB_final` proves class (T) edge-function lower bound, but class requires girth at least 7 and distances at least7 between branch vertices. K4 incidence fails both (girth6, branch distance2).
- `Outside/L_meta_1490.lean:684`: star structure of top AND gates under NoFourCycle, IsLeastAO, TopForm.
- `Outside/L_meta_1491.lean:2496`: aggregate size lower bound with error terms Ustar, junk, centreless, plus cover bound. Not a plain exact size theorem.
- `Outside/L_meta_1528.lean:3453`: sharpened bound when junk is a singleton. No direct application without normal form/decomposition proof.
- `Outside/L_meta_2237.lean:1877`: NoFourCycle read-once AND/OR circuits compute graph function only if edgecard+covercard<=size+1. Read-once assumption is material and does not hold automatically for present circuit.
- `Outside/L_meta_3068.lean` (only PEqualNP.Defs import, about8k lines) is useful lower-bound implementation template with one precomputed OR input. Namespace H8Free implements finite Boolean-semantic gate-state search, symmetry compression, pruning cuts and kernel-decided certificates. `lower` at approximately8070 proves no10-gate abstract build; final theorem lifts this after pinning/restrictions.
- `Outside/L_meta_724.lean` (only PEqualNP.Defs import, about1.3k lines) proves OR count>=8 for two pentagons sharing an edge, allowing arbitrary AND gates and fanout. Namespace OrCost gives free-AND semantics Meet/Run, paidMap/paidVertex restriction lemmas, finite closure certificates. Potential template for proving OR count>=11 here, if discoverable certificate. Together with AND count>=4 that would prove size>=15.
- `Outside/L_meta_984.lean` reuses free-AND OR-count machinery and separate AndPart bound for explicit small graphs.
- Helpers are not exported by PEqualNP.Defs; importing these outside files is disallowed by the posted imports. Their proofs would need copying/adaptation inside the one allowed file.
