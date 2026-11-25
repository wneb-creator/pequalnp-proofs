# L-meta-2590 library route

## Existing certificates
No Petersen-minus-edge 18/19-gate lower bound was found in complete Fin10 source censuses (64 explicit syntax files and 292 short syntax files). Existing ten-input large certificates concern subdivision-K4 (12 edges, lower15). Splitting a first edge-AND and its OR reader leaves a residual bounded above by Petersen and accepting all other edges; it need not equal Petersen-minus-edge, so exact graph deletion lower bounds need an additional argument.

L8035 provides mono Petersen-minus-vertex lower16; L8367 combines it with signed lower15. These only lift our previous signed17/firstAND18 bounds by one, leaving full20 open.

## L971 structural route
L971 proves unrestricted Monotone2 Heawood lower27. There is no READ1 or least-circuit hypothesis in the final statement. It normalizes to strict live binary DAGs and counts wire fanout surplus: totalSurplus+n=gateCount+1. Generic semantic tools use symmetric, irreflexive graphs with separated neighborhoods and minimum degree2. Private-position strengthening also needs degree3 and C4-freeness. Petersen satisfies all of these. Heawood-specific bipartition and opposite-side charging do not automatically transfer.

Checked extraction `/tmp/oec/pequalnp-pilot-99/gap2590/library_route/PetersenSurplus.lean` (4231lines,199852bytes), namespace PEqualNP.Outside.L_meta_2590_aux.Surplus, SHA256 c4263050aec6af424fc64504f463e33ae5f002dab9e25b942a0bb8b98f16e19d. Full compile exit0, empty petersen-surplus.stdout/stderr, emitted .olean. Extracted L971 line ranges1–1374,1810–2470,2517–2694,2792–3575,3639–4418,4441–4732,6310–6434,6826–7130, only comments stripped and namespace changed.

Checked PetersenGeometry.lean/.olean, empty petersen-geometry.stdout/stderr, exit0. Defines exact Petersen adjacency masks[50,69,138,276,521,385,770,548,104,208], sem_Gr, independent-set size≤4, and pg_budget: strict-live correct length≤19 gives totalSurplus≤10 and 6≤eligibleCount≤Bplus. sem_pg_cover_free and sem_pg_private_slot adapt the corresponding L971 lemmas to Petersen and are checked.

## Finite cases and assignments
Petersen has120 automorphisms and76 independent sets (Python exact census). Six orbits including empty: ∅,{0},{0,2},{1,3,5},{1,4,5},{2,4,5,6}. Lean orbit classification is checked separately in PetersenOrbits.lean (exit0,empty logs, SHA2567e125bde853a5839f88eabef46d5c8c1b91e50d5e254b0b6cbded9986392aef0); 17 explicit automorphisms cover one-vertex extensions of these representatives.

Lower_bound agent handles all-eligible p=10. Abstract two-position consumption codes admit a false-positive rectangle model, so code constraints alone are insufficient. Actual DAG ordering and the forced Bzero=0 must be used. Reduction_strategy handles maximal ineligible set{2,4,5,6}: its complement is subdivision-K4 pair vertices plus opposite-pair matching; each eligible label has two ineligible neighbors and therefore at least3 consumption positions.

Remaining obstruction: derive enough additional surplus from shared supported wires and unshared empty-support AND gates to obtain totalSurplus≥11 for all six independent-set orbits. No complete contradiction yet.

Checked PetersenReduction.lean/.olean (empty petersen-reduction.stdout/stderr,exit0) connects arbitraryMonotone2circuits to the sixorbitstrict-liveproblem. `pg_six_cases` gives strictliveCorrectD,length≤19,totalSurplus≤10,eligiblecount≥6,ineligibleemptyorcanonical; no unproved structural assumptions. Scratch importsPetersenOrbits; finalstandalonerequiresinlinefirstthreecomponents.
