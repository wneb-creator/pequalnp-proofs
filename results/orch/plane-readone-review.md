Independent review: plane geometry and READ-1 lower bound

2026-11-25T15:00:40.819253+00:00

Snapshot PlaneReadOneLower.lean:112427bytes,2262lines, SHA-256 c6df5ccfc72e842123daab7cce37fec34d47b96e3310869cdd2d02cfa0730205. Verdict: mathematical/source PASS for preserving a conditional helper partial, pending the author's compilation result.

Exact textual provenance: the entire checked L_meta_4897.lean source is the prefix after changing only its namespace to L_meta_2583.ReadOneCover and removing importMathlib. The local source hash matches the fresh checked feed. The complete PlaneRectangleCover body is then included verbatim. The only new adapter is read_one_lower at2225. The helper keeps the explicit IsReadK(...,1) premise; it makes no arbitraryAO2 lower-bound claim.

Geometry review: unique incidence of distinctpoints excludes every2x2rectangle, hence each nonemptybiclique has a singleton side. Removing a fixedpoint from each incidentline partitions allotherpoints into disjoint q-elementsets, so itsdegree isq+1. This uses q>0 fromq≥2 andN=q²+q+1; no dual incidence axiom is assumed. Doublecounting incidences then gives totalN(q+1) and anypoint/line vertexcover has at leastNcenters. For nonemptyrectangles, each has capacity≤q+1 and weight(area+1), so anycover has totalweight≥N(q+2). These arguments handle overlappingcovers using an inequality, not an invalid disjointness assumption.

Adapter review: E=allIncidencesI is extensionally the postedrelation. rectangle_thin provides the C4-free premise of the reused circuit-to-cover theorem. The exact posted incidence semantics is transported by mem_allIncidences. The returnedcover contributes at leastNcenters and covers exactlyN(q+1)edges; its checkedcostbound therefore yieldsN(q+2)≤C.size+1. In theFano caseq2,N7 this yieldsC.size≥27 forREAD-1 circuits.

Format review: onlyDefs imported; no _root_, quotes, sorry, native_decide, axioms, unsafe declarations, attributes, instance declarations, or global options occur. File112427bytes is below512KiB. Namespace remains withinL_meta_2583. It remains ahelperfile without the final assigned theorem; fullchecker requirements remain outstanding.

Author reports final compilation exit0,9130bytes of inheritedwarnings onstdout andemptystderr; snapshot remains frozen.

PlaneBundle integration review: source122885bytes/2522lines, SHA-256 65a10f37660ac3dfd08efa4d56ee89a3abd380767a92d0db434951b8d673cb1f. PASS pending combinedcompilation. EachofPlaneReadOneLower,PlaneStructural,PlaneAbsorption,FanoFiniteData appears exactlyonce verbatim afterremovingimports. OnlyDefs imported. Independently read theStructural andAbsorption modules: primeimplicants oftheexactincidencefunction are exactlyincidentpoint/linepairs; the READ1 pair-vector characterization follows; the Booleancontext absorption identities retaintheirnecessarybelow-targethypothesis and make no unprovedgatecount claim. New fano_read_one_size specializes read_one_lower toq2,N7 usingthefiniteFano linecardinality andunique-line lemmas, then derives27≤C.size. It retainsAO2, exactfunction, andREAD1premises. No finalassignedtheoremclaim andno forbiddenconstructs.
