# L-meta-4970 orchestration notes

Leasefe8dc4d4-d568-4909-a49a-a241b3015ec1 received15:39:27UTC, advertisedexpiry15:58:22UTC. Exactstatement scratchstatement-4970.txt. No reductions. NewgoalexplicitstarORcoverage andTwoColour.tCount=0 forC4freebipartiteedgefunction. Previousworkpreserved; noPetersencontinuation.

Reduction strategy: ReadOneObstructionChecked.lean gives a kernel-checked three-gate two-edge star circuit satisfying AO2, exact edge function, no 4-cycle, tCount=0, and the posted star-OR coverage, yet not read-1. It is NOT a refutation of L4970: a smaller read-1 circuit exists. Consequently a direct tCount-zero implies read-1 bridge is false; normalization needs genuine gate deletion. Checked source hash ab53e3e4eae6fa7ff467a772a99ca950f9c711d7ab5f4b8ac87d1562127b05e2.

Counterexample-route CHECKED 2026-11-25T15:45:06.045704+00:00: SemanticStarObstruction.lean computes1point/2line star withgatesAND(1,1),OR(3,2),AND(0,4). All4970hypotheseshold; syntacticT=0 andsemanticstarORreachesonlyinput2 throughORs, whileedge(0,1)hasnoread1proof. Thussemanticstarwitnesses+T0doNOTimplysamecircuitread1. Size3satisfiespostedlowerbound2; notfullrefutation.


## Toolchain strategy: semantic feature boundary (checked partial)

`lemmas/toolchain_setup/FeatureCover.v2.checked.lean` SHA256 e2525c43620cde4cc540c67578e9e1d60070faf40653f87703f3654cf652c02b passed pinned Lean exit0 with empty matching logs. For C4-free bipartite E, any exact monotone factorization fE(x,y)=F(features(x),y) with k monotone point features yields a vertex cover of size at most k. Proof: for each edge(a,b), compare singleton a to all nonneighbors of b. Some feature is true on the former and false on the latter. Its singleton-support is nonempty and contained in N(b); a support of size1 selects its point, while support size≥2 has unique line center. Choose one vertex per useful feature.

Potential application: cut the backward output cone at semantically one-sided wires; the remaining semantically mixed gates have a connected binary DAG with point and line boundary features. Each side needs at least tau features, giving at least2*tau−1 mixed gates once the factorization and graph-count bridges are supplied. These bridges are not yet formalized.

Important ledger caveat: L529 charges gates false on the outside-S assignment and true on two singleton inputs in S. Such a gate need not be semantically pure: a OR b OR(c AND y), with a,b,c in S, meets that condition but depends on y. Therefore the semantic mixed-gate lower bound is NOT automatically disjoint from L529 charges, and the bounds cannot yet be added.

[2026-11-25 15:47:46 UTC, proof_strategy] StarCentersChecked.lean compiledexit0, SHA a6861c35df67044bf85bc78187a6f6db1e99faa0e52b307852439255e799d604. Purefinite+semantic helper: ≥2 commonneighbors give unique center inC4free relation; a fixed circuitwire computing a qualifying pure ORstar has uniquecenter across both orientations. The posted served-star assumption extracts a vertexcover with cardinal≤numberORgates. Does not use tCount orcorrectness; doesnotprovefull E+cover ledger.

CHECKED unused-star obstruction 2026-11-25T15:48:31.633340+00:00: UnusedStarObstruction.lean hasC=(a OR c) AND ((a AND b) OR d), withunusedOR(b,d). Allpostedhypotheseshold; edgeab onlyhasunusedlastOR assemanticstarwitness. Thereforeexistentialstarcoverage doesnotimplyactualANDjoinswiththosewitnesses. Size5satisfiespostedbound4; notgaprefutation.

Reduction strategy checked LinearOrChargeChecked.lean: strengthens checked L529 to charge only OR gates. For arbitrary nonuniform family S_i with pairwise intersections <=1 and monotone binary circuit computing each pure OR(S_i), sum_i(|S_i|-1) <= number of OR gates. No tCount or size conclusion for full4970 claimed. The partition invariant cannot merge classes at AND: one operand is false on complement(S_i) and carries all accepted singleton inputs. Source hash 1ec7d965a859d407f7d3ece62f3722228fa5db2e16343ba5a123a00159a8fb86.

## Semantic OR-family component charge checked

`lemmas/sat_strategy/OrCharge.checked.lean` compiles with Defs-only imports and no diagnostics. It reuses checked Clean/Tset wire semantics from L6734, then strengthens the old factor2 gate bound using a label-merging invariant. For pairwise-intersection≤1 support families S_c, it constructs percenter labels making the actual singleton support of EVERY S_c-clean wire monochromatic, and proves sum|S_c| ≤ sum(number of final label classes on S_c) + number of OR gates. Thus multiple disconnected star witnesses are retained as components rather than incorrectly charging unionleaves−1 percenter. `pure_or_tset` and `pure_or_clean` bridge semantically exact star ORs to the invariant. This bundle includes the earlier MergeCharge declarations; omit that duplicate standalone fragment when merging. Independent review requested.

[2026-11-25 15:50:42 UTC, proof_strategy] CountedCentersChecked.lean compiledexit0; SHA 71ebbbc42cf1e12fc34fef524275b978bb914f1cf32d7f2932911ec90fc72eb3. ExtendsStarCenters: neighborhoods indexedbyFinp⊕Finl pairwiseintersect≤1, includingoppositeorientations; anymonotonefunctionfalseoutsideN(center) andtrueontwosingletons hasuniquecenter. Hence correspondingD_center filters ofanyfinitegateindexset arepairwisedisjoint andsumcard≤availablegatecount. This doesNOTshowD_center disjointfromsemanticmixedcore: f=b∨c∨(d∧a) iscounterexample whenN={b,c,d}.


Toolchain update: immutable `FeatureCover.v4.checked.lean` SHA25675701aa641dfaf747011e0dc210f3df57adf2fc97d9323c12dbf450ee2307d30 has complete empty Lean logs and matching manifest. `two_sided_factor_cover` now proves: a monotone exact factorization through k1 point features and k2 line features, with k1+k2<=r+1, yields a vertex cover S with2*|S|<=r+1. It includes transpose/dual cover proof and the generic frontier pin-count lemma. No actual circuit-cut factorization or disjointness with OR-family charges is established.

After the new OR-only star-charge result, a possible stronger residual target is AND-count plus OR gates rejecting all singletons >=2*tau−1. This would be disjoint from the star charges. The semantic frontier theorem does not prove it: an OR gate with nonempty singleton support may still mix a one-sided linear term and a bilinear AND signal, so simply contracting it is invalid. Another unproved formulation is2*tau<=AND-count+number-of-AND-roots-in-output-OR-cone, with those roots bounded by output-OR-count+1.
