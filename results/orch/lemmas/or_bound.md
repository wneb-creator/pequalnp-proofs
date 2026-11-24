# AND/OR count route for L-meta-5112

Updated 2026-11-24T21:58:55.861268+00:00.

Initial free-AND closure on the24 essential rows has80 signatures; exact data in scratch or_bound/initial.json. ExactSAT agent is checking an alternate encoding with≤10 counted OR gates and unlimited free ANDs.

L_meta_724 paidVertex mechanism survives the3 precomputed opposite-edge OR inputs. Deleting a point leaves these inputs unchanged. Deleting an edge-variablev paired withu uses probeq={u,w},p={u,v,w}, wherew is an endpoint ofv. Becausev,u have disjoint endpoints, q is negative andp positive, while(v∨u) agrees onp,q. Thus the initial signal satisfies the requiredGood condition. However this pays onlyoneOR pervertex; 11OR lower bound needs stronger2/3-payment certificates. Original raw_meets monomial characterization does not apply to the augmented basis.

Root asked to implement complementary AND>=4 bound. Compiled generic proof is results/orch/lemmas/AndBound.lean. It replaces eachAND gate by either operand, obtaining at most2^k OR-only majorants. Every negative row is rejected by some majorant. For12 selected negative rows, eachpair has apositive row whose input pattern is contained in theirbitwiseOR. Hence one OR-only majorant cannot reject two selected negatives; inject12 rows into2^k choices, obtainingk>=4. Numeric bridge and finite pair-certificate are under construction in scratch AndBound.lean.

- 2026-11-24T21:59:52.339823+00:00: Numeric extension compiled successfully with targetedMathlib imports. Frozen file results/orch/lemmas/AndBoundSpecific.lean proves at_least_four_ands for any natural-index program returning1764784 from posted initial vectors, with no length or selector constraints. Build log is empty success. This is a partial necessary condition, not a proof/refutation of the posted14-gate existence claim.

- 2026-11-24T22:03:19.955190+00:00: Explicit free-AND normalization compiled in results/orch/lemmas/OrNormal.lean. Uses only Mathlib.Data.List.GetD, no new inductive types or instances. canonical_or_program gives exactly the original OR count; each OR operand and output is a conjunction of earlier canonical sources. Canonical initial sources are false::inputs, hence outputs begin at original-inputcount+1. Every factor is proved in range, even when original selectors are arbitrary/defaultzero. SAT convention input0..12,false13 is a cyclic permutation of formal false0,input1..13; both put OR outputs at14+k.
