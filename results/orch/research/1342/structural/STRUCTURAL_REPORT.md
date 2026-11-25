# L-meta-1342 structural findings

The posted theorem is the full existence of an at-most-21-gate monotone binary circuit for G11. Shard 0 requests exactly two junk AND gates only as search coordination.

## Checked structural sieve
For a least top-form circuit with two junk gates, put B=|tops\centreless|, Q=|centreless|, R=|orN\lam|, u=|Ustar|. Existing checked L1491/L4183 give B+2Q+R <= u+4 and the residual-cover bound tau(G11\Ustar)<=B. Since tau(G11)=7, 7<=B+u. L1490 gives a junk OR-reach witness for every Ustar edge, and L2695 converts it into Q>0 or R>0. Therefore u>=2; if u=2, B=5,Q=0,R=1 and size=21.

The Python enumeration edge_sieve.py confirms tau(G11)=7. Deleting two edges gives residual cover5 in16cases, cover6 in94cases, cover7 in10cases. All16 tight pairs are vertex-disjoint. This computation is not Lean checked. Complete data and stdout are edge-sieve.json/log. Deletion histograms for u=0 through4 are included.

## Existing exact-two-junk case split
- R_meta_2260_2: nested junk; Ustar size2/3/at least4. The size2 branch derives the unique mixing OR source, disjoint edge pair, and tight star count.
- L_meta_5226, checked at upstream9c4fa2bd4f85e59f6cebbe16ca9a4ba71df2b472, closes that nested size2 branch. Its actual helper does not need the final statement's size21 or pair-disjointness assumptions.
- R_meta_2262_1: incomparable junk with a common descendant top. It encodes all16 positive edge inputs and24 maximal-independent negative inputs.
- R_meta_2264_428: incomparable junk with disjoint descendant-top sets.

## Fresh public sources actually read
- PR11107, head61604cf11044939de7e24293b9b88c7f5b5e561c: 6482lines/412015bytes, sourceSHA2560b3f20c44ae8739ae961579014fe617e87e12e3af5d333c91c658990ee82eada. Apparent full proof of L5228 (nested u3), exact final statement, no sorry/new axiom/native_decide/_root_ text found. Source imports Defs and three Mathlib tactic files. Author claims ACCEPTED(check), but comments list is empty and I did not compile; acceptance remains unverified independently. Source includes residual-cover4 induced-matching argument and finite certificates for larger-cover cases.
- PR10447, headaeb99cf3d13a8d3178d286cf7ec50f5fdcce1226: actual50line reduction R5230_619, not full proof. Isolates a <=2vertex cover of first-junk contributions; remaining Ustar edges activate second junk h and meet wmax(h). Its second child is exact residual-cover deletion profile [16,12,8,5,3,2,1,0] for cover sizes0...7. Hard counting child remains.
- PR10624, headd97e7566a51d86ec47719f3093359d9909ba508d: actual52line reduction R5230_1, not full proof. Isolates same residual-cover profile and explicit first mixing-OR routing, retaining hard obstruction child.

## Route document availability
Both referenced routes are absent from working tree, immutable main tree, and all git history checked. Direct pequalnp.com/routes URLs returned404 (full bodies/status saved). Public search index contains no rart/1342/1343 terms and does not expose route exports. No route content was guessed or represented as read.

Reviewer owns main1342/1343 PR census; it found existing shard0 finite-boundary reduction11248, so a new identical encoding would duplicate work.
