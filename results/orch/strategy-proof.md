# Existing-bounds route

- Upstream L_meta_4725.lean (3224 lines, 146284 bytes) proves the exact binary-floor reduction hypothesis: any FanInTwo circuit computing Petersen satisfies 15 + notCount C <= C.size. L_meta_6194 is its equivalent non-NOT count formulation.
- Therefore target reduces to one through four NOT gates. R_meta_2592_271 already records this reduction.
- Other existing reductions: R_meta_2592_318 splits after last NOT; R_meta_2592_408 normalizes wire indices and final output. Three reduction slots are occupied.
- L_meta_4759 proves that Petersen minus one vertex, with extra complemented input x4, needs at least 15 gates. L_meta_1924 and L_meta_2679 give related 14-gate bounds for a first-NOT split with an extra OR input.
- Generic EdgeFnFinal proves |E| + cover - 1 only for girth >= 7 and separated branch vertices, so it does not apply directly to Petersen (girth 5).
- L_meta_7493 gives at least 14 non-NOT gates after restricting away one Petersen vertex.

No full proof yet. Most promising concrete starting point is inlining the 146 KB binary-floor proof as a checked partial, then attacking one through four NOT cases.

## One-NOT bracket route

Four generic bracket lemmas now compile in `lemmas/BracketWitnesses.lean`: generator/co-generator conditions under which replacing the NOT by a constant preserves the output, and the corresponding critical witnesses when replacement changes it. These require monotonicity of the suffix in the original inputs and NOT output; they do not assume monotonicity of the prefix.

For Petersen, an essential one-NOT bracket must have a minimal true edge e with prefix h(e)=false and a maximal independent set I with h(I)=true. Computed all 120 graph automorphisms and the 15 maximal independent sets. The 225 (edge,I) pairs have five orbits, represented by edge mask3 and independent-set masks50,104,116,138,201. Orbit sizes are30,60,15,60,60. This computation is a search aid; the orbit classification has not been proved in Lean.

Constant replacement alone is insufficient even for a scalar monotone function: h=b and G(a,b,z)=(a AND b) OR (z AND (a OR b)) give f=a when z=NOT b, but both constant replacements change f. Replacing z by input a does work in that example. Thus no generic unsound constant-removal claim is used.

The tempting 8039 restriction improvement fails without more reasoning: its14-non-NOT lower bound applies to setting a vertex false, whereas the two-gate killing restriction may set it true. At vertex9, the true cofactor is x4 OR x6 OR x7 OR the edge function of the six-cycle0-1-2-3-8-5-0, and is much easier.
