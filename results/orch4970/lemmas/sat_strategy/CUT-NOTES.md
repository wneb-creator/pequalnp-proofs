# Quantitative cut investigation — paused

Recorded at 2026-11-25T15:57:01.822299+00:00. No residual-gate theorem is claimed.

The checked family_component_charge provides label classes for every center-support family, simultaneously making all clean wire singleton supports monochromatic. Let D be summed support sizes and c the summed final label-image sizes. It proves D <= c + OR-count. Multiple star witnesses at one center can form disconnected components; union-size minus one is not generally justified.

For a prospective stronger construction, omit redundant merges whose two labels already agree. Each remaining merge has representatives in the center support and decreases that image cardinality exactly one. Thus one expects to select protected OR gates B with |B| = D-c, uniquely owned by centers using pairwise support-intersection <=1. This exact-selection strengthening has NOT been formalized here.

If selected component stars cover E, define overlap credit delta = D-|E|. The necessary residual inequality is R >= c + tau - 1 - delta, where R counts gates outside B. The stronger R >= c+tau-1 is unnecessary and can fail for redundant star families. Symbolic example: a standard eight-gate C6 edge circuit plus three unused opposite-side star ORs has eleven gates; all six stars give D=12,c=6,B=6,R=5,tau=3. The stronger residual asks for eight, while the correct overlap-adjusted residual only asks for two. This example was not separately Lean-checked here.

FeatureCover supplies vertex covers from genuine one-color semantic features and a frontier bound. The central unresolved bridge is constructing a cut with such features and enough boundary incidences after charging B. Charged gates can themselves be semantically mixed, so they cannot simply be removed as a pure one-color prefix. For instance h=a AND b; OR(h,t1), then repeatedly OR with further line variables, and finally OR with b gives a pure line OR. Intermediate genuine singleton-component merges can be semantically mixed. T=0 does not prevent this, because AND gates stop syntactic OR reach.

The root acknowledged overlap credit and is coordinating the remaining cut/ledger. No new finite search was started: the proposed free-OR/six-AND Fano test is owned by the counterexample agent, if the ownership audit permits resumption. All work stopped on the root ownership-audit instruction.
