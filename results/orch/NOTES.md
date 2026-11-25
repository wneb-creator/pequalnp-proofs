# L-meta-2583 orchestration notes

Only root holds and renews the lease. Assigned statement in /tmp/oec/pequalnp-pilot-147/statement.txt. Reductions disabled. Separate strategies append dated findings here; write scratch lemmas in results/orch/lemmas. Do not run lake builds concurrently; coordinate with root.

## Construction agent (2026-11-25 14:58 UTC)
Found complete star-cover construction in Outside/L_meta_7684.lean (1126 lines, only Mathlib and Defs dependencies). It gives read-1 AO2 size ≤ |E| + |U| + |V| - 1 for any point/line vertex cover U,V. All points gives plane upper bound N(q+2)-1. Copied to results/orch/lemmas/Construction.lean under L_meta_2583_aux with declarations changed to lemmas; specialized plane_upper corollary written, compilation pending.

## Library route, 2026-11-25T14:58:42.979903+00:00

- Full constructive read-1 upper bound is checked in `Outside/L_meta_7684.lean` (1126 lines): any bipartite edge set and cover A,B admit read-1 AO2 circuit of size at most |E|+|A|+|B|-1. Construct agent is adapting this.
- `L_meta_7639` (1977 lines) proves read-1 lower bound |E|+N ≤ C.size+1 for rectangle-free balanced bipartite graph with perfect matching. `L_meta_4897` (1961 lines) gives the vertex-cover version. Plane target is therefore equivalent to arbitrary-AO2 bound N(q+2) ≤ C.size+1.
- General replacement remains a reduction `R_meta_4895_1` with hypotheses star-budget bound and star construction; `R_meta_4895_628` reduces it to a matching-charge bound. No unconditional general lower bound found.
- Existing unconditional plane bounds include `L_meta_8805` (3N ≤ C.size+1) and `L_meta_5351` (349N ≤ 100*C.size, assuming q ≥ 200); read-2/3 bounds do not reach exact target.
- `L_meta_7241` has exact |E|+cover bound if every AND rejects nonedges, but arbitrary circuits need not satisfy that internal condition.

## Independent partial review 2026-11-25T14:58:59.165908+00:00

Construction.lean copies the checked star-cover and read-1 construction from L_meta_7684, commit 051efff1, PR #12317, by Bastian Milan; it renames the namespace and turns theorem declarations into helper lemmas. New work specializes the edge count and circuit bound to the incidence assumptions. The audit confirms no forbidden source constructs; this partial has no full target theorem and does not prove the posted gap. Lean compilation is still pending.

2026-11-25T14:59:35.336128+00:00 Necessity draft prepared at `results/orch/lemmas/Necessity.lean`: copied read-1 cover lower bound, plane row regularity, cover cardinality via regular bipartite incidence counting, and read-1 lower N(q+2)≤C.size+1. Waiting toolchain before build. Perfect matching is unnecessary: regularity alone proves every cover has ≥N vertices.

2026-11-25T14:59:36.835848+00:00
## Counterexample route — initial findings

- The incidence hypotheses imply an actual symmetric 2-(q²+q+1,q+1,1) design; no degenerate relation loophole found. q=2 yields 7 points/lines, 21 edges, and canonical 27-gate read-1 circuit.
- Exact finite backtracking over triples on seven labeled points found 30 line-unlabeled Steiner triple systems (151200 after labeling the lines); every one has 37 maximal independent sets. Output: /tmp/oec/pequalnp-pilot-147/fano-design-enumeration.json.
- For monotone circuits, equality with the Fano edge function is characterized by truth on the 21 edge minterms and falsehood on the 37 maximal independent sets. Thus a 58-bit truth vector is an exact witness test, not sampling.
- A 15-minute C++ heuristic search for 26 gates is running. It uses simulated annealing and random local mutations, seeded by deleting a gate from a 27-gate star circuit. This is NOT exhaustive and cannot establish impossibility. Files: /tmp/oec/pequalnp-pilot-147/fano_search.cpp and fano-search.stdout.
- Related paper named in repo notes: Jukna, Disproving the single level conjecture, ECCC TR05-021. Not read here; relevance UNVERIFIED.
2026-11-25T14:59:53.051387+00:00
## Structural strategy update

- Exact target is equivalent, with existing canonical read-1 construction and read-1 lower bound, to the sharp arbitrary AO2 lower bound `C.size + 1 >= N*(q+2)`. Existing reusable proofs: `L_meta_7684` builds from a bipartite cover; `L_meta_7639` gives the read-1 matching lower bound; `L_meta_8567` gives least/TopForm normalization.
- Every incidence edge first becomes a two-variable AND at a gate whose two children restrict to its two variables. But that gate need not be below the final function: its singleton-support rectangle can contain nonedges. Unique pair incidence only makes a rectangle a star AFTER the rectangle is proved wholly sound. Charging later filters is the essential unresolved issue.
- Naive child bypass fails even for a tree: let h=(p OR a) AND (p OR b), and contexts q,r where p is adjacent to both, a only q, b only r. Replacing h by either child can introduce ar or bq, though the whole h gadget can be replaced by p if the other required star edges aq,br are already computed. Thus useful normalization must coordinate several gates and absorption, not one local child replacement.
- General quadratic single-level normalization is false, but known examples exploit same-side cliques. A bipartite doubling preserves many 4-cycles and the obvious lifted circuit wrongly accepts same-side pairs plus an unrelated opposite variable. No transfer to projective planes obtained.
