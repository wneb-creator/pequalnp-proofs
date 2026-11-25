# Checked plane geometry for L-meta-2583

`DualGeometry.lean` compiled successfully with a narrow Fintype/Card import. It proves at most one common point from point-pair unique joins, and dual unique intersection from equal positive point/line degrees.

`MixedSets.lean` compiled exit 0 on 2026-11-25; complete logs are `/tmp/oec/pequalnp-pilot-103/2583-mixed-third.stdout` and `.stderr` (stderr empty; two nonfatal unnecessarySimpa warnings). It is self-contained and includes DualGeometry plus:

- `point_degree`: exact posted plane hypotheses imply point degree q+1; partition count copied/adapted from PR13723, avoiding its broad imports and nlinarith.
- `nonincident_mixed_sets_bound_of_degrees`: equal q+1 degrees and unique point joins imply |A|+|B|≤N−q for nonempty nonincident point/line sets.
- `nonincident_mixed_sets_bound`: same bound under precisely the posted plane hypotheses.
- `mixed_vertex_cover_bound`: every incidence cover with both sides proper has size at least N+q.

Proof of the mixed-set bound: fix p0∈A and l0∈B. Put R=all lines except those through p0 or in B. Each p∈A\{p0} has exactly q incident lines in R; each line in R intersects l0 at a point outside A and therefore has at most q points in A\{p0}. Double counting yields |A|−1≤|R|=N−(q+1)−|B|.

Parent has been notified of compile success for immediate independent review and preservation. No desk/git writes by this agent.

## Structural-route notes

`CoverClassification.lean` compiled exit 0 (`2583-cover-first.stdout/.stderr`); it includes MixedSets plus general cover size ≥N and purity of every size-N cover.

Setting a point input false is not controlled by its raw fanout: in the optimal all-point-star circuit every point has fanout1, yet deleting that point removes q private OR gates, its AND gate, and one final OR gate (q+2). Deleting a line from the same circuit removes only q+1 direct reader gates, leaving the wrong side of the minimum-cover choice. Thus a useful deletion recurrence needs an existence statement for a private cone, not an averaged input-fanout lower bound.

Read 2026-11-25: Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf, only gives the C4-free ≥|E| bound for single-level circuits in the relevant paragraph. It does not justify unrestricted normalization.

Read 2026-11-25: https://github.com/open-goat/pequalnp-proofs/discussions/12644 reports no small counterexample to the core-cover inequality |D|+τ(G)≤|U|+mc+τ(G−D), and inconclusive PG(2,3) 63-gate searches. Counts and outcomes are the discussion author’s reported results, not independently reproduced here.

Repo L_meta_2969 and L_meta_3444 refute broad complementary cone-count bounds without minimality. Their circuits are nonminimal; root correctly notes they do not refute a least-circuit version. L_meta_3446 likewise concerns a stronger protected-cone cover inequality without minimality. The original full-U core-cover inequality alone is insufficient unless a complementary least-circuit count is also established.
