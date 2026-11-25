# Plane lower-bound route status

2026-11-25T15:02:00.972404+00:00

All four components below compiled successfully with only `PEqualNP.Defs` imported. Complete stdout and stderr logs are retained under `/tmp/oec/pequalnp-pilot-100/restriction-build/`; parent preserves them on the work branch.

- `PlaneRestrictions.lean`: 5030 bytes; 111 lines; SHA256 `578f6b4ab13d23ea1de350ac5f372863f10fd0a323b7f093ecb01c25a8e1b463`.
- `PlaneStarCover.lean`: 7089 bytes; 157 lines; SHA256 `cf0ac1b315069424c5338c7da76a186a8a1e4a98b0d5ce07b8628511eff632bc`.
- `PlaneRectangleCover.lean`: 12206 bytes; 262 lines; SHA256 `9e376194f79bc7228b7db55db2ec39ddb009b8a1200c30b595c1be5a877a7abf`.
- `PlaneReadOneLower.lean`: 112427 bytes; 2262 lines; SHA256 `c6df5ccfc72e842123daab7cce37fec34d47b96e3310869cdd2d02cfa0730205`.

The new geometry proves dual regularity (every point lies on q+1 lines), thin rectangles, incidence count N(q+1), minimum star-cover center count N, and weighted rectangle-cover cost at least N(q+2). The READ1 lower bound reuses the substantive upstream proof L-meta-4897 exactly, with namespace/import changes only, and adds the plane adapter. Its conclusion is `N*(q+2) <= C.size+1` with the READ1 hypothesis retained.

For q=2 and N=7 this excludes all READ1 implementations with at most26 gates. A genuine AO2 implementation with at most26 gates would therefore refute the assigned replacement statement; counterexample_search is working on that finite search.

The unproved general step is converting arbitrary AO2 circuits into a costed star cover (or directly proving the same exact size lower bound). TopForm alone does not suffice: the independently reviewed PlaneDirtyBlock P4 example has five gates, TopForm and no4cycle, but is not READ1; a four-gate READ1 implementation exists, so that example is not a refutation.

Other inspected upstream bounds do not close the missing step: L-meta-2581 assumes READ3 and yields a coarse bound; L-meta-2672 includes a double-reread error term; L-meta-4510 gives a3N-1 bound only when the output is AND.
