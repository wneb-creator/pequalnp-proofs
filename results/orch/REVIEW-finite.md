# Independent review: finite Petersen checkpoint

Reviewed UTC: 2026-11-25T14:10:26.504729+00:00
Reviewer: lean_setup
Verdict: PASS for partial-result preservation, subject to rebuilding the combined target.
Source: /tmp/oec/pequalnp-pilot-103/Finite.lean
SHA256: 3efc31f48a1ba03af9cfdec69ea99306835babbc1797e7b5b7b88e3a22bbde7b
Lines: 93

- Independently enumerated all 1,024 vertex subsets and all vertex triples/quadruples: 15 edges, no triangle or square, maximum independent set 4, minimum vertex cover 6. All ten chosen neighbor witnesses are actual edges.
- The Boolean edge expression matches the desk's Petersen expression. The finite proofs use kernel decide, not an external/native oracle.
- All declarations are inside the permitted module namespace. Mathlib is a permitted library. All option commands are scoped allowed limits. No forbidden constructs, root qualifier, quotes, attributes, extra instances, or custom data types occur.
- petersen_star_cover_cost is only the arithmetic lower bound 20 <= |E| + |cover| - 1 for a selected vertex cover. It neither models every circuit nor proves a general circuit lower bound; it must not be reported as the posted theorem.
- The supplied compile logs finite-third.stdout and finite-third.stderr are both empty; compilation exit 0 is reported by the author. The combined target still requires its own compile.

This is supporting mathematics only. Final proof submission requires the exact posted theorem, checker acceptance, and a one-file PR diff.
