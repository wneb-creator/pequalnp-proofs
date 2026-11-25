# Descendant and existing-proof search

Searched public map/search metadata and all 712 checked repository source files indexed by the term Petersen. Exact theorem statements are extracted into `/tmp/oec/pequalnp-pilot-118/petersen-checked-statements.json` (this is data, not compiled results).

## Most useful checked components

- `L_meta_6581.lean` (4555 lines): full ten-vertex Petersen edge function requires at least **16 non-NOT gates**. This improves `L_meta_6194` (15) and reduces any 19-gate counterexample to at most three NOT gates.
- `L_meta_7493.lean` (4140 lines): Petersen with vertex 9 fixed false requires at least **14 non-NOT gates**.
- `L_meta_8033.lean` (7136 lines): deleted Petersen requires size >=15 and binary floor13.
- `L_meta_8035.lean` (6653 lines): excludes size15, zero NOT.
- `L_meta_8037.lean` (4014 lines): excludes size15, exactly one NOT.
- `L_meta_8039.lean` (4222 lines): excludes size15, exactly two NOT.
  Thus 8033+8035+8037+8039 imply unconditional deleted-Petersen **size >=16**; alternatively use7493 to omit8039. This assembly has not been Lean-checked in our file, and helpers need deduplication to stay under512KiB.
- `L_meta_5236.lean` (4560 lines): normalized suffix with free initial x0 OR x2, at most18 gates and3..4NOT cannot compute full Petersen. This covers the first-OR/nonedge case at higher NOT count.
- `L_meta_5238.lean` (3253 lines): same with at least5NOT.
- `L_meta_8021.lean` is only contradictory assumptions (no NOT and count>=1); it provides no new small-NOT bound.
- `L_meta_6198.lean` is variable restriction/gate elimination, not the remaining main small-NOT case.

Public metadata for2592 is still conjecture. Checked status is recorded for8033,8035,8037,8039,6581. All three reduction slots for2592 already exist. No direct full-Petersen binary lower bound >=17 or size>=20 was found among the712 relevant checked theorem statements.

Only PEqualNP.Defs is an allowed project import. Existing Outside proofs may supply proof material, but cannot simply be imported.

Last updated: 2026-11-25T14:20:08.780934+00:00

## Stronger certificate internals and new proof attempt

`L_meta_8037` actually certifies a universal deleted-Petersen binary floor15: its one-NOT assumption is used only to derive a binary budget14, then the same signed `rootSImpossible` certificate contradicts that budget. `L_meta_6581` already embeds this certificate and exposes it as `nineFloor`.

New snippets: `FirstProjection.lean` implements ten explicit graph automorphism projections, verified independently in Python for all512rows each. Together with `Retention.snippet.lean` from lower_bound agent, it aims to prove full-Petersen binary floor17 and floor18 when the first signed binary gate is not OR. The projected mass counts only constants; duplicate wires are deliberately not charged, because duplicate charging is false in general. Lean validation is pending the shared Defs build.

First-NOT checked statements found:5367 direct consumer count floor;7312 missing positive consumer forces a later sign-changing NOT;7314 nonminimal shape produces ordinary18circuit;5905 restricted cofactor lower bound;4083 cut separation. None alone closes the tight positive-OR/negative-AND topology.
