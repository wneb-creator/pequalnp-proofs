# Plane READ1 lower bound provenance

`PlaneReadOneLower.lean` reuses the complete already-recorded proof `lean/PEqualNP/Outside/L_meta_4897.lean` (98,262 bytes, 1,961 lines at discovery). Its namespace is changed to `PEqualNP.Outside.L_meta_2583.ReadOneCover`; project imports remain `PEqualNP.Defs`. This upstream proof supplies the substantive C4-free READ1 circuit-to-vertex-cover bound. It is not newly proved mathematics in this job.

The new geometry and counting lemmas were developed in `PlaneRestrictions.lean`, `PlaneStarCover.lean`, and `PlaneRectangleCover.lean`. The final adapter uses plane regularity and the star-cover center lower bound to conclude `N * (q + 2) <= C.size + 1` for READ1 circuits computing the plane incidence function.

This remains a conditional READ1 lower bound. It does not establish the assigned gap, which asks for replacement of arbitrary AO2 circuits by no-larger READ1 circuits. It can support a refutation if a smaller AO2 circuit for a concrete plane is found.
