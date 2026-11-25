# Any-profile optimization and new Petersen-deletion control

For profile=any, v8 removes only unused definitional cone/ownership auxiliaries; the decoder still recomputes and checks actual cones and ownership. The v8 known Petersen20 circuit padded to21slots passes all1024inputs and has effective prefix20. Its C5 at-most6 query is UNSAT in the reviewed normalized finite model (not a Lean minimality theorem).

The graph-only v9 addition is the eight-vertex ten-edge graph obtained by deleting adjacent Petersen vertices. Its known13-gate star control is SAT and independently verified on all256inputs, with exact earliest prefix13, all cones/owned edges and pre-target domination/incomparability constraints. Its12-gate query and the full Petersen19 query are not included here: no live output was frozen.

Sources, controls, full solver logs and independent review are preserved. The status census is a historical snapshot at creation, not a claim about later runs. No full L-meta-2448 proof or refutation is claimed.
