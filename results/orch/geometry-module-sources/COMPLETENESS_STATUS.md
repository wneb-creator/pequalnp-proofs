# Geometric completeness for counterexample verification

Goal: every posted admissible point set X equals AllRows.points r for some r : Fin36 × Fin13. Combined with AllRows.row_eq, this reduces all posted negative inputs to the 468 literal rows. The row order is exactly geometry-data.json.generic; flat index13*r.1+r.2 agrees with the counterexample model.

Checked and cached in /tmp/oec/pequalnp-pilot-62/lean-modules:

- GeometryRowsDefs: exact AllRows definitions, SHA256 3b206cf10d7acd0196a5ad5dd32df658d448cad6d99861469e60a2f5ee6978cf.
- GeometryMaskCore: decode Fin8192 into point sets; symbolic injectivity via bits and surjectivity via equal finite cardinalities. SHA256 32c1da597f6d84f77b41d63dc70e4ee7dee96938e96483b1e55d6d77c5fec15b.

Additional checked modules:

- GeometryCompletenessProofs: symbolic assembly from chunk/classification hypotheses, exit0.
- GeometryFlags: exact52 flag inputs and explicit incident-pair coverage, exit0.
- GeometryMaskData: a66825-bit packed lookup table, exit0 in4.01seconds.
- GeometryCompletenessBench: masks0 through127, including40 admissible masks, exit0 in9.02seconds wall and5.86seconds kernel. PeakRSS3,826,584KiB; peakcgroup5,406,539,776bytes.

Prepared only, not yet checked:
- GeometryCompleteness:64 chunks of 128masks, followed by masks_classified and admissible_complete. No existential 468-row search is used.
- GeometryRowsAgreement: only the 36row_eq chunks and aggregate, extracted from the already checked standalone AllRows source for a new cached module.

Use LEAN_PATH with both the lean-modules directory and its parent. The guarded runner emits .olean using explicit -R and -o, profiles declarations, records complete output and peakRSS/cgroup use, and interrupts only its own process group at 7.3 GiB cgroup usage. Parent coordinates resource slots and renews the desk lease before builds. Only the first128-mask classification benchmark has run; the full64-chunk certificate remains unchecked.

The earlier capacity-three 22 route is paused. Its checked chunk0 covers 252 recursive states; the maximum 582-state chunk1 remains untested. Do not describe the 236-chunk certificate, action preservation or orbit descent as proved. The capacity 4 point-partition obstruction shows that merely increasing packing capacity cannot reach the posted 51 bound.
