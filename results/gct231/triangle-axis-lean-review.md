# Checked triangle-axis scalar certificate: independent archive review

The frozen 15-file `triangle-axis-lean/` archive passes exact coverage, SHA256 and text-only checks against manifest `c05cc0f79fc27076354256d2cfb5438f7a3d00246292b9cf31607f1325bc7255`. Total size including the manifest is 13937 bytes.

The final Lean source is byte-identical to the original independently reviewed certificate, SHA256 `f453366b19430a626696520b30cdcbefbd2131b6aa4cc32606fa2c7beeb89a22`. Its four polynomial hypotheses remain explicit. The integer polynomial combination yields 4214784=0, giving the contradiction. There are no new axioms, admitted proofs, unsafe declarations, or changes to the reviewed algebra.

The final `build02` log is empty and records exit 0. The separate axiom driver is exactly the final source followed by one `#print axioms` command; its successful log reports only propext, Classical.choice and Quot.sound. Both run metadata files agree with the preserved sampled-RSS monitor and limits. The earlier diagnostic differs only by the deprecated complex import alias and retains its warning; the final source uses the original preferred import.

The README correctly limits this theorem to the displayed four equations. Connecting them to a geometric chart and covering other charts remain separate obligations. No compiler was rerun for this review.

Independent reproducer/full log: `/tmp/oec/pequalnp-pilot-75/gct231/triangle_axis_lean_review.py` and `triangle-axis-lean-review.log`, completed 2026-11-25T12:05:13.706463+00:00. All review output is outside the frozen archive.
