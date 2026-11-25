# Geometric completeness for counterexample verification

The full classification is now Lean kernel checked. For every posted admissible point set X, GeometryComplete.admissible_complete proves that X equals AllRows.points r for some r : Fin36 × Fin13. The64 independent128-mask checks cover all8192 point subsets. They are split into eight cached modules, each containing eight consecutive chunks, and combined symbolically by GeometryCompleteness.

Checked module order:

1. GeometryRowsDefs: exact AllRows definitions.
2. GeometryMaskCore: bitmask decoding, injectivity and surjectivity.
3. GeometryMaskData: the explicit packed row-index lookup.
4. GeometryCompletenessProofs: symbolic chunk/classification assembly.
5. GeometryCompletenessGroup0 through GeometryCompletenessGroup7: all64 closed kernel certificates.
6. GeometryCompleteness: masks_classified and admissible_complete.
7. GeometryFlags: exact52 positive flag inputs, explicit incident-pair index and coverage.

GeometryRowsAgreement also passed, in42.04seconds wall and39.3seconds kernel time. Its checked AllRows.row_eq theorem transports each literal AllRows.row to the posted AllRows.rowInput(AllRows.points r). This completes the geometric coverage and input-transport pipeline.

The eight completeness groups took255.94 seconds total wall time; the aggregate took3.01seconds. Maximum group peakRSS was3,839,360KiB and peakcgroup5,251,825,664bytes. There were no proof failures or resource stops in this sequence. Complete logs, immutable source snapshots and SHA256 files are under results/orch/checked/modules; status.json records exact module hashes. Olean caches are in the task scratch lean-modules directory.

For reproduction, build the modules in the order above with PEqualNP.Defs available and the olean output directory prepended to LEAN_PATH. The guarded runner uses explicit Lean -R/-o, records complete output plus peakRSS/cgroup use, and stops only its own process group at7.3GiB. Root coordinates slots and renews the desk lease.

This is geometric completeness for future circuit verification, not a proof or refutation of the posted51-OR statement. The earlier capacity-three route remains paused: only its documented partial components and chunk0 are checked; the236-chunk packing certificate and orbit/action closure are not proved.
