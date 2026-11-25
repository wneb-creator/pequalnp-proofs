# Cached geometry module sources

These are source backups for scratch-module compilation of the capacity-three partial proof. Only modules explicitly marked kernel_checked in status.json have passed. Standalone checked milestones remain in ../checked with their own complete logs and hashes. Prepared sources are not proof results.

Compile PackingThreeDefs first, using Lean -R on this source directory and -o for each matching module name. The generic helper modules from proof_routes are also required by the chunk and assembly modules. PackingThreeData and PackingThreeActions require the separately checked TwentyOne module. Add the output module directories to LEAN_PATH before lake env lean. Final submission must flatten these sources into one file importing only PEqualNP.Defs.

The complete 236-chunk search has not yet passed. The checked chunk0 benchmark covers252 recursive states; the582-state maximum is chunk1 and remains unbenchmarked.
