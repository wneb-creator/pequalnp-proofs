This research bundle proves Packed.checkNode for indices 1536 through 1667 inclusive, using the frozen certificate at commit 36375ce3bb56c227c81ecae98f6641800006b8c2, results/swarm/h8/certificate18. It is not a proof of L-meta-2373 or a proof that all 5230 nodes pass.

Compile the frozen PackedDirect dependency stack under Lean 4.36.0 with the repository's pinned dependencies, then compile H2ChunkDefs.lean, H2Nodes1536_1539.lean and H2Nodes1540_1667.lean with those compiled modules on LEAN_PATH. H2PackedReplay.blockCheck_at converts each range Boolean equality to its individual node equalities. Every supplied index is below5230, so Fin.ofNat introduces no wraparound.

The128-node theorem uses listPieces_all at depth5, yielding32 separate four-node decide +kernel obligations. The source retains axiom-print commands as research diagnostics. Only the standard three axioms appear. The named submission helper remains a separate Defs-only file; this multi-module research bundle is not in submission format.

Complete Lean stdout/stderr and wall-time/peakRSS measurements are included. Source and compiled-object hashes are recorded in manifest.json; compiled objects are not committed. The first128-node block ran under a9000MB Lean cap. Its14.32-minute runtime is local evidence only; no whole-file checker runtime or512KiB submission-size claim is made.

Sub-agents: setup, coverage, sat, constructive (4 unique agents).
TIMING total=120 subagents=4
