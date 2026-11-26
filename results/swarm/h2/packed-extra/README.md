This research bundle proves frozen Packed.checkNode for indices2852 through3071 inclusive (220 nodes). These nodes were explicitly reassigned from H4; H4 stopped at2851. This does not prove all5230 nodes or L-meta-2373.

H2PackedReplay.extra_checked takes only i:Fin5230 and2852<=i.val<3072. It combines exact adjacent110-node chunks [2852,2962) and [2962,3072) using the already checked H2PackedReplay.check_interval. Each chunk uses listPieces_all depth5 with three/four-node decide +kernel leaves.

Dependencies are the frozen36375ce3 certificate at results/swarm/h8/certificate18 and H2ChunkDefs/H2IntervalBridge from commit719980203 at results/swarm/h2/packed-replay. Under Lean4.36.0, put their compiled modules on LEAN_PATH, then compile H2Extra2852_2961, H2Extra2962_3071 and H2ExtraRange in that order. Complete source, stdout, stderr, source/object hashes and invocation wall/peakRSS receipts are supplied; compiled objects are omitted.

The two110-node compiler invocations ran concurrently with6000MB caps; the aggregate uses3500MB. Allthree axiom reports contain exactly propext, Classical.choice, Quot.sound. Source diagnostics and research imports are intentional; this is not a single-file submission. No full-checker runtime or submission-size claim is made.

Together with our published1536..2303 result this verifies988 distinct nodes, in two disjoint intervals.
Sub-agents: setup, coverage, sat, constructive
TIMING total=143.4 subagents=4
