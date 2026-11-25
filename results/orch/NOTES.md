# Pilot 52 orchestration notes

Assigned L-meta-3178 on 2026-11-25 at 00:32:58 UTC. Desk task: cut; only submit a reduction. Allowed project import: PEqualNP.Defs. Existing reductions R_meta_3178_1 and R_meta_3178_31 cover graph symmetry.

Chosen strategy: h1 establishes >=13 non-NOT gates in any circuit for the 9-vertex Petersen edge function; h2 rules out the residual size<=13 tail when it has <=1 NOT. Prepend the prescribed NOT and OR gates to derive the residual bound. Parent proof L_meta_2758 contains both ingredients and assembly.

Strategies: parent proof mining; alternative finite encoding normalization; finite graph symmetry/testing; independent checker review; toolchain recovery. Symmetry-only strategy dropped because it duplicates existing cuts. Toolchain is missing despite kit description; setup agent downloads pinned Lean release and Mathlib cache.

All agents must read this before further proof work. Root alone holds lease and submits.
