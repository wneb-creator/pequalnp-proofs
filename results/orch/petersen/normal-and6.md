# Petersen AND-count route

The checked library proof `L_meta_635` establishes that every OR-free AndCountCircuit10 separating the maximal independent sets of the Petersen graph uses at least six AND gates. The compiler `L_meta_7541` is generic internally and specializes from26 inputs to10 without changing its proof: any Monotone2 circuit having a false input compiles to this model with no more AND gates and equal outputs. Exact Petersen computation supplies the false input and the separating boundary behavior.

`normal_and6.lean` inlines those existing proofs under `PEqualNP.Outside.L_meta_2590_aux`, uses only `PEqualNP.Defs`, and appends a direct original-Circuit theorem `petersen_and_ge_six`. Initial Lean validation is running. This is an unconditional AND-count result; an independent OR-count lower14 would imply the requested size20 bound.

2026-11-25T15:23:20.852100+00:00 STOP on parent lease loss. The complete AND6 source is preserved but UNVERIFIED: the first compile was stopped after7minutes while potentially evaluating a1024-assignment bridge. It has been replaced by a15-edge direct Boolean proof plus100-pair finite certificate. Standalone bridge first failed Decidable synthesis on the30-disjunct relation; maxRecDepth4000 was added. Improved full source and standalone bridge checks are pending. No source may be claimed compiled until their logs show exit0.

Additional findings: L905 gives six-AND impossibility only under each variable occurring bare in at most2 AND gates, not a clean-gate classification. Its521752-byte certificate is near512KiB. Six ANDs alone cannot imply clean/read1: adjacent-star identity u(A∨v)∨vB=(u∨v)∧(u∨B)∧(v∨A) retains2 ANDs but adds1 OR, allowing dirty circuits above optimum. L616 gives unconditional Petersen size≥16 from the general cubic C4free n+vertexcover bound. L7804 gives a low-occurrence adjacent pair in sub-star-cover circuits, but assumes global IsMinimalCircuit rather than monotone-only minimality.

Final validation statuses after STOP: improved full AND6 process was terminated intentionally, exit143; standalone bridge check exit1 (see normal-log-petersen-normal-bridge4.*). No complete AND6 result was checked.
