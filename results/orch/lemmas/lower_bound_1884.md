# L-meta-1884 input normalization and lower bounds

Frozen checked InputSupport.lean imports only PEqualNP.Defs. It uses explicit Petersen essential-coordinate witnesses and proves every nonzero variable lies in the image of the ten-slot input map. If zero is omitted, the extra unary map is nonconstant and hence is identity or Boolean negation. If the unary map is constant, the input map is surjective and therefore bijective. These statements assume exact circuit correctness but no gate-shape or size hypothesis, so they respect all default/forward-reference semantics automatically. No claim that zero must occur in every input map is made.

Compilation/export passed with empty stdout and stderr. Source is frozen at /tmp/oec/pequalnp-pilot-99/gap1884/lower_bound/InputSupport.lean, SHA256 6ff188d17207bf4a2d440c25b0f352ee61a3ed53ff036df4ac03d7a4b1ddc552. Full logs: input-support.stdout and input-support.stderr. This is a necessary-condition component, not the full posted lower bound.

Existing L_meta_2594 provides arbitrary input relabeling; L_meta_2596 provides arbitrary unary-map normalization to the free negative literal. sat_encoding owns the compact prefix-NOT compiler to ordinary ten-input circuits. The next application is the earlier checked binary-floor17 theorem, which should force at most one internal NOT in an 18-gate canonical circuit.
