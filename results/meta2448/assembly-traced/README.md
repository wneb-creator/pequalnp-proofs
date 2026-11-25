# Portable partial checkpoint for L-meta-2448

This checked collection of helper results does not prove or refute the posted theorem requiring a globally minimum circuit with a star ownership profile. The global normalization argument remains unresolved.

The 2341-line candidate depends only on `PEqualNP.Defs`. It preserves the previous 2234-line checkpoint verbatim and appends the checked 107-line TracedRepair component, removing only that component's dependency line. Exact input hashes and all 174 declaration names appear in `candidate-manifest.json`.

TracedRepair exposes the compiler's exact lowered gate list. Under its explicit repair identity, zero-input and sampled-term hypotheses, one constructed circuit simultaneously has the stated size bound, full function equality, and strict sampled true-AND count decrease. It does not establish minimum selection or a star ownership profile.

The complete candidate passed Lean. A separate cached probe audited all 174 declarations, including definitions; only `propext`, `Classical.choice`, and `Quot.sound` occur. Full build and axiom logs are retained. The probe is validation material and is not part of the candidate source.

The root agent owns the named target, repository build, official checker and publication. This scratch-module result alone is not an accepted proof of the gap.
