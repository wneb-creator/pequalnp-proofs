# L-meta-1884 independent review

The exact statement concerns a circuit with at most 18 gates evaluated on eleven input wires: ten values `x (sigma i)`, followed by the free unary value `u (x 0)`. The required output is the Petersen edge function on ten independent Boolean variables. No proof or counterexample has been established.

## Definition obligations

`MetaComplexity.FanInTwo` permits AND, OR and NOT, with zero, one or two listed operands. It permits duplicate operands, forward or missing wire references, unused gates and arbitrary output indices. A missing read is false. Empty AND and empty NOT are true; empty OR is false. NOT reads only its first operand and ignores a second listed operand. In this statement gate j produces wire 11+j. IsAO2 and monotone-circuit normalizations cannot be applied without proving their extra hypotheses or constructing an equivalent circuit.

The input map sigma is an arbitrary function, not necessarily a permutation. The free unary function has four possibilities: false, true, identity and complement. If sigma omits a nonzero variable, both the raw and unary inputs ignore that variable, contradicting essentiality of the target. Sigma may omit zero when the unary input recovers it, so bijectivity cannot be assumed unconditionally. If zero is omitted, the ten raw slots cover the other nine variables; one duplicate remains. Constant unary input does force sigma to be bijective.

An invalid output is constantly false and cannot equal the target. An output directly reading a raw input or the extra unary input also cannot compute the target. These observations must be proved when used; FanInTwo itself supplies no output bound.

## Existing reductions and prior components

R_meta_1884_773 separates arbitrary relabeling, normalization of the free unary input to complement, and the hard canonical lower bound on `x ++ [!x 0]`. Its normalization hypothesis excludes output index 10; the reduction handles that direct-unary-output case separately. The hypotheses are conditional obligations, not completed lower bounds.

R_meta_1884_1 instead exposes ordinary ten-input and deleted-vertex lower bounds together with restricted reader configurations for raw wires 0 and 10. R_meta_1884_412 exposes a finite pivotal-input property and a remaining circuit core. The finite property does not by itself prove the gate bound. Three live reductions are already recorded, so another reduction cannot be presumed available.

The previously checked modular Bound17 result says that a standard ten-input Petersen circuit has at least 17 non-NOT gates. For the canonical extra-complement case, prepend one NOT gate reading raw input 0, without changing any original gate index or output index. Starting with ten inputs, the new NOT creates wire 10 and every original gate remains at wire 11+j. This preserves even missing-read behavior. The added NOT and added gate cancel in the old bound, yielding the useful prospective corollary `17 + internalNotCount <= C.size`; at size 18, at most one internal NOT remains. The construction and transfer still need their own Lean proof. They do not exclude the zero/one-internal-NOT cases. The old Full17 inline snapshot was not independently built; its dependencies and Bound17 were checked modularly.

The old monotone Petersen CNF and unrestricted NOT CNF artifacts are conditional completeness/replay bridges, not UNSAT certificates. Their normalized input assumptions and gate counts must be adapted before use here. No stopped search from a withdrawn assignment supplies a lower bound.

## Reviewed first partial

InputSupport.lean is frozen at SHA256 `6ff188d17207bf4a2d440c25b0f352ee61a3ed53ff036df4ac03d7a4b1ddc552`, 81 lines and 2924 bytes. Its successful compile logs are empty. The ten explicit essential-coordinate witnesses were independently checked against the fifteen target edges. The proofs compare identical input lists and derive the range and unary-function consequences above from correctness alone, without assuming a specific gate model.

The exact source passes semantic and forbidden-format review. The actual guard reports only the absent top-level main theorem. It is approved as a partial support lemma, not a proof of the posted circuit bound.
