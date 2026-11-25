# Fano six-AND auxiliary SAT check

This is a computational auxiliary result for L-meta-4970. It is **not a Lean proof of the posted statement**, and it is not a formal Lean proof of the circuit-to-CNF encoding. The exact CNF has been found UNSAT by CaDiCaL, and its LRAT certificate has been independently accepted by the local Std LRAT computational checker. The encoder and both symmetry reductions were separately source-reviewed by the counterexample agent.

The graph has seven left vertices and seven right vertices. Right vertex j is adjacent to left vertices j, j+1, j+3 modulo seven. It has 21 edges and minimum vertex cover seven. The informal interpretation of the checked CNF is that this graph function cannot be computed by an AO circuit with T0 and at most six AND gates, even with arbitrarily many OR gates. The star-witness assumption of the posted gap is not imposed here.

## Result and controls

- Exact final instance: 4,135 propositional variables and 28,735 clauses.
- Original symmetry-reduced solver run: UNSAT, exit 20, 63.45 seconds.
- Certificate-producing run: UNSAT, exit 20, 74.67 seconds.
- Certificate: 1,417,154 LRAT actions, 148,051,462 bytes before gzip.
- Independent verification: `Std LRAT computational checker: VERIFIED UNSAT CNF`, exit 0.
- A pinned canonical seven-AND circuit satisfies the same symmetry conditions. The decoder independently checks every CNF clause and all 16,384 input assignments. Its binary expansion has 7 AND gates, 20 OR gates, T0, and pure star witnesses for all 21 edges.
- The verifier accepts a valid two-clause control certificate and rejects a deliberately incomplete certificate.

Complete solver, decoder and verifier logs are included. `MANIFEST.json` records sizes and SHA256 digests, including the uncompressed certificate digest. The certificate is stored as deterministic gzip.

## Encoding and its unformalized completeness argument

Every maximal OR-only region can be flattened to a subset of original inputs and earlier AND outputs. Each AND therefore has two nonempty selected subsets. T0 is enforced by requiring the selected original inputs within each operand to have one colour; previous AND outputs contribute no original inputs to OR-reach. The final output is an OR of selected AND outputs: a direct original input would incorrectly accept its singleton assignment. Dead AND gates can be removed, and smaller circuits can be padded with identity AND gates, so exact six-AND synthesis covers the at-most-six question.

The monotone graph function is fixed by its 21 positive edge-pair assignments and 37 negative maximal independent sets. Boolean gate semantics are Tseitin encoded on these 58 patterns. Each intermediate AND must be used by a later AND or the final OR.

The two operands of each AND are ordered lexicographically. Adjacent independent AND gates are also ordered: if neither operand of the latter selects the former gate, both gates can be swapped and later references remapped. The first gate is canonicalized under all 168 colour-preserving Fano automorphisms, obtained by testing the 7! point permutations against the incidence triples and deriving their line permutations. Its 32,385 unordered nonempty monochromatic operand pairs have 517 orbits, all represented. A globally lexicographically minimal encoding satisfies both symmetry rules simultaneously. These completeness arguments have been reviewed, but have not been formalized in Lean.

## Reproduction

The scripts use `/tmp/oec/pequalnp-pilot-157` as their scratch directory. With Python 3 and the project's Lean 4.36.0 toolchain available, run from the repository root:

```sh
mkdir -p /tmp/oec/pequalnp-pilot-157
python3 results/orch/fano-and6/and_sat.py --graph fano --ands 6 --t0
python3 results/orch/fano-and6/and_order_symmetry.py /tmp/oec/pequalnp-pilot-157/fano-6and-t0.json /tmp/oec/pequalnp-pilot-157/fano-6and-t0.cnf /tmp/oec/pequalnp-pilot-157/fano-6and-t0-ordered.cnf
python3 results/orch/fano-and6/and_fano_symmetry.py
cadical --lrat=true -t 600 /tmp/oec/pequalnp-pilot-157/fano-6and-t0-automorphisms.cnf /tmp/oec/pequalnp-pilot-157/fano-6and-t0-automorphisms.lrat > /tmp/oec/pequalnp-pilot-157/reproduced-certificate.log 2>&1
```

CaDiCaL returns exit 20 for UNSAT. To verify a generated certificate, run from the `lean/` directory:

```sh
lake env lean --run ../results/orch/fano-and6/VerifyLrat.lean /tmp/oec/pequalnp-pilot-157/fano-6and-t0-automorphisms.cnf /tmp/oec/pequalnp-pilot-157/fano-6and-t0-automorphisms.lrat > /tmp/oec/pequalnp-pilot-157/reproduced-verify.log 2>&1
```

To verify the preserved certificate instead, decompress `fano-6and-t0-automorphisms.lrat.gz` with a standard gzip decoder and pass its path, together with the preserved CNF, to the same verifier. `VerifyLrat.lean` parses the DIMACS clauses without semantic transformations and calls the independently implemented `Std.Tactic.BVDecide.LRAT.check`. Executing that checker does not construct a kernel proof of the circuit claim.
