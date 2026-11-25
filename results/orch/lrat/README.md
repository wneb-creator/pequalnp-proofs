# Kernel-only SAT certificate route

This is supporting work for L-meta-2602, not a proof or refutation of the posted 64-gate statement. The certificate below verifies the already known **65-gate** witness against all 52 incidence edges. Root holds the lease and handles submission.

## Completed and checked

- `Plane65.cnf`: Tseitin encoding of the 65-gate circuit XOR the full 52-edge DNF. It has 194 variables and 506 clauses: 26 original inputs, 65 circuit gates, and 103 DNF gates (52 AND plus 51 OR).
- `Plane65.lrat`: CaDiCaL UNSAT certificate, 206 RUP additions and two deletions. `Plane65-cadical.log` is the complete stdout/stderr; solver exit 20 means UNSAT.
- `Plane65-rup.lean`: ordinary Lean proof of inconsistency of those 506 clauses. Lean exited 0; `Plane65-rup.log` records the axiom footprint `[propext, Classical.choice, Quot.sound]`.
- `Plane65-bool.lean`: adds eight elementary Boolean clause lemmas and `sat_plane65_wiring_identity`. Given the 168 gate equations, this proves wire 90 equals wire 193. Lean exited 0; full successful output is `Plane65-bool-2.log`, with the same three allowed axioms.
- The generated proof uses only `Mathlib.Tactic`, ordinary declarations/tactics, and allowed recursion/heartbeat limits. For final proof-file embedding, remove the diagnostic `#print axioms`, scope every limit option per declaration, and put helper declarations inside the required module auxiliary namespace block (the archive currently uses unscoped limits and some fully qualified helper names). It contains no string literals or forbidden root-qualified names.
- `Probe.lean` and `Probe.log` additionally demonstrate Mathlib's existing `lrat_proof` machinery has the same allowed axiom footprint. This scratch-only demonstration contains string literals and diagnostics; do not embed it in a submitted proof.

## Reusable generator

Run the following from this directory, supplying absolute paths:

```sh
python3 generate_identity.py WITNESS_JSON OUTPUT_DIRECTORY --solver PATH_TO_CADICAL
```

The witness JSON must have `gates` as lists `[operation, inputA, inputB]` with `operation` equal to `and` or `or`, and an integer `output`. Inputs are wires 0 through 25. Gate `i` produces wire `26+i`. The generator checks distinct earlier gate operands, constructs the exact incidence edge DNF using `(point-line) mod 13` in `{0,1,3,9}`, calls CaDiCaL with `--lrat=true --binary=false`, then emits `Identity.lean` and metadata. `export_rup.py` rejects unsupported RAT steps; it never trusts the solver's answer as an axiom. Lean independently checks every generated proof term.

Use the installed toolchain environment before `lake env lean OUTPUT_DIRECTORY/Identity.lean`. Full generated output must still be compiled and independently reviewed. The combined generator was also exercised end to end on `plane65-witness.json`: it exited0, and its `GeneratedIdentity.lean` compiled exit0 with only `[propext, Classical.choice, Quot.sound]`. Full outputs are `generator-test.log` and `GeneratedIdentity.log`.

## Circuit.wires integration

`Plane65-recurrence.lean` now also proves `sat65_valuations` for the actual `Circuit.wires` values90 and193, for every input `Fin26 → Bool`. Lean exited0, and the complete `Plane65-recurrence-3.log` lists only `[propext, Classical.choice, Quot.sound]`.

This adds a generic one-step wire recurrence copied from accepted `L_meta_2067.lean` lines6–103 into our own `SatWire` auxiliary namespace, two binary-operation specializations, the168-gate extended circuit, its finite validity proof, and the168 applications of the recurrence. Thus the Boolean certificate is now connected to actual circuit evaluation without expanding expressions. The extension contains the65 original gates followed by the103 edge-DNF gates. A future final witness still needs the simple prefix-preservation connection from its original circuit to the extended circuit and the identification of the final103 gates with the posted edge existential; those are not claimed by this supporting theorem.

An earlier optional attempt to prove all168 equations directly by `rfl` was stopped after approximately two minutes; the successful generic recurrence replaces that approach. No failed trial is included in this archive.

## Rejected tactic mode

Installed Lean 4.36 `bv_decide` and `bv_check` both unconditionally call `nativeEqTrue` in `Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:40`. There is no kernel-only configuration; neither was invoked. Mathlib's LRAT proof reconstruction uses ordinary kernel proofs, but a direct RUP exporter avoids string literals and meta declarations in final submitted source.

`manifest.json` records exact archived bytes and SHA256 hashes. No failed native or axiom-extended proof is included.
