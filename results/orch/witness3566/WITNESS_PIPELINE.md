# Circuit witness verification

`make_witness.py` accepts the finite-search JSON schema and generates a standalone Lean file proving:

- `witness_ao`: the circuit is `TopForm.IsAO2 n`;
- `witness_size`: its exact gate count;
- `witness_correct`: `circuitFun n witnessCircuit = graphFun witnessGraph ∅`.

The graph is exactly `EdgeOwnership.edgeGraph n` applied to the JSON edge list. Gate order and operand order are preserved. The optional JSON `output` is respected; otherwise the last gate is the output. The generator validates input ranges and allows only AND/OR gates.

Generation, from this directory:

```bash
python3 make_witness.py /absolute/path/witness.json /absolute/path/VerifiedWitness.lean
```

`GraphSemantics.lean` must be beside the generator. Its checked generic proof is copied into the output; the resulting Lean file needs only `import PEqualNP.Defs`.

The default `--strategy kernel` checks the flattened Boolean identity with ordinary trusted-kernel `decide +kernel`. It introduces no untrusted axiom. This works independently of whether the circuit has dirty AND gates. `--strategy simp` is an optional faster algebraic strategy for suitable witnesses.

The circuit bridge checks one wire-list transition per gate using two generic binary-gate lemmas, then rewrites the circuit fold. The graph bridge chooses the corresponding edge-list member in each direction. Neither bridge enumerates all vertex pairs or all input assignments.

Benchmark/build command:

```bash
PATH="/tmp/oec/pequalnp-pilot-178/toolchain/lean-4.36.0-linux/bin:$PATH" LEAN_NUM_THREADS=2 python3 run_lean.py /absolute/path/VerifiedWitness.lean /absolute/path/verified-build.log
```

`run_lean.py` retains complete stdout/stderr and records elapsed time, exit code, and Linux maximum RSS. It uses one Lean thread and a 5800 MiB Lean memory cap. Wait for the root's RAM slot before invoking it.

Checked benchmarks:

| Artifact | Inputs | Gates | Strategy | Elapsed | Maximum RSS |
|---|---:|---:|---|---:|---:|
| `Witness.lean` | 14 | 27 | simp | 6.352 s | 2,929,356 KiB |
| `WitnessKernel.lean` | 14 | 27 | kernel | 12.240 s | 3,273,228 KiB |
| `WitnessSmall.lean` | 11 | 18 | simp | 9.593 s | 2,906,868 KiB |
| `WitnessSmallKernel.lean` | 11 | 18 | kernel | 4.892 s | 2,931,692 KiB |

Successful logs are `witness-build-7.log`, `witness-kernel-build.log`, `witness-small-build.log`, and `witness-small-kernel-build.log`. These certify known upper-bound witnesses, not counterexamples to L-meta-3566. A smaller witness must be combined with the checked graph-side lower bound and the root's converse theorem.

The generator gives every output the same helper names inside `PEqualNP.Outside.L_meta_3566`; select one witness when composing the final single-file proof. The JSON graph order matches the independently checked Heawood and Graph11 graph artifacts. Do not combine several generated witness files without renaming their helpers.
