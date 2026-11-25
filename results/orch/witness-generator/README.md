# Candidate-to-Lean bundle for L-meta-2732

This bundle generates a single Lean file from a binary AND/OR circuit. Strict mode preserves the posted statement exactly and permits at most 26 normalized gates. No 26-gate witness has been found; this bundle is proof assembly infrastructure.

The input is a JSON list of triples such as `["or", 0, 1]`, with 14 implicit inputs, gate `i` producing wire `14+i`, and the last gate being the output. Fanins must refer to earlier wires. The generator checks all 16,384 inputs before and after removing idempotent, duplicate, and unused gates. It then checks the packed 58-row boundary output and renders the kernel-checked witness argument, full input-renaming proof, and symmetry-minimal prefix proof inline. The only Lean import is `PEqualNP.Defs`.

For a genuine candidate, run from `/workspace/pequalnp-proofs/lean`:

```sh
python3 /tmp/oec/pequalnp-pilot-70/formalization/witness-generator/generate_witness.py /absolute/path/to/candidate.json --output /workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_2732.lean && ELAN_HOME=/tmp/oec/pequalnp-pilot-70/elan PATH=/tmp/oec/pequalnp-pilot-70/elan/bin:"${PATH}" lake build PEqualNP.Outside.L_meta_2732
```

Generation does not itself run Lean, the repository checker, or git. Its JSON output explicitly records `lean_checked: false`. Root must renew the lease before a long build and independently review the generated diff before pushing.

The optional `--relaxed-27-test` mode is restricted to this job's scratch directory and requires exactly 27 normalized gates. It replaces only the four helper tail bounds and the posted conclusion's tail bound from 24 to 25. The fixture under `relaxed_27/` therefore proves a weaker 27-gate statement. It is **not a proof of L-meta-2732** and must never be copied into the submitted module or presented as a completed gap.

The template and exact posted-statement bytes are pinned by `manifest.json`. The generator refuses an altered bundle. Its output has one outer auxiliary namespace and a final fully qualified theorem. Strict-mode guards reject the 27-gate baseline and a truncated incorrect circuit before writing any output; complete stdout and stderr are recorded alongside `guard-validation.json`.

The eventual exact candidate still needs its own Lean build and the official checker. A successful relaxed smoke check confirms inline assembly and namespace compatibility only.
