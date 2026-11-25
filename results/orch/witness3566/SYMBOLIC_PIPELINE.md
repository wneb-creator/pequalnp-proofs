# Symbolic amplification witness verification

This extends the checked ordinary circuit/graph bridges to large input counts without enumerating all assignments to the extended graph. The31-input63-gate control is an upper-bound witness, not a counterexample to L-meta-3566.

## Reproduce the checked large control

From the directory containing the generator and its dependencies:

```bash
python3 make_symbolic_witness.py symbolic-large-control.json symbolic-large-simp-plan.json VerifiedLarge.lean
PATH="/tmp/oec/pequalnp-pilot-178/toolchain/lean-4.36.0-linux/bin:$PATH" LEAN_NUM_THREADS=2 python3 run_lean.py VerifiedLarge.lean verified-large-build.log
```

This generation reproduces `SymbolicLargeFast.lean` byte-for-byte. Dependencies beside the generator are `make_witness.py` and `GraphSemantics.lean`. The generated Lean file is self-contained and imports only `PEqualNP.Defs`.

The cut plan contains a wire index and the edge list of its Boolean function. The generator proves that smaller identity, substitutes it into the full circuit expression, then expands appended stars by precise Boolean distributivity and `ac_rfl`. It does not invoke a31-variable `decide`.

Each cut supports `strategy: simp`, `strategy: kernel`, or the default `auto`. Auto tries the algebraic proof and falls back to ordinary `decide +kernel`; the fallback is limited to cuts with at most16 input variables. No `native_decide`, axioms, assumptions, or untrusted evaluators are used.

The full default simp set was too slow on the31-input extension identity. The final generator uses only explicit distributivity there, followed by AC normalization. Expression definitions are noncomputable because executable code for them is unnecessary; all equations remain available to the kernel.

## Convert a searched base witness

```bash
python3 amplify_symbolic.py base-witness.json OutputPrefix
```

This writes `OutputPrefix.witness.json`, `OutputPrefix.cuts.json`, and `OutputPrefix.lean`. The expected base schema is:

```json
{
  "graph": {"n": 15, "edges": [[0,6]]},
  "witness": {
    "gates": [["or",0,1]],
    "output": 15,
    "observed_helpers": [{"support": [0,1], "wire": 15}]
  }
}
```

The tiny JSON above illustrates the schema only; it is not a valid graph-function witness. Use the actual searched witness or `symbolic-base-control.json` for a valid example.

The converter independently checks every assignment to the base inputs and verifies every helper equals the OR of its support exactly. It shifts original gate indices to accommodate fresh inputs, adds one fresh center/private pair per helper, and appends OR(helper,private), AND(center,result), OR(previousOutput,result). The extended graph adds the corresponding star edges. It never enumerates all assignments to the extended inputs. The Lean output separately certifies the full extension.

Current converter supports exact helpers. It deliberately rejects relaxed helpers satisfying only OR(S) <= h <= OR(S) OR F. Such helpers require an additional absorption certificate; they must not be passed through unchanged.

## Checked controls

| Source | Inputs | Gates | Edges | Full build | Maximum RSS |
|---|---:|---:|---:|---:|---:|
|SymbolicLargeFast.lean|31|63|50|16.136s|3,095,680KiB|
|SymbolicSmall.lean|16|27|20|13.651s|2,932,480KiB|

The large input is `symbolic-large-control.json` with plan `symbolic-large-simp-plan.json`. Its exact nested base input is `symbolic-base-control.json`. The small input is `../finite_search/c8-amplified-4-27.witness.json`, plan `symbolic-small-plan.json`; it exercises the default auto strategy. Complete successful stdout/stderr is retained in `symbolic-large-fast-build.log` and `symbolic-small-build.log`. A few unused-simp-argument warnings do not affect the checked theorems.

Both files prove `witness_ao`, `witness_size`, and `witness_correct`. Large source484lines and small source271lines contain no forbidden root text, string literals, attributes, or diagnostic commands. Their only options are maxRecDepth and maxHeartbeats.

The independent reviewer confirmed exact source/JSON/generator agreement, all32768 base truth-table rows, all8 helper outputs, and full31-input symbolic DNF equality to50 edge monomials. Its review is in `../repo_review/symbolic-witness-audit.log`; the full31-input graph has a matching and cover of size14. This review does not claim a smaller counterexample circuit.

`prepare_symbolic_controls.py` recreates the controls from `../certificate_search/subk33.json`, `../certificate_search/subk33-free-program.json`, and the small finite-search witness. Direct regeneration from the preserved full JSON and plan does not need those external scratch dependencies.

Wait for the root's Lean RAM slot before starting a build. The runner preserves complete diagnostics, uses one Lean thread and a5800MiB cap, and records wall time and maximum RSS. No tracked repository file is modified by this pipeline.
