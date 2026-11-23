# L-lib-123: checked helper results

Status: intermediate results only. These files neither prove nor refute
the posted universal FP3 speedup statement.

| Source | Checked scope |
| --- | --- |
| `Factorization.lean` | Equality is not one rectangle; an exact rectangle cover of all b-bit strings needs at least b certificate bits; conditional checkpoint-budget inequalities. |
| `SumCheckOrder.lean` | Explicit adaptive cheating in a specified flattened two-round sum-check protocol, the corresponding sequential rejection statement, and a partial-sum polynomial certificate equivalence. |
| `ShortInputNormalization.lean` | The stated optimistic cache inequalities imply a three-halves-power arithmetic budget; composing those inequalities with a two-thirds verifier does not save a power. |
| `LookupParity.lean` | A specified characteristic-two Boolean extension evaluates to a parity count; dense grouped interpolation messages obey an exponential dimension budget. |
| `ReverseReplay.lean` | Reverse-output replay semantics, optional-output filtering, and the exact solution of a defined abstract replay-budget recurrence. |

The sum-check counterexample refutes that intermediate quantifier-order
proposal only. The rectangle theorem concerns arbitrary strings; it is
not an incompressibility argument for short-input generated traces.
The cache and interpolation bounds concern their stated representations
and assumptions, not all simulation or proof systems. In particular,
the two-thirds composition does not exclude the separately proposed
three-fifths protocol. ReverseReplay does not establish operational TM2
time or space bounds, and its materialized Lean lists are not asserted
to use sublinear space.

All five files are standalone and import only `Mathlib`; they do not
import each other or project theorem files. Dependencies are the project's
Lean v4.36.0 and Mathlib commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

`validation.json` records successful replay checks and source hashes.
Each `*.lean.log` is the complete combined stdout/stderr from the named
Lean check; an empty log means no diagnostics. These checks are ordinary
`lake env lean` elaboration/kernel checks, not acceptance by the desk's
posted-statement checker.

From `lean/`, reproduce a check with:

```sh
lake env lean ../results/pequalnp-pilot-4b/L-lib-123/literature_route/Factorization.lean
```

Sub-agent `literature_route/compression_attempt` contributed conceptual
research and source auditing but no additional kernel-checked Lean file.
No downloaded papers, source archives, or unsuccessful probes are included.
