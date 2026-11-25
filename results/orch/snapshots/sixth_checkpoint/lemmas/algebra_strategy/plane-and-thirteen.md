# Plane AND lower bound: locally checked

The complete accepted upstream L-meta-1898 proof and a line-negation adapter to the exact posted L-meta-650 graph compile together in `PlaneAndThirteen.lean`.

- Command (workdir `lean/`): `lake env lean -j 1 -M 9216 /workspace/pequalnp-proofs/results/orch/lemmas/algebra_strategy/PlaneAndThirteen.lean`
- Started: 2026-11-25 04:59:49 UTC. Completion observed: 2026-11-25 05:04:18 UTC.
- Exit status: 0. Complete stdout and stderr: `plane-and-thirteen.validation.log` (empty successful output).
- SHA256: `d06130173f0021dc028289a66daa1c919c90bad6dc9c991a1bfec0aaa679c04d`.

The theorem `PEqualNP.Outside.L_meta_650_aux.PlaneAndThirteen.thirteen_ands` establishes at least 13 AND gates for every correct Monotone2 circuit for the exact posted 52-edge graph, with no normal-form or intermediate-wire-soundness assumption. It does not establish an OR-gate bound or refute the requested 63-gate statement.

The accepted upstream proof body is unchanged. Only its broad `import Mathlib` was removed, and `PEqualNP.MetaComplexity.Helpers.PermInputs` was added for the adapter. The accepted source was fetched into `/tmp/oec/pequalnp-pilot-57/upstream-refresh-002/L_meta_1898.lean`. The additional helper import makes this a research artifact, outside L-meta-650's permitted final-file imports. Earlier 6GB attempts exhausted the Lean interpreter memory limit; this exclusive 9GB run succeeded.
