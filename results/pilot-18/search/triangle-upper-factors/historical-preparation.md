# Exact triangle upper-factor candidate family

Ready for main independent review. No solver, search worker or Lean build was
started. Existing workers and their input files were untouched.

For each vertex v, let `H_v = F_G OR OR(N(v))`. For the two triangles `(1,4,8)`
and `(3,6,7)`, the product of the three H factors is exactly F_G. This was checked
on all2048 assignments for each triangle. There is also a short reason: each
triangle has a degree-two simplicial vertex, respectively1 or3. On an independent
input, satisfying that vertex's neighborhood OR selects one of the other two
triangle vertices. An independent input containing that selected vertex cannot
satisfy its own neighborhood OR. Thus not all three factors can be true on an
independent input. On a positive input all three are true.

The fresh parent is the reviewed original-DAG encoding with J18 fixed true:
`orch/S01/consecutive-junk-v2/normalized.cnf`, SHA
`3fefefe3949bc703fc2b9f023be12bc42f1afe7619e8ed5ed63be2f8e7648812`.
Its11968variables and114567clauses remain, with its body bytes unchanged. Each
child has114660clauses: exactly93 additional units and no auxiliary variables.

## Pins

Every permutation assigns its three exact factors to wires27,28,29, which are
prefix gates14,15,16. Each factor adds11 singleton-support units and16 positive
edge units. For a proper singleton support S, the clean-AND prefix encoding
already makes values on nonempty independent inputs equal OR(S). Thus these
27 units pin all40 boundary values to H_v; the24 negative rows need no separate
prefix value variables. Monotonicity and a missing singleton ensure the empty
input is false too. The metadata records all40 expected boundary values for
independent inspection.

The suffix has these exact gates, with operations AND throughout:

| Gate | Output wire | Left wire | Right wire |
| --- | --- | --- | --- |
|17|30|27|27|
|18|31|30|30|
|19|32|28|31|
|20|33|29|32|

The second copy reads the first copy so gate17 remains live. Every suffix gate
reaches the final output. All three factor outputs are read. Gates17 and18 are
junk because a proper nonempty factor support accepts a singleton. Gate19 is
also junk: any pair of factors shares the third triangle vertex in its support.
Gate20 computes F_G and is clean. These facts were checked on all2048 inputs
for every permutation using exact-factor oracles. They do not establish that
the three oracles can jointly be built by a17gate clean-AND prefix.

## Cost screening and scope

The independently enumerated residual vertex-cover bounds match the parent's
2048-entry support-cost table:

| Factor | Support | Minimum clean-wire gate bound |
| --- | --- | --- |
|H1|4,8|16|
|H4|1,8,10|13|
|H8|1,4,5,9|12|
|H3|6,7|17|
|H6|3,7,10|14|
|H7|3,6,9|14|

The bounds are `|S| + |E(G-S)| + tau(G-S) - 1`. Consequently H1 cannot occupy
gate14, and H3 must occupy gate16. All12 files are retained for reproducibility;
only these six permutations are marked `cost_feasible` and worth candidate CPU:

- `(4,1,8)`, `(4,8,1)`, `(8,1,4)`, `(8,4,1)`
- `(6,7,3)`, `(7,6,3)`

This is a candidate-only restriction. There is no WLOG assertion that a size21
witness must use these factors or place them at the last three prefix gates.
Inherited prefix sorting, liveness, cost and other parent restrictions remain.
Even UNSAT for all12 children would not refute the parent, the assigned shard,
or the posted existential statement. The cost screen is only used within this
fixed family; no formula is silently discarded.

## Artifacts and controls

- Generator: `generate_triangle_factors.py`
- Audit: `audit_triangle_factors.py`
- Family: `triangle-upper-factors/family.json`
- Review: `triangle-factor-review.json`
- Full logs: `triangle-generation.stdout.txt`, `triangle-generation.stderr.txt`,
  `triangle-audit.stdout.txt`, `triangle-audit.stderr.txt`

The audit checks12288 scalar factor values,4096 product identities,24576 suffix
rows, all1116 added units, exact parent-plus-unit reconstruction of all12 files,
cost table agreement, wrong-parent and existing-output rejection, and25
byte-identical reproduced files. Generation and audit both exit0, with empty
stderr. No satisfying assignment for the full CNF is known; oracle/unit controls
are not represented as a full-model SAT control.

Reproduction, from any working directory, requires the pinned parent files:

```sh
python3 -B /tmp/oec/pequalnp-pilot-18/orch/S02/generate_triangle_factors.py \
  /tmp/oec/pequalnp-pilot-18/orch/S02/triangle-upper-factors-new
```

Any future SAT model still requires the full CNF/model validator, all2048 scalar
checks, constant elimination and size<=21, followed by the exact Lean proof.
