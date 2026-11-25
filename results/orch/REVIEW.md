# Independent checkpoint review

Reviewer: checker_review sub-agent. Reviewed 2026-11-25 UTC.

This is a preservation checkpoint of recovered helper lemmas, not a proof of
L-meta-1031. The final theorem is absent. Do not open a proof PR from this state
or describe it as checker-accepted.

Reviewed source: `lean/PEqualNP/Outside/L_meta_1031.lean`, 3,027 lines,
144,376 bytes, SHA256
`c3cf7ffffc50b449695e13e6f99914ffcea66ad0eec640bf7bfa612eccc32102`.

- The source is plain UTF-8, not a link, and not executable.
- Its sole import, `PEqualNP.Defs`, is allowed by this gap's posted imports.
- Helpers use the file's own namespace or its permitted auxiliary namespace.
- The updated repository format guard reports only the expected two failures:
  no theorem, and no fully qualified final theorem at top level.
- The guard found no prohibited words, quotes, root qualifiers, attributes,
  options, imports, or namespace errors.
- No added axioms or proof placeholders appear in the source.
- At review time, no tracked repository files were changed; the only untracked
  additions were this proof file and the team's `results/` directory.
- Exclude generated `results/orch/lemmas/__pycache__/` binaries when staging.

Source review passes for a clearly labelled partial checkpoint, conditional on
the named Lean build succeeding. The root agent owns the build and must record
its actual result; it was still running when this review was written.

The local full-statement checker cannot accept this checkpoint because its
required theorem is absent. All `results/` files must be absent from the final
proof PR diff, which must add exactly one named Lean file. A final proof needs
a fresh independent review, named build, full local checker, and capped cleanup
verification before delivery.

## Matching and maximal-gate checkpoint extension

The root reports that the baseline named build passed and was preserved in
commit `a7459d04`. This review covers two new helper namespaces, not a final
proof of the posted gap.

The 204-line `PEqualNP.Outside.L_meta_1031.Matching` block from
`results/orch/lemmas/constructive_matching.lean` has SHA256
`e281f861d7a90f7404bad08141159b431c3bc37405fa0bac1eac5a364c0f0394`.
Its contract is sound:

- The endpoint-list `Nodup` hypothesis and exact edge enumeration describe a
  matching, including the empty graph and arbitrary isolated vertices.
- The construction has `2 * es.length - 1` gates, interpreted as zero for the
  empty list, and computes the graph edge function on every Boolean input.
- The lower bound counts all distinct essential endpoints. It holds for any
  fan-in-two circuit computing the function; the displayed minimum therefore
  covers every monotone competitor required by the posted statement.
- Every constructed AND reads an actual edge's two input variables directly.
  The inherited `OwnsPair` definition expands to the posted wire-ancestry
  condition, and `direct_stars` supplies both nonempty ownership and its center.

The `PEqualNP.Outside.L_meta_1031_aux.Maximal` block from
`results/orch/lemmas/minimal_cone.lean` has SHA256
`56362a5ec869d85d1ae67a23eedc27fc7ab7d51b833de0255cce19d72ac9cf29`.
The new `wireStep`, `downstream_difference`, and `minimum_top_gate_sound`
declarations were reviewed. The dependency relation requires strict increasing
wire indices and actual gate inputs. A positive witness lost by deleting the
gate supplies an OR-only path to the output; hence any input activating that
gate activates the graph function. The hypothesis allows unrelated later ANDs.
It does not establish soundness of gates with AND descendants and does not
resolve the remaining normalization problem.

Both new blocks pass all format rules except the intentionally absent final
theorem. No forbidden declarations, tactics, root qualifiers, quotes, options,
or attributes were found. Their separate successful compiles were reported by
the owning agents; root must complete the combined named build after appending
the reviewed blocks. Review passes for that partial checkpoint if it builds.

## Exploratory finite-search review

Reviewed `results/orch/lemmas/counterexample_small.py`, SHA256
`4082e37ccf5c8d2a6a7bff08a3b3a62f946cc7fd148de4e80a0ae578cdb2cda7`.
Graph enumeration correctly filters triangles and pairs of distinct common
neighbors (four-cycles). Breadth-first search explores sets of available truth
tables using binary AND and OR, discarding operations that add no new function.
State deduplication preserves reachability and minimum gate count in that model,
but retains only one topology per semantic state. Therefore a witness with bad
ownership would not establish a counterexample to this existential statement.
Constants, unary gates, repeated inputs, duplicate functions and forward reads
are omitted; treating this as the exact posted circuit model requires the usual
redundancy-elimination argument, which this Python search does not certify in
Lean. The search remains exploratory.

An independent evaluator recomputed complete truth tables and all AND-ancestor
ownership conditions from the emitted programs. It validated 37 four-input
witnesses, all 170 witnesses in the five-input depth-four run, and all 290
witnesses in each five-input depth-five/depth-six run. Every validated program
computes its claimed graph function and every AND owns a nonempty star. Twelve
five-input graphs remained unfound at depth six. Full independent evaluator
output is saved in `/tmp/oec/pequalnp-pilot-59/independent-finite-review.stdout`
and `.stderr`.

## Positive-formula and intrinsic matching extensions

Reviewed the 159-line `PEqualNP.Outside.L_meta_1031.ReadOnce` namespace from
`results/orch/lemmas/exchange_readonce.lean`, SHA256
`593215adc411a3f1ce41e6d8fda5cf39e3250998095b195651da2929ec401002`.
The compiler recursively emits a fan-in-two monotone circuit with exactly one
fewer gate than the formula's leaf count, preserving all original input wires
while combining the two compiled subformulas. `compact_formula_minimum`
assumes a positive formula representing the graph function whose leaf count
does not exceed the number of nonisolated vertices. The essential-input lower
bound then proves its compiled circuit globally minimum among the posted
monotone competitors. This is a conditional minimality result; it does not
establish such a formula for arbitrary graphs or assert the ownership property.
No mathematical-contract issue found.

Reviewed `degree_one_edge_list` and `degree_one_optimal` added to the Matching
namespace in the 591-line version of
`results/orch/lemmas/constructive_matching_compact.lean`. The full Matching
block has SHA256
`fb7a0f70ef6d73999fdf2ed10c890e2821a252f9b07ed73cb088ff02a03a2829`;
the added declarations through the closing namespace have SHA256
`31e74108a0c7590fbba805b504c21d00d931585e13fbf305014bd4e0e580dade`.
The prior Matching declarations are byte-identical to the earlier reviewed
block. Orienting edges by the strict vertex order gives one representative per
edge; the intrinsic at-most-one-neighbor hypothesis implies distinct edges
have disjoint endpoints. The previously reviewed matching theorem therefore
supplies full minimality and ownership under that intrinsic hypothesis.

Both namespaces pass the updated source guard except for the expected absent
final theorem. Review passes for a partial checkpoint after the combined named
Lean build succeeds. The owning agent confirmed its latest successful compile
covers the exact 591-line compact source; the earlier 599-line count was stale.

## Recording the actual local-checker verdict for a partial

After renewing the lease, the root can run the normal checker on the exact
posted statement and the partial target. Set `PEQUALNP_REAL_LAKE` to the
task-local Lean 4.36.0 `bin/lake`, `PEQUALNP_HOME` to the task-local build queue,
and prepend that toolchain's `bin` to `PATH`. From the repository root run:

```sh
node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_1031.lean /tmp/oec/pequalnp-pilot-59/statement.txt check
```

Capture complete stdout and stderr separately and preserve the actual exit
status. The verifier's expected result for this theorem-free partial is
`REJECTED (no-theorem)`, exit 1; that remains an expectation until observed.
The format guard separately refuses the absent theorem. Neither result may be
reported as acceptance, even when every helper compiles. Any checker fault
must be recorded as a fault rather than replaced with the expected rejection.

## Cycle witness, filtering obstruction, and pair-clause helpers

Reviewed the following namespace blocks. All source guards report only the
expected absence of the final theorem; their owners report successful standalone
Lean compiles. Approval is for merging these helpers into a partial checkpoint,
conditional on the combined named build succeeding.

| Block | SHA256 |
| --- | --- |
| C5 witness in `L_meta_1031_aux` | `a67cb1d8aa90666e00893cf643934b7802a159915f9c83ef4118cc9aee2f1ee0` |
| `L_meta_1031_aux.TwoDirty` | `8f83385b024a82cd3413c10c5ac23dff3e27cc213554f8e90edd18996bd49ed6` |
| `L_meta_1031.PairThreeCNF` | `510d0481c271da86fa5b324bdbf7e2eff13fe9a1542e14f7aa0800f129523fc7` |
| Pair-owner extraction in `L_meta_1031_aux` | `35990fbf2fd0b9428111c761400bb75c9024cc559fbde27e190851700d8a01a4` |

The C5 block proves an explicit seven-gate circuit computes the five-cycle
edge function, with allowed gates, no graph triangles/four-cycles, a star
profile, and nonempty edge ownership at every AND. The block does not prove
the lower bound seven; report it as a witness, not a new optimum theorem.

The TwoDirty block computes the two-edge matching through two overlapping
rectangle filters and a final AND. Both intermediate ANDs own disjoint graph
edges, so their ownership has no common center; the final AND owns no edge.
The circuit nevertheless computes the correct graph function. Every gate is
essential under false deletion, and replacing any gate by any earlier wire
changes the function. An explicit three-gate circuit computes the same function
as this seven-gate circuit. Consequently these are obstructions to naive local
rewrites or to dropping the minimum-size hypothesis, not a refutation of the
posted gap. The source uses ordinary kernel-checked finite decision proofs.

PairThreeCNF first proves that a triangle-free graph represented exactly by
three pair-hitting clauses has two disjoint clause sets and is bipartite. Its
extension adds the four-cycle restriction and derives a vertex cover of size
at most two: unless one side already has size at most one, each side intersects
the third clause in at most one vertex, since two such vertices and two opposite
vertices would yield a forbidden four-cycle. This checks the represented-graph
contract; it makes no assertion that an arbitrary circuit has this form.

The pair-owner extraction block chooses the globally earliest active AND, so
it owns the given pair and has index at most the original gate. It does not
claim this owner lies in the original gate's dependency cone. The subsequent
soundness argument only needs some owner, so the weaker ancestry conclusion is
sufficient. Unsoundness on any input consequently yields an owned nonedge,
possibly a repeated-endpoint pair, when the input count is positive. This is a
necessary obstruction, not its elimination.

At this review's staging inspection the Git index was empty, so no credentials
or generated artifacts were staged. The untracked Python `__pycache__` directory
still exists and must remain excluded from named staging. No credential-bearing
files were opened or copied during review.

## Emergency preservation after lease loss

The root reports a desk HTTP 410 at 02:36 UTC. No build, checker, or proof
research was started by this reviewer after that report.

The 4,260-line target was independently compared with its 3,977-line committed
predecessor. The old source is an exact byte prefix; the appended source is
only the four reviewed C5, TwoDirty, PairThreeCNF, and pair-owner blocks. The
target's PairThreeCNF is exactly the previously reviewed 120-line namespace,
SHA256 `510d0481c271da86fa5b324bdbf7e2eff13fe9a1542e14f7aa0800f129523fc7`.
The complete target SHA256 is
`8a412529ff2014b5250528c4ed71e1843ec5694e56a8682ecff35f6671460038`.
Approved for immediate preservation as individually compiled components on a
previously built baseline. The assembled target has not had a combined build
at this point; no full-theorem or checker-acceptance claim is warranted.

The already-running standalone PairThreeCNF check subsequently completed with
exit zero, according to its owner. Its 221-line source SHA256 is
`fd56c716626ae3e6ebfb187c68659ce372cfe965dc64a0e006a6b8fc3934ec88`,
and its 219-line namespace SHA256 is
`62fddeba2440d7e470303d1974895812e254699295c7848e2dc9ed023e4871b4`.
The new declarations were reviewed without starting another compile: the
nonempty graph's size-two cover can be chosen as the endpoints of an actual
edge. When both clause intersections are nonempty, their unique vertices are
adjacent by the representation; otherwise a singleton cover and any edge
suffice. The contract keeps all triangle/four-cycle, exact-representation, and
nonempty hypotheses. No format concern found. Approved to preserve this
standalone compiled component as well; it is not yet part of the 4,260-line
assembled target reviewed above.
