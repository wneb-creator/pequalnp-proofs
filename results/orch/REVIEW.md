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
