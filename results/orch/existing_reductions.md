# Existing Petersen reductions

Read-only investigation completed 2026-11-25T13:49:14.385798+00:00

## L-meta-2592

The public desk feed at https://data.pequalnp.com/data/desk/gaps.json (updated 2026-11-25T13:47:28.057Z) lists exactly three live/open reductions, matching the three files already on current main. Hence the per-step three-reduction cap is exhausted. No fourth reduction candidate is useful unless one existing reduction dies.

- `R_meta_2592_271.lean`: binary gate floor `15 + notCount C ≤ C.size`, then exclusion when size ≤ 19 and NOT count is 1–4. First child `L_meta_4725.lean` is checked (3224 lines). Remaining child `L-meta-4727` is open.
- `R_meta_2592_408.lean`: normalize invalid wire reads, NOT arity, and output to the last gate, preserving a NOT or strictly decreasing size; then exclude legal normalized candidates. First child `L_meta_7389.lean` is checked (305 lines). Remaining child `L-meta-7391` is open.
- `R_meta_2592_318.lean`: split the final NOT into a prefix circuit P and monotone suffix Q, using `P.wires input ++ [!P.eval input]`, with P.size + Q.size + 1 = C.size. First child `L_meta_8295.lean` is checked (66 lines). Remaining child `L-meta-8297` is open.

The first children are already proved, so reproving them only gives local scaffolding; imports for our gap allow `PEqualNP.Defs` only, so needed proof bodies must be inlined in our one target file.

## Descendants of L-meta-4727

- `R_meta_4727_1`: dead reduction. It merely splits by whether a NOT exists despite the positive NOT-count hypothesis, leaving one vacuous case and one restatement. Avoid this waste split.
- `R_meta_4727_17`: compiles circuits into a duplicate-free list F of AND/OR truth functions, plus ≤k complemented source functions M; leaves lower-bound child `L-meta-6062` open. Compiler child `L_meta_6060.lean` already checked.
- `R_meta_4727_53`: compiles into an arbitrary-binary-function circuit plus a set N of negated wires, |N|≤4, with monotonicity after the selected input sign flips; leaves signed-bound child `L-meta-7229` open. Compiler child `L_meta_7227.lean` already checked.

## Parent L-meta-651 and monotone sibling L-meta-2590

`R_meta_651_7` is the basic split into monotone/no-NOT sibling 2590 and our with-NOT sibling 2592. Both remain open. The parent has two other live reductions: `_1` (first-gate orbit reduction into unary, edge pair, nonedge OR, nonedge AND) and `_2` (last-gate/wire OR/AND decomposition).

The monotone sibling has three live reductions:

- `_1`: test only fifteen minimal true rows (edges) and fifteen maximal false rows (maximal independent sets), then separate first AND versus first OR.
- `_491`: compress one input through a feedback-free guard, then check AND and OR substitutions on the thirty critical rows.
- `_932`: functional straight-line program normal form, remove duplicate functions/nonedge pair ANDs, then reduce by a selected raw edge OR / nonedge OR / edge AND. This is a 760-line proof with useful automorphisms and monotone masking lemmas, but cannot handle arbitrary NOT directly.

## Suggested strategy

Reuse (inline) the checked 4725 binary floor if doing casework: every counterexample has 1–4 NOT gates. Normalization 7389 enables finite SAT encodings with exactly one/two predecessors per gate and output at the last gate. The hard part is genuinely the final finite lower bound, not bookkeeping. Existing cutLast, normalization, and first-gate symmetry reductions should not be independently reinvented.

## Records

Full public feed: `/tmp/oec/pequalnp-pilot-98/public-gaps.json`.
Full concatenated reduction sources: `/tmp/oec/pequalnp-pilot-98/reduction-sources.txt`.

## Checked graph scaffolding

2026-11-25T13:57:34.725790+00:00 Pure graph fragment compiled successfully with Lean4.36.0, exact maximum independent-set size4 and minimum vertex-cover size6. Source candidate: results/orch/lemmas/graph_facts.lean; test log /tmp/oec/pequalnp-pilot-98/graph-finite-check3.log (exit0, empty). Explicit independent witness {0,2,8,9}; complementary cover {1,3,4,5,6,7}. Whole graph has76 independent subsets and five maximum independent subsets, independently enumerated over1024 subsets in Python. The 20-gate witness portion is being tested separately against already-built direct Defs modules.

2026-11-25T14:02:20.191291+00:00 Complete graph_facts candidate (only PEqualNP.Defs) compiled exit0: concrete20-gate circuit, Monotone2, FanInTwo, exact size20, symbolic correctness, HasCircuitSize20, exact independent and cover numbers. Log graph-facts-final.log. Circuit correctness uses explicit input list, Boolean distributivity, ac_rfl; exhaustive circuit decide abandoned as unnecessarily slow.

2026-11-25T14:02:20.191305+00:00 Additional graph_properties candidate compiled exit0: ptFun_monotone and ptFun_essential for all10 coordinates. Neighbor singleton finite certificates use10 cases only. Log graph-properties2.log. Parent should merge only new lemmas because shared graph definitions are repeated for independent testing.
