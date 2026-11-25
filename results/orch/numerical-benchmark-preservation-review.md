# Independent numerical benchmark preservation review

Verdict: PASS for all four named compiled benchmarks. The retained build metadata records exit zero and matches each current source SHA-256; all four complete logs contain zero errors. The current `checkPlain` guard passes on all four files. No build was rerun.

Each root benchmark copies 174 declarations, and each cofactor benchmark copies 183 declarations, from the full width-278 ForceBatch candidate without any code-token changes. The preludes within each benchmark pair are byte-identical. Only the terminal numerical theorem's grouping changes.

The rootM benchmarks both test level 11, states 186 through 281 inclusive, arity 11, all 55 unordered operand pairs per state: 96 states / 5,280 state-pair checks. The split form uses six consecutive groups of 16; the merged form uses one group of 96. These are row-cut checks and do not include the separate node header check.

The g383 benchmarks both test level 9, states 3 through 118 inclusive, arity 9, all 36 unordered operand pairs per state: 116 states / 4,176 state-pair checks. Original groups 36+36+36+8 with recursive cell splits and replacement groups 64+52 have exactly the same nonoverlapping state range. Both include the same per-state header checks. The full candidate's `cellsBlock` and `spanChecks` logic preserves coverage under these subdivisions.

No numerical data, target, operation semantics, width, or checker predicate changes between each pair. No prohibited constructs or new assumptions were found. These benchmarks establish their stated finite checks; they do not establish complete certificate replay or the full gap theorem.

| Component | SHA-256 |
| --- | --- |
| RuntimeWidth278Split96Benchmark | `726da2427b50840e73dab5c3fb03707e573205c5daa1b7d3b01102295d1adad9` |
| RuntimeWidth278Merged96Benchmark | `c2f4bbf3a99f4ae0918b642e90bf9929df57d4a2979d9e0ed9bb563a92bac52a` |
| RuntimeCofactorOriginalBenchmark | `37d067818229d7e105ca35f7dd3159aabc425212230ff433870e7854934e69ba` |
| RuntimeCofactorGroups64Benchmark | `c9c399f5e544a8d3a2b91bb42b08318516e15c89e21c9eab71481a63bccbbbd7` |

Reviewer: /root/status_review.
