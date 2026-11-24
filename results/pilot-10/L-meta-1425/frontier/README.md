# L-meta-1425 finite-frontier evidence

This bundle preserves untrusted search/certificate data for all ten exact truth tables in the posted statement. It is not itself a Lean proof. A separate Lean checker must establish every finite barrier, input encoding, target encoding, and upper witness before the posted theorem is proved.

`preservation-manifest.json` lists each source, data file, and complete diagnostic stream with its original absolute path, proposed archive-relative path, byte count, and SHA256. Executables, SAT artifacts, superseded small-budget trials, and duplicate copies of regenerated layers are deliberately excluded.

The target order is exactly the order in the posted statement. The lower-bound budgets are `[5,6,7,8,6,8,6,5,4,8]`; the verified monotone witness sizes supplied by another agent are one larger. This generator proves nothing about those witnesses. The finite search permits any number of NOT operations, so a successful Lean validation would give the stronger unrestricted AND/OR/NOT lower bounds needed for the one-NOT statement.

## Exact finite semantics

A wire is a 32-bit unsigned integer. Bit x is its value on the five-input assignment whose numeric index is x; input i has bit x equal to `(x >> i) & 1`. The initial list is `[2863311530,3435973836,4042322160,4278255360,4294901760]`. NOT is XOR with `4294967295`, and binary operations are bitwise AND and OR.

A state is a sorted list of wires, preserving duplicates and their multiplicities. Layer s records states with s operations remaining. Every initial state is inserted separately into every layer s >= 4, so all budgets up to the selected cap are represented; no one-gate padding claim is used. The list-length bound is `length <= s + 1`.

For a state of width w in layer s > 0, slack is `s + 1 - w`. Each existing occurrence may be consumed by NOT when slack >= 1, or retained as well when slack >= 2. Each unordered pair of distinct occurrences may be consumed by AND or OR. Either original occurrence may also be retained, provided the number retained is at most slack. Duplicate-valued occurrences remain distinct choices. Result lists are sorted and deduplicated only as whole states.

Coverage uses all assignment pairs (i,j) with target bit i false and target bit j true. Equality coverage requires some current wire to differ on i and j. In tight mode, when the child width equals remaining budget plus one, directed coverage instead requires a wire false on i and true on j. The latter is valid only after a Lean proof that a tight run has no future NOT step or retained input; that proof is outside this generator.

A child failing coverage is rejected. A surviving child is inserted in the next layer. At layer zero the only accepting state is the singleton containing the exact target mask. Every preserved final run printed `EXHAUSTED`, and every layer-zero file is empty. These observations are computational evidence, not proof certificates by themselves.

## Reduced pair lists

`pair_reduce1425.cpp` repeats the same full-coverage search while recording, for every rejected child, the nonempty set of opposite-target row pairs witnessing its rejection under the applicable equality/directed predicate. It additionally records all 31 proper sublists of the initial five inputs using equality coverage. A greedy hitting set chooses a common pair list for each target that hits every recorded requirement. The chosen pairs preserve all current rejection decisions, including proper-input-sublist rejection. A selected pair need not have i <= j.

The reduced-search layer files were compared byte-for-byte with the final tight-mode layers for every target and budget. All comparisons passed. These duplicate layer files are omitted from the bundle; their hashes and matching baseline paths appear in the manifest. Selected pair counts are `[10,21,37,54,21,52,21,12,8,54]`.

## Scope and expected checks

The final tight frontiers contain 16,611 states in total. The preserved equality-only baseline contains 28,629 states. Neither representation uses orbit reduction, score pruning, input-variable symmetry, or an assumed NOT-count bound. Full 32-row truth tables are used throughout.

The generators are compiled with `g++ -O3 -std=c++20`; complete compiler output and version information are preserved. Every search command uses a 1,000,000-state cap; no preserved run reached that cap. Complete stdout and stderr are retained. The manifest includes the exact statement and command arguments needed to regenerate each run.

The final trusted proof must independently validate the data. In particular, hash lookup or decoder correctness must never be assumed: the Lean barrier must verify that each retained successor is a permutation of the decoded stored state. The generic unrestricted NatRun checker was compiled separately; compilation of that generic framework alone does not certify these concrete frontiers.
