# Independent status and definition review: L-meta-2582

Reviewed 2026-11-25 at approximately 18:34 UTC. No desk calls, repository mutations outside this note, or proof claims were made by this reviewer.

## Status

- The desk statement in the supplied `desk-002.json` asks for a same-size-or-smaller AO2 circuit computing the same projective-plane incidence function and satisfying `ReadK.IsReadK (N + N) D 2`. Its reported open-PR count is zero.
- The public export at `https://data.pequalnp.com/head.json`, generated at 2026-11-25T18:32:08.247Z, points to `data/map/overview.47944fd31eda.json` and then `data/map/program/meta_complexity.6c9c437cafed.json`. The exact node is `[2582, "j", [], "53e90433145c", 1795510802, 0, -1]`: status `j` (conjecture), with no dependency list. Its recorded node timestamp is 2026-11-24T09:00:02Z.
- The same export's `data/graveyard.ada762e6e231.json` has no exact `L-meta-2582` entry. These public records provide no evidence of an accepted proof or refutation. They do not identify current lease occupancy.
- A fresh, fully paginated GitHub open-pull-request census returned 2238 records, containing 2233 distinct PR numbers. Five repeated numbers arose while the live list changed during pagination. No title, body, head reference, or head label matched exact `L-meta-2582` or `L_meta_2582`. This is a live snapshot, not a guarantee against subsequent submissions.
- The separate GitHub all-state search endpoint returned HTTP 422 stating that the repository could not be searched. That search is not used as negative evidence. The open-PR census itself completed successfully with empty stderr.
- No exact 2582 proof file is present in the checked repository. The sole `git log --all --grep=2582` match is `69959db1 L-meta-1320 (#2582)`, which names an unrelated PR number.

## Definition checks

`lean/PEqualNP/Defs/ReadK.lean` defines read-k by joint count vectors for a single proof tree on each prime implicant. AND adds multiplicities; OR chooses a child proof tree. Each entry is capped at `k + 1`, so for k = 2 an actual count of at least 3 stays at 3 and fails the final at-most-2 test. This is not the weaker independent per-variable scalar recursion also present in the file.

The posted `2 <= q` and `N = q^2 + q + 1` imply `N >= 7`; there is no empty-domain shortcut. Every column contains q + 1 points, so the target has true inputs and prime implicants. Point and line wires lie in disjoint halves of the input set. In particular the exact-function hypothesis prevents vacuous read-k caused by a constantly false circuit, a missing output wire, or a single input used as the output. `TopForm.IsAO2` requires AND/OR gates only, backwards reads, and exactly two operands per gate.

An arbitrary circuit computing this function need not itself be read-2: redundant self-AND gates can multiply every proof-tree count while preserving its Boolean function. Removing such redundancy can produce a smaller read-2 circuit, so this observation does not refute the existential statement. No trivial counterexample or definitional loophole was found.

## Relevant checked source

- `L_meta_1942.lean`, final theorem at line 2616, has the same plane hypotheses plus read-2 and proves `N*q <= 100*C.size`.
- `L_meta_2581.lean`, final theorem at line 1044, supplies a corresponding constant-factor lower bound under read-3.
- `L_meta_7684.lean`, final theorem at line 1123, constructs a read-1 incidence circuit from a bipartite vertex cover with size at most the edge count plus the cover count minus one.
- `L_meta_2393.lean`, helper near line 4679, constructs a read-1 plane circuit with `D.size + 1 = N*(q+2)`.

These provide lower bounds under a read restriction and explicit upper bounds. None supplies the required comparison `D.size <= C.size` for an unrestricted given circuit. The missing comparison is mathematically substantial.

Raw public-response and PR-census diagnostics remain in the named job scratch directory with prefix `status2582-`; they contain no desk lease fields. No Lean build was rerun for this status review.
