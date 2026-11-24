# L-meta-3451: checked partial results, full statement unproved

This branch preserves research artifacts under the owner's push-early instruction. It is not a proof PR and does not have the required final theorem. The exact-statement checker reports `REJECTED (no-theorem)`. A successful build of the helper file must not be described as a proof of L-meta-3451.

The only gap held by this pilot is L-meta-3451. L-meta-1035 remained listed as open at the initial checks, with no matching open PR or upstream commit found; the desk assigned a different gap, so this pilot did not work on 1035.

## Checked mathematics

All project-specific dependencies are from `PEqualNP.Defs`; Mathlib is pinned by the repository. The main partial file is `lean/PEqualNP/Outside/L_meta_3451.lean`, with helpers inside its own namespace.

- `acyclic_incidence` proves the exact requested conclusion for every acyclic incidence graph. `universal_row` and `universal_column` handle the corresponding C4-free cases. The construction has backward-only reads, and every AND implies the entire target function on every input.
- `zResCircuit` restricts arbitrary input coordinates to false or reindexes them. It preserves gate count, monotonicity, backward reads, circuit output, and every gate wire's value. A forced-false AND becomes an empty OR.
- `padSuffices` proves that the global statement without its singleton clause implies the exact full posted statement. Add an isolated point and line, normalize, and restrict them to false. **Its nonedge-normalization hypothesis remains unproved.**
- `lcReplacement` gives sufficient conditions for replacing one gate at the same cost: its new value is pointwise below the old value, and agrees on every incident pair. The full edge function is preserved and every wire decreases.
- `lcZeroSupport` and `lcOneSupport` clean gates accepting zero or one incident edge, respectively.
- The `md` lemmas minimize the count of AND gates that accept a nonincident pair. In the resulting no-larger equivalent circuit, every remaining such AND accepts at least two distinct incident edges. This part does not require C4-freeness.
- `lcStarSupport` cleans a gate whose supported incident edges form a star, **provided an earlier wire already computes their exact neighborhood OR**. That wire's availability is not proved merely from star support.

The principal forest and padding lemmas were audited with Lean's axiom printer and use only `propext`, `Classical.choice`, and `Quot.sound`. Their full output is retained in `axiom-audit.log`. Further helpers have independently reviewed source and successful kernel compilation.

`fsNormalize` also proves singleton cleanup for positive binary-tree formulas, with unchanged full semantics and no larger leaf count. It does not handle sharing or nonincident-pair cleanup, and no formula-to-circuit translation theorem is included.

## Strategies ruled out or still incomplete

`route_obstruction.lean` checks a seven-gate circuit for a two-edge matching. It has one nonedge-dirty AND, but bypassing that AND to either operand changes the output. A clean three-gate circuit is also checked. This disproves a local bypass rule for arbitrary circuits; it does **not** disprove a rule restricted to minimum-size circuits or the posted statement.

Extracting all neighborhood-OR functions simultaneously from a single-output circuit may duplicate shared gates. Neither the forest proof, the star replacement, nor the input-restriction transformation establishes this at unchanged cost.

The remaining main difficulty is normalization on cyclic C4-free incidence graphs. No counterexample to the posted statement has been found.

## Finite evidence

The scripts and complete outputs under `lemmas/counterexample/` are computational evidence, not Lean certificates. All 334 C4-free 3-by-3 matrices were classified into 16 row/column/transpose classes. Their unrestricted and requested-clean minimum sizes agree (0 through 8); all stored witnesses were independently checked on all inputs.

The 4-by-4 census has 18,521 matrices and 59 classes, with 14 connected classes using all eight vertices. All 59 explicit clean upper circuits were independently evaluated on all 256 inputs each. Bounded lower-size synthesis continues separately; a timeout establishes no lower bound. Consult its complete results for the final status of each query.

## Submission boundary

The live gap row has not enabled reductions: global `reductions_open` is insufficient under the repository guard. No reduction or partial-proof PR has been submitted. A valid proof PR must add only the named Lean file, with the exact fully named theorem last and the public statement unchanged. The preserved `results/` artifacts would have to be removed from the PR's net diff while remaining available in these preservation commits.

Sub-agents: six, covering normal forms, finite counterexample search, decomposition, generic restriction, universal-vertex graph lemmas, and independent review.
