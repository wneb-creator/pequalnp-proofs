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
- `minimum_dirty_essential` strengthens the previous invariant: each residual dirty AND is essential for two distinct incident edges, meaning zeroing the gate makes the circuit reject those edges. Output-level replacement preserves the full function without requiring every internal wire to agree on every edge.
- `lcLiteralEssential` replaces a gate by a unary OR of a raw input if that input is accepted alone and belongs to every output-essential edge. The condition is explicit; its existence is not established in general.
- The `mf` lemmas derive cross-incidences from a globally safe product of two wires. With two accepted singleton points and two accepted singleton lines on one wire, C4-freeness forces every bad pair of every safe partner wire to be the same pair. A rectangle with at most one missing incidence is a star or at most2-by-2. These hypotheses are explicit; no circuit rewrite or size bound follows yet.
- `frGloballySafeReaders` selects a latest gate accepting an input rejected by the circuit. It is not the output, and all direct readers are ANDs globally implying the output. The gate may be dangling; existence of a reader, mixed singleton support, and gate savings are not proved here.
- `saSafeOperand` replaces an AND by an operand that globally implies the original output. It preserves the full function while increasing wire values. `edUnary_delete` then removes a copy gate, saving exactly one gate; the generic deletion proof also preserves surviving AND wire values under index renaming. `saStrictSafeOperand` composes them into a strict reduction. In a minimum circuit, every AND operand therefore accepts some rejected input; `frMinimumLatestReaders` then proves every reader of the latest globally unsafe gate is a binary AND with its other operand strictly earlier.
- `otFrontier` extracts the output OR frontier, preserving full semantics and bounding root count by suffix OR count plus one. `taFactorCircuit` reconstructs/factors the tail. `raMinimumReaderCard` combines the actual construction and count: the latest globally unsafe gate of a minimum circuit has exactly one AND reader among those output-frontier roots (the additional `raMinimumReaderOne` lemma rules out zero by rebuilding the tail without that gate). This initially counts contributing roots. The subsequent `raAllTailAndRoots` and `raMinimumUniqueReader` results prove that every suffix AND belongs to the frontier and the selected latest unsafe gate has exactly one actual syntactic reader, without assuming away dangling gates. They do not normalize its whole cone or establish the posted AND cleanup.
- `lcStarSupport` cleans a gate whose supported incident edges form a star, **provided an earlier wire already computes their exact neighborhood OR**. That wire's availability is not proved merely from star support.

The principal forest and padding lemmas were audited with Lean's axiom printer and use only `propext`, `Classical.choice`, and `Quot.sound`. Their full output is retained in `axiom-audit.log`. Further helpers have independently reviewed source and successful kernel compilation. The final audit of 26 selected results is retained in `axiom-audit-final.log`; all use only these standard axioms.

`fsNormalize` also proves singleton cleanup for positive binary-tree formulas, with unchanged full semantics and no larger leaf count. It does not handle sharing or nonincident-pair cleanup, and no formula-to-circuit translation theorem is included.

## Strategies ruled out or still incomplete

`route_obstruction.lean` checks a seven-gate circuit for a two-edge matching. It has one nonedge-dirty AND, but bypassing that AND to either operand changes the output. A clean three-gate circuit is also checked. This disproves a local bypass rule for arbitrary circuits; it does **not** disprove a rule restricted to minimum-size circuits or the posted statement.

`uncrossing_local_obstruction.lean` and `star_essential_obstruction.lean` strengthen the local obstruction: in their fixed nonminimal contexts, every one-gate replacement using earlier wires that preserves the full output remains dirty. These do not refute normalization of a globally minimum circuit. The formula filter rewrite works at no larger leaf cost, but preserving all shared intermediate interfaces can require another gate; `formula_fanout_probe.py` checks a multioutput example, not a counterexample to the posted single-output statement.

Extracting all neighborhood-OR functions simultaneously from a single-output circuit may duplicate shared gates. Neither the forest proof, the star replacement, nor the input-restriction transformation establishes this at unchanged cost.

The remaining main difficulty is normalization on cyclic C4-free incidence graphs. No counterexample to the posted statement has been found.

## Finite evidence

The scripts and complete outputs under `lemmas/counterexample/` are computational evidence, not Lean certificates. All 334 C4-free 3-by-3 matrices were classified into 16 row/column/transpose classes. Their unrestricted and requested-clean minimum sizes agree (0 through 8); all stored witnesses were independently checked on all inputs.

The 4-by-4 census has 18,521 matrices and 59 classes, with 14 connected classes using all eight vertices. All 59 explicit clean upper circuits were independently evaluated on all 256 inputs each. The frozen checkpoint establishes matching bounds computationally for50/59classes:34 solver UNSAT results below the upper and16 elementary input-count cases, covering14,033/18,521 matrices. Nine classes remain inconclusive. All12 first-gate branch queries under `theta_split` also timed out; their81-file checkpoint is independently audited. The final five forced-dirty minimum-size queries and one productive-theta query also timed out. Their frozen checkpoints were independently audited and all search workers stopped. A timeout establishes no lower bound.

## Submission boundary

The live gap row has not enabled reductions: global `reductions_open` is insufficient under the repository guard. No reduction or partial-proof PR has been submitted. A valid proof PR must add only the named Lean file, with the exact fully named theorem last and the public statement unchanged. The preserved `results/` artifacts would have to be removed from the PR's net diff while remaining available in these preservation commits.

Sub-agents: seven, covering normal forms, finite counterexample search, decomposition, generic restriction, universal-vertex graph lemmas, independent review, and a fresh fixed-pair conceptual review.

The auxiliary Lean files in `lemmas/` are historical snapshots, often importing the then-current named module. Their declarations are now integrated into the named file. Build that module to reproduce the final checked source; recompiling an older snapshot against it can report duplicate declarations. Logs record each snapshot check at creation.

To reproduce the final checked helpers, from `lean/` run `lake exe cache get` followed by `lake build PEqualNP.Outside.L_meta_3451` using the pinned Lean toolchain. From the repository root, `node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_3451.lean results/orch/statement.txt check` reproduces the missing-theorem rejection. The auxiliary axiom-audit source can be run with `lake env lean ../results/orch/axiom-audit-final.lean` from `lean/`.

## Frozen source and validation

The named Lean file has 6,363 lines and 292,811 bytes; SHA256 `d592bf23259a4c40bd232d62247b6e2ae2ea7fbd6f63239e7abdec67f6fa1a06`. Named build25 passed with 18,419 jobs. The exact checker completed with `REJECTED (no-theorem)` for this frozen source; `final-checker.log` preserves the complete output. The format guard finds only that missing theorem and its required final position. A proof cleanup pass is not triggered because the exact checker does not pass: before/after that skipped pass, 6,363/6,363 lines.

`minimum_invariants` puts global minimum size, two essential edges for each residual nonedge-dirty AND, and the latest-unsafe frontier property in one equivalent no-larger circuit. The subsequent actual-reader theorem applies to that circuit. `ocFilterSplit` and `ocFilterCollapse` prove the conditional Boolean identities recorded in `NEXT_STEPS.md`; circuit construction, general orientation, and private-cone existence remain unresolved.

The final independent audit confirms that only the named Lean file and preservation artifacts differ from the upstream base. All 26 selected final results use standard Lean axioms. No reduction or proof PR is ready; this pilot’s lease was released with reason `other` because global normalization remains unresolved after more than 90 minutes of parallel work. No other pilot’s lease was touched.
