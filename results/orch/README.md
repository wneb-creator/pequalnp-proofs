# L-meta-2585 — partial results only

This branch does not prove or refute the posted statement. No proof PR has been opened.
The task asks whether every binary monotone circuit for a C4-free bipartite edge
function has an equally small read-1 replacement.

The named module is `lean/PEqualNP/Outside/L_meta_2585.lean`. Its checked components
are assembled without proof edits from the sources listed in `assembly.json`.
The latest exact build, source hash and line count are in `validation.txt`;
`logs/` retains complete stdout and stderr. The official local checker exited 3
because its full prebuilt Mathlib cache was unavailable; it gave no proof verdict.

## Checked components

- `lemmas/SinglePoint.lean`: the exact replacement theorem when P=1, with arbitrary L.
- `lemmas/FamilyCombined.lean`: an affordable star cover produces a read-1 replacement.
- `lemmas/Normalization.lean`: size-preserving OR normalization and incidence specialization.
- `lemmas/LeastNormalized.lean`: a globally least equivalent normalized circuit whose
  every gate is essential to accepting an incident pair.
- `lemmas/CleanReadOne.lean`: the normalized case with no dirty AND gates is read-1.
- `lemmas/MixedLinear.lean`: a sharp OR-gate lower bound for fixed pure row outputs
  with pairwise neighborhood intersection at most one.
- `lemmas/Prime.lean`: incidence prime implicants are exactly its incident pairs.
- `lemmas/ClosedIncidenceTests.lean`: edge positives and maximal-independent negatives
  suffice to verify a monotone candidate.

The missing step is an affordable star cover for an arbitrary least circuit with
dirty AND gates, or another size-preserving way to remove repeated reads. The
construction and normalization results do not establish that missing cost bound.

## Obstructions and searches

`DirtyBlockExample`, `HigherDirty`, and `FreshCostExample` are checked examples
against stronger attempted intermediate claims. None refutes the leased statement.
The last gives six doubly reread edges in an eleven-gate circuit with a seven-gate
read-1 replacement; the checked optimality wrapper proves that seven is the actual minimum.

`searches/` contains source, controls, exact invocations, hashes and retained logs.
External SAT UNSAT results are computational evidence, not Lean proofs. Timeouts,
interrupted runs and negative heuristic searches are UNKNOWN. Every claimed
positive control is distinguished from a sought counterexample. Detailed scope
and independent reviews are recorded in `NOTES.md` and per-search READMEs.

`TIMELINE.md` records strategy and build milestones. The root held the only lease
used by this team and renewed it every five minutes. Sub-agents never submitted
or released a lease.

## Final stop

The desk invalidated this job's lease with HTTP410 despite its last returned expiry.
Both permitted recovery requests returned the same pre-existing lease belonging
to another pilot, with the shared-handle five-gap limit. Work stopped under the
user's explicit rule; that other lease was neither worked nor released. No live
lease belonging to this job remained to release. See `desk-recovery.json` and the
full diagnostic headers/body in `logs/desk-beat-error.txt`. Desk null count:0.
