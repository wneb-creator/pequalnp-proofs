# Independent archival review of Fano and Petersen search artifacts

Reviewed 2026-11-25T14:59:57.668895+00:00 by sat_encoding, independently of counterexample agent. Verdict: PASS for archival as computational search evidence and positive controls. No full gap proof, refutation, or solver-UNSAT certificate is established.

## Frozen sources and independent controls

`fano_sat.py` SHA256 `6c21b9a3f84f0918b9aebeb612ac9347b4602c9610ea180f87e0ee6694b12812` was frozen by its author before review. I read all86lines and inspected the selector, gate-semantics, output, symmetry, and optional-pruning clauses.

Independent checker `gap2583/sat_encoding/review_fano_controls.py`, SHA256 `590b7a7260d4c65ebe523da8aceec5ca79acaeaacb13c1c82e3eda6ad82334ac`, imports no search code. It independently enumerated the exact cyclic Fano incidence, all16384 assignments,458 independent sets,37 maximal independent sets,21 prime implicants, and58 test rows. It checked the explicit upper27 circuit and both SAT-decoded27-gate controls on every assignment, strict binary backward AO2 references, and the joint capped count-vector recursion on every incident pair. All21 pairs admit vector(1,1), so the controls are read-one in the intended joint sense. All27 gates have some edge support. Exit0; complete `review-fano-controls.stdout/.stderr`.

Independent checker `gap2583/sat_encoding/review_search_archive.py`, SHA256 `ecf98b67564df6080558a331b165959a5153c9482a9d137b2ddce2ee55efab01`, checks immutable archive hashes and reads actual saved solver models/CNFs without using the search encoder. Both Fano27 SAT models satisfy every clause (159608 baseline,161525 edge-visible), have one-hot source selectors, and decode exactly to the saved circuits. The incomplete26-gate local-search candidate is rejected:47 full truth-table errors, including one minimal-edge input. Exit0; complete `review-search-archive.stdout/.stderr`.

## SAT encoding scope and completeness caveats

Base gate semantics are correct: op=false selects AND, op=true selects OR. Sequential one-hot source selectors and conditional mux clauses choose earlier wires; the standard six gate clauses enforce the correct Boolean operation. Output is the final gate. For AO2 circuits,58 rows are logically sufficient: every true input contains a positive edge, and every false input is contained in one of the enumerated maximal independent sets. The independent checker verified those coverage facts for every input.

The source additionally requires distinct ordered operands, nondecreasing maximum fan-in indices, every nonfinal gate read later, and every input read somewhere. These are useful restricted search conditions; this Python encoding has no checked theorem transforming every arbitrary size≤26 AO2 circuit into an exactly26-gate model satisfying all these conventions. In particular, fixed exact size and distinct operands mean arbitrary padding cannot simply be presumed. Therefore even a restricted UNSAT result would not by itself prove the posted statement. The actual baseline26 probe returned UNKNOWN.

Optional edge-visible pruning requires each gate true on some positive edge row and excludes direct-input ANDs of nonedges. These agree with the intended least-circuit restrictions and pass the27-gate positive control. Our checked edge-invisible-removal theorem supports the minimality argument, but it does not alone establish completeness of the entire fixed-size SAT encoding. No finite formal lower bound is claimed from these search clauses.

The completed dirty-first-AND path/cycle experiments are archived as restricted finite computational observations only. Their UNSAT logs are not Lean certificates, and no general clean-first-AND theorem is inferred. Heuristic C++ sources are hash-preserved, not treated as trusted proof components.

## Petersen archival checks

Read final frozen `canonical.py` SHA256 `21b64eee572dce5fb34e1b0cfcce1b29c33d325637582db7317f1b4d458129cd`. Its base order matches the previously checked unrestricted Lean encN: AND/OR/TRUE/NOT, false sentinel inputs, arbitrary output, at least one NOT, no symmetry or connectivity constraints. Optional cardinality clauses match the checked descending-pair/triple/quadruple and exactly-two additions. Their use in a full gap proof remains conditional on the required NOT-count bound.

The91 selected rows are necessary for the NOT-capable circuit target, but do not themselves give full truth-table equivalence for arbitrary NOT circuits. Accordingly every SAT candidate requires independent full1024-row validation. I independently checked the21-gate/one-NOT and22-gate/two-NOT controls using arbitrary-output and default-false semantics: both pass all1024 rows. All five finalized long Petersen solver logs report UNKNOWN; no unfinished proof trace was inspected or accepted.

## Archive manifests ready for root preservation

Under `gap2583/counterexample/`:

- `archive-review-manifest.json`:72 files,2491340bytes, including final Petersen canonical/source/control/long-run logs and frozen Fano source/controls/completed baseline probe.
- `archive-review-supplement.json`:11 small metadata JSONs,47483bytes, including Fano variable maps and Petersen row/mode metadata.
- `archive-review-completed.json`:9 completed stochastic/structural-control artifacts, including the rejected26-gate candidate.

All92 named files matched recorded size and SHA256. Original manifests were kept unchanged. Counterexample agent confirmed these sources/logs were not yet copied into the branch; only notes had been committed. Root should preserve these92 files, the3 manifests, both independent review scripts, their complete stdout/stderr, and this report. Any still-running search requires a later separately frozen final-log manifest.
