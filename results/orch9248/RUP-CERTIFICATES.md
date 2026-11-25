# RUP certificate validation for PHP(5,4)

The posted L-meta-9248 statement excludes RUP refutations with at most twelve learned clauses. The final checked certificate has fifteen clauses. It improves the earlier sixteen- and twenty-clause examples, but does not settle the posted statement. Work stopped after the root reported HTTP 410 on renewal at 17:14:26 UTC; the fifteen-clause compilation had already finished successfully.

`lemmas/Witness15.lean` is 37 lines and 2,014 bytes, SHA256 `c6a7a29f251b4a836f4b127981caeff543d26c4ba9e1cb2ffc9418b49adada1c`. Its complete successful logs are `/tmp/oec/pequalnp-pilot-103/9248-witness15-first.stdout` and `.stderr`, both empty, exit status zero. It proves a RUP run containing the empty clause with length exactly fifteen. `witness15-input.json` converts the unchanged signed search result `search-alt/run-best-15.json`; `witness15-traces.json` regenerates all traces against the harness database order. No checker verdict on the posted twelve-clause statement was requested or obtained.

`lemmas/RUPHarness.lean` is a 137-line, 5,302-byte, Defs-only checker and soundness proof adapted from the already checked `L_meta_9477`. It replays explicit unit-propagation traces and turns successful checks into the project's inductive `IsRUPRun` proposition. No oracle or native evaluation is used. Its theorem `validated_refutation` accepts the additional empty-clause and length-at-most-twelve checks needed for a counterexample to the posted statement.

The earlier `lemmas/Witness16.lean` also compiles with this harness and proves:

- The generated newest-first list is an `IsRUPRun (PHP 5 4)`.
- The empty clause occurs in the list.
- The list has exactly sixteen entries.

The successful complete logs are `/tmp/oec/pequalnp-pilot-103/9248-witness16-first.stdout` and `.stderr`, both empty; exit status was zero. Source SHA256: `eb629fcc9a0d759852c4fa661cd45e59b393f014f193bf241e76acd1dd1e4cf0`. The harness hash is `8f5f89f7f1abd53fd77eef5c439a8e68780c9308c58a6381ce0542a8529e1cee`.

The original search result is `search-alt/diagnostic-best.json`, using signed DIMACS literals and pair-major input-clause order. It remains unchanged. `witness16-input.json` converts only its learned clauses to the harness format. `witness16-traces.json` contains new propagation traces regenerated against the harness's different, hole-major database order. Those traces were independently replayed in Python before the Lean check.

## Encoding and input order

A literal is encoded as `2 * (4 * pigeon + hole) + sign`, where `sign = 0` means positive and `sign = 1` means negative. Valid integers are 0 through 39. Pigeons range from 0 through 4 and holes from 0 through 3.

The initial database has forty-five clauses: first the five positive pigeon rows in pigeon order; then, for each hole in increasing order, all negative pigeon pairs `(p,q)` with `p < q`, in nested increasing pigeon order. Each checked learned clause is appended to the end of this database. Trace indices are zero-based. Candidate steps are supplied oldest first; `RUPHarness.learned` reverses them to the newest-first order used by `IsRUPRun`.

## Emitting a new candidate

The JSON format is `{"steps": [{"clause": [encoded literals], "trail": [database indices]}, ...]}`. The `trail` field is optional; the emitter computes it when omitted. The last propagation operation must identify a falsified known clause. A candidate must contain an empty learned clause.

```sh
python3 results/orch9248/emit_rup_certificate.py candidate.json \
  results/orch9248/lemmas/Candidate.lean --module Candidate \
  --normalized-json results/orch9248/candidate-traces.json
```

The emitter rejects out-of-range literals, duplicate literals, malformed traces, and clauses that fail unit propagation. It never claims Lean validation itself. For candidates of at most twelve steps it additionally emits the exact existential witness theorem needed to refute the posted negation; longer candidates get only run, empty-clause, and exact-length theorems.

## Rebuilding from the checkout

Use the pinned Lean v4.36.0 installation and warm Mathlib cache. From `lean/`, with the real `lake` available:

```sh
lake exe cache get
lake build PEqualNP.Defs
export LEAN_PATH="$(pwd)/../results/orch9248/lemmas${LEAN_PATH:+:${LEAN_PATH}}"
lake env lean --root=../results/orch9248/lemmas \
  -o ../results/orch9248/lemmas/RUPHarness.olean ../results/orch9248/lemmas/RUPHarness.lean
lake env lean --root=../results/orch9248/lemmas \
  -o ../results/orch9248/lemmas/Witness15.olean ../results/orch9248/lemmas/Witness15.lean
```

Keep complete stdout and stderr for each command when reproducing the check. No `lake update` is needed. The short-name harness dependency is for archived development modules; a final posted-theorem submission must inline it into the single permitted file.

`Baseline20.lean`, `baseline20.json`, and `baseline20-traces.json` separately validate the old `L_meta_9250` twenty-clause certificate through the same emitter and kernel checker. This is a pipeline test, not another claimed improvement.
