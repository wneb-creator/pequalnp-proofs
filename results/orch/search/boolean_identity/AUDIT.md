# Independent archive audit

Reviewed and replayed on 2026-11-25 UTC by the structural strategy agent,
independently of the search author. Verdict: **PASS for the saved controls,
boundary sets, composition counts, and consistency of the finished logs.**
No counterexample was found in the recorded searches. No lower bound, exhaustive
circuit search, or proof of L-meta-2583 is claimed.

## Preserved material

The 19 original files comprise six Python sources, six circuit controls,
`summary.json`, `README.md`, and five complete stdout/stderr logs. They were
copied byte for byte from the completed scratch directory. The additional audit
script, two replay logs, this note, and `SHA256SUMS` record the independent check.
The unrun `hyperoval.py`, bytecode caches, and temporary or active artifacts are
excluded. `SHA256SUMS` includes every local file except itself and also the two
existing parent-archive dependencies used by the source programs:

- `../counterexample_q3_repair.py`: PG(2,3) incidence, boundary, and evaluator.
- `../q3-concurrent-control/control.json`: the 66-gate input for the 65-gate seed.

No search was restarted during this audit. Commands were:

```text
python audit_controls.py > audit-independent.log 2>&1
python audit_dataset.py > audit-dataset.log 2>&1
```

Both exited zero. Their complete outputs are preserved.

## What was checked

`audit_controls.py` uses a scalar gate evaluator independent of the search's
bit-packed evaluator. It validates the opcodes and earlier-wire references,
tests every minimal positive incidence pair, and tests every subset of the
right input class with all allowable left inputs enabled. These are complete
semantic checks for each saved monotone circuit: every false input lies below
one of those tested false inputs, and every true input contains a tested edge.

| Saved control | Gates | Positive pairs | Right subsets checked |
| --- | ---: | ---: | ---: |
| direct65-control.json | 65 | 52 | 8192 |
| best-76131.json | 64 | 52 | 8192 |
| two-pencil-best-48.json | 48 | 40 | 256 |
| two-pencil-best-49.json | 49 | 40 | 256 |
| affine-best-45.json | 45 | 36 | 512 |
| affine-best-eligible.json | 46 | 36 | 512 |

`audit_dataset.py` independently constructs maximal independent assignments in
the opposite orientation, confirms maximality and the exact boundary sets,
and propagates squarefree proof-tree leaf sets of degree at most two to check
the recorded non-read-1 edges. The 65-gate seed is regenerated from its archived
66-gate parent and matches the saved control exactly.

The full PG(2,3) boundary has 52 distinct positive pairs and 704 distinct maximal
independent assignments. The two-pencil module has 40 positive pairs and 228
maximal independent assignments; its closed omitted-center sets consist of
225 sets with nonempty row and column parts, plus the empty set, all rows, and
all columns. The affine module has 36 positive pairs and 197 maximal independent
assignments. Its closed omitted-point sets are precisely all unions of its
12 affine lines, with size distribution `0:1, 3:12, 5:54, 6:84, 7:36, 8:9, 9:1`.

For the PG(2,4) embedding, the audit checks the cyclic difference-set plane,
point and line degrees, both pair-uniqueness conditions, and the injective
18-point/eight-line module embedding. It independently reconstructs the whole
embedded gate list. The omitted 13 lines contain 65 remaining edges; each line
adds four OR gates, one AND gate, and one output OR, for exactly 78 gates.
This decomposition proves correctness of the extension from the already
validated module; the audit does not enumerate all 42-input plane assignments.
A regenerated canonical 47-gate module embeds as 125 gates.

The affine embedding adds four omitted point stars, with three OR gates, one
AND gate, and one output OR each, for exactly 20 gates. Each saved embedded
circuit is also checked by scalar evaluation on all 756 full-plane boundary
patterns. A regenerated canonical 44-gate affine module embeds as 64 gates.
The saved eligible 46-gate module embeds as 66 gates, consistent with metadata.

All four final log records match `summary.json`: 74,593 + 18,268 + 16,768 +
21,770 = 131,399 sampled rewrite queries, across 933 + 522 + 350 + 454 = 2,259
starts. The reported smallest sizes are 64 for each full-plane run, 47 for the
two-pencil module, and 44 for the affine module. The smallest saved affine
control meeting the search's present-neighborhood pressure condition has
46 gates. The latter condition and its recorded counts were replayed; it is
a search heuristic and is not independently proved here to be a necessary
condition for a smaller circuit.

## Limits of the evidence

- The rewrite programs randomly sample cuts, cap candidate pools, and retain
  bounded candidate lists. Failure to find a smaller circuit excludes no
  general circuit class.
- Query and start totals are checked against the complete finished logs, not
  by replaying all queries. The logs do not preserve every intermediate
  candidate, so this audit validates saved controls and reviewed validation
  code rather than every historical search transition.
- Wall-time stopping conditions mean the numeric random seeds alone do not
  guarantee an identical future query count or search trajectory.
- Complete scalar validation applies to the six saved controls. The original
  scripts assert full boundary agreement after accepted rewrites, but only
  the controls and the regenerated canonical modules were independently
  replayed in this audit.
- The Python checks supply finite computational evidence and reproducible
  circuit artifacts; they are not Lean proofs or checker acceptance.
