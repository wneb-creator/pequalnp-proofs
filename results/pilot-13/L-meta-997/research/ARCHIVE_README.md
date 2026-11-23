# L-meta-997 search and intermediate checks

No artifact in this directory refutes the posted L-meta-997 statement.

## Actual-statement searches

`actual_search_summary.json` summarizes the sustained search from 2026-11-23
22:06:22 UTC through 22:21:39 UTC. `full_family_synthesis.py` builds bounded
SciPy/HiGHS MILPs. The fixed prefix computes all specified meeting OR outputs,
then H as the AND of three disjoint meeting outputs, followed by the unique NOT.
The remaining AND/OR tail is synthesized. Candidate verification uses complete
truth-table bit vectors, and computes the posted refund before claiming a result.

* `full_r6_pq` and `full_r6_yp`: HiGHS returned infeasible for the particular
  n=14 fixed prefix and four-gate tail, using 49 input samples. Infeasibility of
  this relaxation excludes those fixed-prefix constructions. This is a solver
  result, not a Lean certificate or an exhaustive result for arbitrary circuits.
* `full_r7_yp` and `full_r8_yq`: time limits, with no incumbent. Inconclusive.
* `full_r5_control`: time limit despite a known feasible ordinary-OR circuit.
* `full_r5_baseline_verified`: the known circuit was explicitly converted to a
  MILP variable assignment and checked against every constraint. This validates
  that the positive control's timeout was not caused by an inconsistent model.

`evolve_full_family.py` searches a broader n=14 family: only three meeting OR
outputs and H/NOT are fixed; the other 28 gates mutate freely. Each candidate is
evaluated on all 16,384 inputs. The two recorded runs examined 6,150,976 candidates
in total and found no zero-error candidate. This is a heuristic search, not an
exhaustive result. The normalized errors from its two runs use different false
positive weights and must not be compared directly.

`analyze_evolved_family.py` additionally searches compatible exact-OR outputs
already present in a candidate and trims unused gates. Its recorded scan was
time-bounded and incomplete. It omitted nonnegative refunds while looking for
a promising positive margin, and found none in the explored portion.

## Relaxed signature searches

`pair_synthesis.py` searches singleton, heavy-base, and heavy-singleton signatures.
The `n8_control` run found the ordinary four-gate OR of five inputs. `n8_synthesis`
and `n8_union` timed out without candidates. They do not establish infeasibility.

## Verified counterexamples to intermediate claims

These examples are intentionally inefficient circuits. They satisfy the posted
semantic hypotheses, but do not violate its total-gate inequality.

* `switching_example`: all 256 inputs checked; refutes deleting all unrefined
  meeting-light charges and then demanding sufficient heavy-private charges.
* `union_switching_example`: all 4,096 inputs checked; even the union of light-
  private and heavy-private T gates outside all meeting-light charges has size
  five, and the posted refund has size one, while |T|-1 is seven. This refutes
  that blanket-deletion intermediate bound. Its W-chain is excluded by light
  refinements requiring strict singleton-support growth.
* `refined_overlap_example`: all 1,024 inputs checked; exhibits one genuinely
  growing OR gate with proper singleton/heavy supports on both sides. It is
  sound for the meeting output and sound on the heavy window for the disjoint
  output, but does not satisfy the posted refund predicate. This refutes only
  a local overlap-implies-refund claim; joint selection and global counting
  arguments remain possible.

Each example has its Python construction, decoded JSON circuit/signatures,
and complete stdout plus stderr in a `.log` file.

## Checked helper

`refund_extension.lean` proves the automatic refund lower bound from disjoint
outputs of cardinality at least two, using the integrated `light` namespace.
Its compilation succeeded with exit zero and the empty `refund_compile.log`.
The full copied test module is omitted because the root's integrated proof file
preserves the required helper definitions.

## Reproduction and provenance

All solver and example diagnostics were redirected as complete stdout plus
stderr; no `.log` file is merely a head/tail excerpt. The `.json` files preserve
the decoded outcomes or best candidates. The programs contain no credentials.
The current solver scripts include later audit options and equivalent evaluator
optimizations added after some early runs; the recorded model dimensions,
outcomes, circuits, and original logs are retained. The archived original
evolution script preserves the first run's exact pre-weight-option source.

The example programs write their result JSON into the original scratch path
`/tmp/oec/pequalnp-pilot-13/status_review/`; create that directory before rerunning.
Solver scripts accept an explicit output path. No additional package download
is needed when NumPy and SciPy are available.

`archive_manifest.json` lists selected files, sizes, SHA-256 hashes, and totals.
It excludes its own hash to avoid a self-reference, and excludes the duplicate
555-line copied Lean test module.
