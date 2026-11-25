# Research checkpoint preservation review

Verdict: PASS for preservation of the versions in `REVIEW-research.sha256`. This is not a proof of L-meta-2583, a global UNSAT claim, or a local checker acceptance.

Scope: 74 previously untracked research/source/diagnostic files, plus the current NOTES, TIMELINE, validation record, named Lean file, and this review's independent finite-check report. The exact 79-file scope and SHA256 values are in the manifest. Files changed or added after that snapshot require a fresh comparison or review. The manifest and this report do not hash themselves.

All inspected files are UTF-8 text without NUL bytes. Source/diagnostic inspection and credential-pattern scans found no credential values, private keys, authenticated URLs, executable binaries, object files, or serialized solver binaries. The C++ files are source. The scripts use local scratch data and local solvers; no environment-secret reads or network calls were found.

## Search claims and validation

- Independently recomputed the 21 Fano edges and 37 maximal independent sets. Their sizes are four (21 sets), five (14), and seven (two). These are exactly the archived positive/negative rows.
- Verified all 336 archived permutations preserve the edge set, with unordered-pair orbit sizes 42, 21, and 28.
- Independently evaluated the archived standard 27-gate circuit and the productive positive-validation witness on all 16,384 assignments: both have zero errors.
- Independently evaluated the archived 26-gate negative fixture and near miss: each has 47 incorrect full assignments. The near miss has exactly one incorrect extremal assignment, 8196. It is not a counterexample witness.
- The three completed unrestricted first-AND runs and the completed productive incident-AND run all report UNKNOWN. Their result JSON statuses and hashes agree with their complete solver stdout and driver logs.
- The two UNSAT reports concern validation restrictions only: a pinned incorrect circuit, and a productive first AND on two point inputs. Neither is unrestricted 26-gate UNSAT.
- The two SAT reports concern the known 27-gate validation circuit. They do not refute the gap.
- The productive-edge condition is explicitly recorded as a search restriction, not a formally established normalization theorem. The broader split was stopped before all cases finished. No complete census result is claimed.
- All eight entries in the existing `search/SHA256SUMS` matched the archived files.

The full finite-check summary is preserved in `REVIEW-research-checks.json`. No solver search or heavy Lean build was rerun for this review.

## Frozen partial logs

`elastic-fano.stdout`, `elastic-fano.stderr`, `or-fano.stdout`, and `or-fano.stderr` are explicitly **frozen snapshots from searches that were still running** when copied. Their hashes identify the reviewed snapshots. The stdout files contain initial best values only and no completion line; stderr is empty. Preserve them only with this partial-snapshot interpretation, and do not stage a later changed version under this review. They provide no finished-run iteration total or exhaustive negative result.

`search/baseline-complete-diagnostics.json` is an archive of full available text diagnostics, including the stopped unfinished split case. The filename does not mean that the full six-case search completed. The notes correctly distinguish the stopped run from completed individual cases.

## Mathematical research scope

`onehot-obstruction.md` explicitly identifies its construction as a pen-and-paper obstruction to a relaxed one-point-at-a-time model, not a Lean-checked result or a counterexample to the full gap. The dual rails are complementary only under the one-hot restriction; the text states why simultaneous true point inputs invalidate the argument for the original function. The finite-field/projective-plane construction is presented as a mathematical argument, not an externally measured result.

I recomputed its arithmetic: q=4096, N=16,781,313; total gate bound 43,732,101,605, desired bound 68,769,820,673, difference 25,037,719,068. The OR/AND bounds sum to the stated total. The gate formulas account for empty parity, all-zero point inputs, and two-input AND/OR only.

The two-junk P5 script and note explicitly concern a nonleast nine-gate circuit with a five-gate replacement. They refute only a local odd-cycle shortcut. They do not claim a least-circuit counterexample. This reviewer authored that example earlier; its preservation check here is a source/diagnostic consistency check, not a separate independent mathematical peer review.

Source-census notes distinguish proved results from conditional reductions, nonminimal counterexamples, and unresolved charging steps. The later external discussion counts in `partial_lean.md` are explicitly attributed to the discussion author and are not reported as independently reproduced computations.

The named Lean file is unchanged from the latest separately reviewed geometry/deletion checkpoint: 399 lines, 18,033 bytes, SHA256 `eba26c08cfd4bc65b81c609fcc820eff7bd9df7264daaa0ff00aa4ac9306969f`. Its import and helper namespaces match the gap; the forbidden-format scan found no issue. The posted circuit target theorem is absent. The validation record consistently says partial build PASS and no checker verdict.

## Next strategy

The most promising structural direction is a least-circuit surgery argument for nested two-junk cores with nonliteral final filters. Bipartiteness does not eliminate these cores locally, and the one-hot obstruction rules out proving the general bound from single-point restrictions alone. Existing L_meta_5391 handles literal final filters, while L_meta_5412 handles two pure flags. A useful extension would quantify the mixed-color OR gates needed by a nonliteral filter and charge them against the star-replacement cost, using constraints from simultaneously true points.
