# Independent preservation review

Verdict: PASS for preservation of all eight reviewed components. This is a review of compiled partial artifacts, not a claim that the complete L-meta-670 proof or repository checker has passed.

The reviewer checked the complete retained diagnostic logs (zero errors in all eight), the recorded exit-zero build metadata where present, the current source hashes below, and the current repository guard's `checkPlain` on every source. All eight pass. No added axioms, proof holes, kernel bypasses, forbidden text, string literals, disallowed attributes, or disallowed options were found. No large build was rerun.

## Semantic and source checks

- **RectangleParameterizedProbe:** `roots` and `prior` are explicit parameters. Its checker theorem retains root goodness, valid projected masks, prior impossibility bounds, and exhaustive checking/symmetry premises. The root-subset lemma has the correct direction: impossibility from a larger initial pool implies impossibility from a smaller pool. No numerical bound is asserted without its hypotheses.
- **RectangleWholeCircuitProbe:** `whole_from_imp` has the exact posted nine-input graph conclusion and the explicit unresolved hypothesis `Parameterized.Imp rawP 0 16`. It extracts a `Sol` of the original circuit's complete gate count from all nine input columns; no first-gate restriction or free seed is introduced. All 15 inspected circuit extraction helpers are unchanged from the upstream L-meta-1673 source after namespace conversion. The added `m0_full` is checked by the kernel. Out-of-range reads, empty/unary gates, and NOT gates are accounted for by the original helpers. This is a conditional bridge, not a completed proof of the gap.
- **ParentLiveFastStateProbe:** `fastState_eq` proves equality with the existing decoded `stateSet`, followed by the same validated permutation and `BitVec.toNat` map. `decodeN_eq` preserves each binary operation and default value; `selectLive_map` preserves filtering. The only permutation premise is explicitly retained. The codec cannot assert a lower bound by decoding alone; existing checker soundness is still required.
- **TerminalNodeProbe:** the added disjunct is accepted only with an explicit `ending_sound` proof for the identical child `Impossible` predicate. The proof enumerates every allowed operation and all four keep flags, retaining distinctness, properness, freshness, and existing pool/link premises. The zero-cap case follows from target absence. No unchecked terminal oracle is introduced.
- **RelativeNamespace1673Probe:** independent comparison with upstream L-meta-1673 found only the intended full/relative namespace renaming, source section wrapper, an additional Mathlib tactic import, and renaming the final declaration to `C1673.outcome`. The theorem statement and all proof bodies are otherwise unchanged.
- **ForceBatchProbe:** both forcing functions are proved to be exact identities. The list order and all seven Batch fields are preserved. There is no certificate assumption.
- **ForceBatchIntegrationPrefix:** its entire computational/proof body is an exact prefix of the already independently reviewed ForceBatch adaptation. The row-cut wrapper and two simp additions introduce only the proved identity.
- **CompactMinificationProbe:** independently inverted all declared identifier substitutions and recovered an exact 170,766-character prefix of the original PR12184 proof body. Numerical data and proof steps are unchanged; the benoitrazet attribution, source PR, and revision remain present. The recorded build metadata hash equals the current source hash.

These results are suitable for the work branch's preservation directory. The one-file final PR, exact final theorem, allowed imports, final namespace layout, complete build, and recursive axiom audit still apply to any eventual complete submission.

## Reviewed source fingerprints

| Component | Bytes | SHA-256 |
| --- | ---: | --- |
| RectangleParameterizedProbe | 157243 | `82cf08870a03b5b297d7df98085066334b5048f5bec49454a7071d31851a391e` |
| ParentLiveFastStateProbe | 158581 | `85f503dde5100c23353196a2a2a67fe36a7913eafb15071df78bb5597f76f988` |
| TerminalNodeProbe | 103785 | `71fad0fcba8029ea5bfd9c36f2f2a4cbb96e81fa8c0d3ac9ac8a309ead6b0c03` |
| RelativeNamespace1673Probe | 200602 | `a1e615a32c84dc237d7f6f687f0d36f777947c62c4e06ce351e5238152927c21` |
| ForceBatchProbe | 1444 | `13caed65ac610b020b2b5e218dae94789c4d0acebd9e05b698be340bc629f8c4` |
| CompactMinificationProbe | 159195 | `c8604f9b1003602e10ff07183d29d81cea44f43c55650f1c958a0830581f5385` |
| RectangleWholeCircuitProbe | 166373 | `b0cec01a6a73dd6e8f2f1e00bebb5653b919aaeb55192ca46d9197bfc907a446` |
| ForceBatchIntegrationPrefix | 173747 | `af2502c0b38b70df386e310c4290ab122bbf58704508670d3640f7732fa1fd14` |

Reviewed UTC: 2026-11-25T04:56:37.166098+00:00
Reviewer: /root/status_review.
