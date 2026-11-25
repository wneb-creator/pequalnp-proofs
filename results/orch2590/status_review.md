# Independent review for L-meta-2590

## Initial statement and source review

- The assigned statement excludes a circuit of at most 19 gates computing the exact 10-input Petersen edge function, under `Monotone2` only. `Monotone2` permits empty and unary AND/OR gates and does not impose backward-read or output bounds. A proof restricted to `IsAO2` therefore needs a checked normalization bridge.
- The local full-history filename check found no existing `L_meta_2590.lean`. The structured GitHub PR census for search `2590`, all states, returned an empty JSON list. The desk response reports no open proof PR and three live reductions, so reduction capacity is full.
- `L_meta_4033.lean` proves the nine-vertex Petersen-minus-vertex-9 function needs at least 16 ordinary gates, even allowing NOT gates. Its internal `monoRoot` is the directly relevant monotone certificate. The full file is 521,569 bytes, leaving only 2,719 bytes beneath the 512-KiB ceiling; a reusable final proof should extract the monotone dependency closure rather than copy the full signed branch and certificates.
- `L_meta_5971.lean` supplies generic signed restriction machinery but its final nine-vertex bound is only 13 binary gates. `L_meta_8113.lean` concerns a 42-input projective-plane dirty-pair normalization, not a completed Petersen bound.
- Existing reductions cover: (1) all first AND/OR possibilities on 30 extremal rows; (932) semantic trace normalization into canonical edge-OR, nonedge-OR, or edge-AND branches with forbidden earlier raw cases; (491) a compressed guarded-input representation plus two truth-table exclusions. All decisive exclusions/compression remain hypotheses in those reductions.

## Search-source preservation audit

`anneal.cpp` is byte-for-byte identical to the previously reviewed `results/orch2583/anneal_readone.cpp`, SHA256 `5c2419be8e1325a84d09b3ac5aaf51f898c2eb302ca9d59bdab67d1820d1d7e7`.

The neutral adjacent-gate swap checks that the second gate does not read the first, swaps payloads, and exchanges the two output labels in every later gate and in the circuit output. Thus it preserves backward validity and semantics. The explicit-output parser and capacity checks remain present. READ1 guidance affects heuristic scoring only. A candidate is accepted only after an independent evaluator checks every assignment (1,024 for Petersen); no search failure or SAT timeout is a formal impossibility result.

Verdict: PASS for preserving the heuristic search source, not a proof of the assigned lower bound.

## Petersen graph component

`lemmas/PetersenGraph.lean`: 65 lines, 2,425 bytes, SHA256 `a1d72e82a1afb5b65958d01f7a79e4f826e38d06a7b7058b65b655118e0b205d`.

The graph uses precisely the posted 15 edges and symmetric adjacency. Kernel-checked finite propositions establish 15 edges, no four-cycle, vertex-cover lower bound six, an explicit six-vertex cover, and equality of the graph predicate with the posted Boolean function. The finite decidability witness is explicit; there is no global instance. The `2590-petersen-graph4.stdout` and `.stderr` logs are both empty. Official plain/import/namespace parsing passes after appending an in-memory parser-only trivial final theorem; that sentinel is neither saved nor compiled and is not a claim about the assigned theorem.

Verdict: PASS for preserving this graph component. It does not establish the circuit lower bound.

The final compiled graph snapshot supersedes that initial hash: 69 lines, 2,645 bytes, SHA256 `728d616dff660527a804524eae9d40279b37f18eed7ddffe2de512e217c6a403`. Delta audit PASS: `graphDec` becomes an abbreviation and two finite proofs explicitly unfold adjacency; mathematical claims and finite witnesses are unchanged. The final snapshot also passes official plain/import/namespace parsing.

## Exact extremal boundary

`lemmas/Boundary.lean`: 79 lines, 2,636 bytes, SHA256 `3d2aa6c6ccc0b03ff55da539ce96b93d314f3fd0d827fd702a4a59ccb063237d`. Confirmed successful `2590-boundary3.stdout` and `.stderr` logs are empty.

The positive rows are exactly the 15 graph edges; the 15 negative rows cover all false assignments from above. The cover propositions and target values use kernel-checked finite decisions. `exact_of_boundary` applies monotonicity upward from positive rows and upward toward negative rows in the correct directions. `replacement_from_dominance` exposes its old computation, monotone context, new monotonicity, and both boundary implications explicitly. Its positive implication is old wire true implies replacement true; its negative implication is the reverse, precisely the polarity needed for the replacement argument. This is a function-level replacement theorem, not a circuit-cost normalization theorem.

Verdict: PASS for preservation. Official plain/import/namespace parsing also passes with the parser-only sentinel.

## Conditional TopForm search pruning

The proposed search restrictions are mathematically sound provided the searched circuit is least in `IsAO2`, satisfies `TopForm`, and every gate lies in the output cone. This review is not a formal normalization certificate.

Every wire below the target has a below-target AND ancestor: raw inputs fail on their singleton assignment, and a below-target OR must have both operands below target. Hence an AND with a below-target operand violates TopForm. An OR with one below-target and one non-below-target operand is non-below-target; its below-target AND ancestor prevents every path to the output from crossing a later AND, so a false-target witness would propagate to the output through OR gates. Such a mixed OR cannot occur in the pruned cone.

The below-target OR gates therefore form a final join network over the below-target AND tops. It can be replaced by a chain of one fewer ORs than tops. Every top needs a private minimal-edge witness: if its accepted edge set is covered by the other tops, their monotone union still computes the exact edge function, and removing that top and rebuilding the final join saves gates. An empty or already-covered current top can consequently be rejected if all generated tops must survive in the final output cone. Later tops cannot restore a lost private witness. These filters must not be presented as valid for arbitrary non-TopForm circuit enumeration or a search that silently discards charged prefix gates.

## Monotone restriction compiler

`lemmas/SemanticRestriction.lean`: 461 lines, 20,777 bytes, SHA256 `56f56bb81172d62d7601917f358bbf41f227bade8bf3014c30e8dbf028368e8e`.

The prefix is exactly the existing L7961 source through before `single_drop`, except the assigned namespace rename and trailing whitespace. It handles empty/unary gates and missing or forward wire reads through explicit constant/wire status values. New declarations count deleted gates exactly, characterize membership by the state before each gate, and charge any finite set of distinct erased gate indices. The restricted function is explicitly assumed nonconstant so the output does not require adding a constant gate. Direct readers are charged under either assignment; a reader of an AND killed by a false input is charged only with the required strict gate ordering. No minimality assumption is hidden in the counting lemma.

The confirmed successful build logs `semantic2590-restriction.*` contain only three simp suggestions and empty stderr. Official plain/import/namespace parsing passes with the same in-memory parser-only sentinel described above. Verdict: PASS for preserving this generic component; it supplies no complete Petersen lower bound by itself.

## READ1 SAT propagation

Reviewed `counterexample.cpp` at SHA256 `23c993e41f8493470b1ca1c56c4e8e720ffc8c91d6743ce04699183202a3e65c`. The selected proof flag is equated to the selected source flag. Singleton-once proofs propagate only through OR. Pair-once proofs propagate through OR or through an AND of opposite endpoint singleton proofs. The CNF implications enforce these equivalences in both directions. The last-active-gate guard is `padding[g] OR NOT padding[g+1]`; it activates the READ1/nonREAD1 restriction exactly before the identity padding suffix. An independent evaluator tracks capped endpoint multiplicities and checks encoded counts.

Verdict: PASS for these encoding additions as research machinery. For a nonREAD1-only search, general dominance normalization must be justified by the READ1 lower bound of 20 (making every correct circuit of size at most 19 nonREAD1), or by a separate preservation argument. It is not automatically valid for arbitrary nonREAD1 circuits of larger size. No UNSAT certificate is claimed.

## READ1 Petersen lower bound

`lemmas/ReadOneLower.lean`: 1,970 lines, 97,386 bytes, SHA256 `fa6d0a4cad3e42981eefe5203a398adc9a4d32a22248f59c678425df0e18b207`.

Verified exact composition: the previously reviewed `ReadLower.General` prefix from the L2583 work, renamed to L2590; the final graph component at hash `728d616d...`; and the exact 25-line specialization suffix. The generic cover bound, no-four-cycle certificate, 15 edges, and cover size at least six imply circuit size at least 20. Hypotheses explicitly require `IsAO2 10`, exact Petersen evaluation, and `IsReadK 10 C 1`. The corollary correctly negates READ1 for size at most 19. No preservation of READ1 across a public `Monotone2` normalization is claimed.

The confirmed successful `2590-read-one-lower.*` logs contain only inherited warnings and empty stderr. Official plain/import/namespace parsing passes with the parser-only sentinel. Verdict: PASS for preservation of this restricted lower bound, not the unrestricted assigned theorem.
