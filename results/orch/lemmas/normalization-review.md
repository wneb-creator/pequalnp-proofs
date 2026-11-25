# Independent normalization review

2026-11-25 UTC. Reviewer: repo_review. Source-only mathematical and format review; no builds, desk calls, git writes, or edits to the reviewed Lean files. Root reports Rename.lean has compiled successfully; this review is independent of that compilation.

## Verdict

PASS for preserving Rename.lean as checked partial helpers. PASS for the mathematical content of PrefixMin.lean, pending its compilation. Neither file alone proves the posted existential statement.

## Renaming semantics

The wire map changes exactly the original n input indices. Every index at least n is fixed, including the extra suffix inputs, previous gate outputs, self/future wire references and permanently out-of-range indices. This is the right transformation for this repository, whose malformed references read false rather than being rejected by a well-formedness condition.

The fold invariant quantifies over every natural index, not merely valid wires. Its induction starts with arbitrary old/new lists of equal length at least n and a corresponding getD relation. The append step uses wire f i = old.length iff i = old.length, valid because old.length is at least n. Therefore invalid/future reads cannot accidentally become valid through input renaming. Output indices are renamed too, as required if the circuit outputs an original input directly; invalid outputs remain invalid.

The evaluation direction is correct:
renamedCircuit f C evaluated on (x ++ suffix) equals C evaluated on ((x composed with f) ++ suffix).
It holds even for noninjective input functions. A permutation is needed later for distinctness/order transport, not for this semantic identity. The separately proved wire_injective uses precisely that needed injectivity hypothesis.

Circuit size is unchanged because gate renaming maps the gate list one-for-one. Monotone2 is preserved because each gate operation is unchanged and mapping inputs preserves list length. This also covers constants, unary gates and repeated wire inputs permitted by Monotone2.

Integration caution: use n=14 to rename the residual circuit while fixing prefix wires14 and15. The suffix in the evaluation lemma is the SAME suffix on both sides; the full prefix transport proof must separately establish that its renamed prefix computes the original prefix on x composed with sigma. Sorting the two input indices is valid only after applying AND/OR commutativity and permutation injectivity.

## Prefix minimization

prefixScore exactly matches the posted arithmetic expression. prefixRename matches the posted extension of a14-input permutation that fixes wire14. prefixWitness retains the target order, operation, Monotone2,24-gate budget and evaluation requirements, omitting only the canonical-rank clause.

minimum_prefix uses Nat.find on scores of ACTUAL witnesses. This is valid even though circuit syntax may admit infinitely many malformed wire indices: only inhabitedness and well-ordering of natural scores are needed. It does not assume decidable synthesis. Classical choice is permitted.

canonical_prefix correctly combines global witness-score minimality with the supplied transport hypothesis. The transported witness score is rewritten to the exact target rank, producing the desired inequality for every function automorphism. It is conditional on existence and transport, which still must be proved before the posted theorem is complete. No circularity or weakened target was found.

## Format

Both files use only the allowed PEqualNP.Defs import, ordinary definitions/lemmas and allowed helper namespaces. Scope declarations and matching ends stand at column0. No _root_, string literals, attributes, options, sorry, new axioms, native_decide, bv_decide or unsafe tactics found. No project type/instance introduced.

For integration into the one assigned file: retain only its initial imports; copy helper bodies with their own fully named namespace blocks before the final fully qualified theorem. Standalone helper-only files are preservation artifacts, not admissible final proof submissions because they lack the assigned theorem.

## Update: complete PrefixNormalize transport review

Reviewed the272-line PrefixNormalize.lean and its normalize-check.log. PASS for immediate checked-partial preservation. Root reports exit0; log contains only deprecation, linter and profiling messages, with no proof errors.

The new prefixIndex extends sigma to Fin15 by fixing14, and its injectivity follows from the existing wire-map injection. Its value lemma proves equality with the exact prefixRename used by the posted statement, including the Fin.ofNat boundary case.

transport_prefix takes the original witness and maps the first pair by sigma, the second pair by prefixIndex, then sorts each pair with min/max. Strict inequalities follow from original distinctness and injectivity. AND/OR commutativity justifies both sorts without changing values or operation tags.

The permutation direction and suffix bookkeeping are correct: u is op1 evaluated at x(sigma a),x(sigma b), hence exactly the original first gate evaluated on x composed with sigma. Rename.initial with the common suffix[u] gives the second-gate input correspondence. Rename.eval is then applied with the common two-element suffix[u,second]. The original witness at x composed with sigma followed by the given function-automorphism equality yields F x. No inverse permutation is missing.

The result preserves the24-gate residual budget and Monotone2. score_sorted together with prefixIndex_val yields precisely the rank of the permuted original pair, including the fixed prefix wire14. This discharges the previously abstract transport hypothesis; only existence of an uncanonicalized prefixWitness remains needed for the global canonical result.

All helper declarations remain in allowed module namespaces, imports only at the top, matching ends at column0, and no forbidden text/tactic/option was found. Preserve as partial work until the actual existential circuit witness is supplied.


## Pair-clean subgraph bridge review (2026-11-25)

PASS for the 891-line compiled PairCleanSubgraph.lean. Compared against L_meta_1983: ambient G retains cleanliness, no-four-cycle and cross-support conditions; subgraph J supplies the positively hit pairs, counted edges and requested vertex cover. Birth witnesses imply necessary ambient adjacency, so the stated theorem does not require an extra explicit J-subgraph-G assumption. Output singleton rejection and positive J-edge evaluation are correctly used; malformed outputs follow existing default-false semantics. The conclusion is the conditional pair-clean bound, not an unrestricted circuit lower bound. Format scan found no forbidden strings, root escapes, unsafe proof commands or attributes.

## Current-target 20-gate bound review (2026-11-25)

PASS for Heawood20.lean (1101 lines, empty compile log and reported exit 0). Its original 1069-line prefix is byte-identical to accepted L_meta_1483 after removing the full Mathlib import and renaming its namespace/theorem. Independently enumerated all 21 currentEdges and confirmed exact identity-map agreement with the cyclic Heawood relation. current_adjacency uses kernel decide; current_lower20 correctly swaps endpoints for reversed adjacency. It requires exact full evaluation and proves size at least 20. This does not by itself prove the requested 26-gate witness or the separate minimality/padding consequences. Helpers require final one-theorem namespace packaging before a complete proof PR.
