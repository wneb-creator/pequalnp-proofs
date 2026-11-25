# Independent review: first non-OR binary bound

Reviewed UTC: 2026-11-25T14:28:29.586933+00:00
Reviewer: lean_setup
Verdict: PASS mathematical and format review for a partial-result checkpoint, conditional on successful compilation against the checked Binary17 base.
Source: results/orch/lemmas/Binary18.lean
SHA256: 3ae7fd370997c7f1df3be8ef2f34b1cf54b000d4e2e7fdef03ef4a7a6735760b
Lines: 107

- needed_pin correctly extracts a live original input using two rows where the target differs but every alternative available source, including the first binary result, agrees.
- In the AND/left-difference cases, restriction of that original input to false makes both it and the fresh binary result constant false. They are distinct pre-projection live sources, hence two separate list occurrences. The mass bound legitimately counts both even though their projected functions coincide.
- The projected target is the checked nine-variable graph, and projected initial sources remain available. Applying its fifteen-binary lower bound plus the two constant-source charges gives a suffix bound of seventeen; adding the first operation gives eighteen.
- The new d=3 case swaps the two original inputs: (not v) AND u equals u AND (not v). Distinctness, raw-source membership, freshness, and the tail state are preserved by the swap. Its use of the d=2 case is sound.
- Scope is explicit: first_non_or_floor assumes d.val != 1 and raw remaining initial inputs. It does not establish an unrestricted eighteen-binary lower bound. The OR-first case remains excluded, and none of these lemmas alone proves the posted nineteen-total-gate impossibility.
- The file is an inlining snippet inside the permitted module child namespace, with no imports. It introduces only lemmas and uses the actual Binary17 definitions; no dummy assumptions, new axioms, forbidden commands, placeholders, root qualifier, strings, attributes, options, custom data types, or exported instances occur.
- Scratch validation may depend on an already compiled Binary17 module. The final named file must inline the definitions/snippet with permitted imports and be rebuilt; this review does not treat the scratch dependency as an authorized final import.

Compilation was pending when this review was written. Root must record exit zero for this hash before claiming it checked. No apparent credential material occurs in the snippet.
