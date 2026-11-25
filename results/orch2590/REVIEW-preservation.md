# Preservation-only independent review

Reviewed 2026-11-25T15:24:09.820770+00:00 after the parent reported HTTP410. No new mathematical search or proof changes were performed for this review.

- `results/orch2590/lemmas/FirstNonbelow.lean`: SHA256 `467f08e4ac241a1d89271814490138f2f48573d41af36e8017d113f366b1fd83`, 8515 bytes, 208 lines.
- `results/orch2590/lemmas/EdgeAnd.lean`: SHA256 `dc88b17a72cc7ac96b7c64c077d1e1f8c84cf07d30e390548c0bd537d2cb947f`, 2261 bytes, 58 lines.

## Verdict and scope

No semantic or plain-file issue found in either helper. Parent reports successful standalone Lean checks; the saved final stdout/stderr for FirstNonbelow fourth attempt and EdgeAnd first attempt are empty. I did not independently rebuild after lease loss. Neither helper proves the posted Petersen20 lower bound.

`first_nonbelow_raw_or` explicitly assumes AO2, a lift fixed point, every gate in the output cone, every gate true on some graph edge pair, and no gate semantically equal to a primary input. It selects the earliest gate not below the graph function. Any earlier computed operand is below the function and nonzero: an AND using it would also be below, while an OR using it contradicts lift fixedness. Both operands must therefore be raw inputs; freshness makes them distinct, and edge-pair productivity rules out the AND case. The conclusion is exactly a raw distinct-input OR. No least-circuit normalization or productivity theorem is silently assumed; deriving these hypotheses remains separate work.

`intersect_raw` treats the raw distinct conjunction u∧v and any monotone Boolean function h. If h accepts the pair{u,v}, monotonicity makes the intersection equal the raw conjunction. Otherwise every two-point input is rejected: any pair making the raw conjunction true must equal{u,v}. The corollary states the resulting impossibility under explicit semantic freshness and edge-pair productivity. No graph assumptions are needed or concealed.

FirstNonbelow imports only Defs; EdgeAnd imports one allowed Mathlib module. All declarations are in the respective target subnamespaces. No forbidden constructs, quotes, axioms, string literals, namespace escape, disallowed attributes/options, or credential content found.

## Archived experiments

`andfloor/` contains47 manifest-listed files plus its manifest. Complete solver and driver stdout/stderr are preserved; five-AND and dual-thirteen runs are UNKNOWN, not UNSAT proofs. The only UNSAT results are pinned/immediate encoder sanity cases. No unrestricted six-AND/non-read1 test was started. The13OR witness and its simplification were independently evaluated using1024-bit truth vectors: both match Petersen, with all gates live and valid backward references. The simplified circuit has23 gates,10AND and13OR, so it refutes only the proposed unconditional OR≥14 route. Its independent review is `or13-independent-review.json`.

Research files are branch archives, not part of a one-file proof PR. Their inclusion in preservation commits must not be described as a checked20 proof.
