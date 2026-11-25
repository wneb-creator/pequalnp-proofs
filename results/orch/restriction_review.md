Independent restriction and certificate review for L-meta-2592

The endpoint partial is mathematically sound and follows the plain-file rules: allowed imports and namespace, no forbidden commands, quotes, attributes, or unapproved options. Its endpoint claims handle empty NOT operands, extra ignored operands, and invalid references. It is a partial only and does not prove the posted statement.

The signed certificate in L_meta_670 is stronger than the displayed final theorem: it excludes at most 14 binary gates even when wire negation is free. The generic projected_bound theorem charges every essential raw input made constant by a restriction. Fixing Petersen vertex 9 to false should therefore raise the full graph lower bound to 16 binary gates.

Prepared source files:
- DeletedSigned.lean: 243,603 bytes; a conservative declaration-dependency pruning of the checked L_meta_670 signed certificate.
- Binary16.lean: 288,897 bytes before any elaboration fixes; the signed certificate, a 1,024-row copy of the generic live-wire semantics, circuit extraction, and projection to the deleted graph.
- Binary16 exposes binary_lower, binary_not_lower, and three_not_bound. The intended conclusion is 16 + notCount C <= C.size, restricting size-19 candidates to at most three NOT gates.

The self-contained candidate imports only PEqualNP.Defs and has no sorry or added axiom. Compilation is in progress. It is not a full proof of L-meta-2592.

A proposed extension charging duplicate restricted roots was rejected as unsound in the signed model: (a AND c) OR (NOT b AND d) uses three binary gates; identifying a=b yields a multiplexer which still needs three. Only the constant-root charge is used here.

Preservation reviews:
- Named L_meta_2592.lean, 76 lines / 2,801 bytes, SHA256 af5f01ac5fbbad52b8c1be5b7efab0b9419890efbfe67987d9752609edaf0cb8: finite critical-input witnesses and partner exclusions are sound; format passes. No final posted theorem.
- Final compiled Endpoint.lean, 182 lines / 7,745 bytes, SHA256 97b272a4105befedb2cb8f8df639b6a75c18f63491d5a87f0d377269f349637b: independently reviewed after elaboration fixes; math and format pass. No final posted theorem.

2026-11-25T14:20:41.933840+00:00 DeletedSigned.lean compiled successfully, exit 0. The standalone base certificate is checked; the new Binary16 extension is still pending. Full diagnostics: /tmp/oec/pequalnp-pilot-100/restriction-build/deleted-build.out and deleted-build.err.

2026-11-25 14:42 UTC: Parent confirmed the self-contained Binary16 named-file build passed. The generic signed deletion certificate gives binary count at least 16 with arbitrary free complements. Floor17Data now compiles: 800 operand-critical witness entries, checked in 40 kernel calculations, prove both operands of the first signed binary operation must remain live. The initial monolithic finite check exhausted memory; all diagnostics and source were retained. Splitting checks uses about 3.1 GiB. Projection checks also all passed on the first attempt; three ordinary API/simplifier elaboration errors were corrected, and projection is being cached separately. Conditional first-AND/difference binary floor18 is being developed and reviewed by status_review/structural_proof. The target still requires excluding the remaining one- or two-NOT circuits.

2026-11-25T14:47:22.266540+00:00: GLOBAL FLOOR17 COMPILED. Floor17Data, Floor17Projection, Floor17Proof all passed, and instance-free Floor17CleanData passed after replacing FirstProperty by an abbrev. Final combined extension Floor17.lean is 20,309 bytes and 502 lines. Theorem binary_seventeen yields at least17binary gates for every legal correct Petersen circuit; two_not_bound reduces size≤19 candidates to at most2NOT. Floor18 independently compiled through status_review and gives at least18binary gates when the first normalized operation is AND/difference; at17binary the first operation must therefore be OR. All remain substantive partial results, not the full posted target.
