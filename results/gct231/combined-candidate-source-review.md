# Combined scratch candidate: independent source-preservation review

`integration/L_gct_231_CombinedCandidate.lean`, SHA256 `455519b9fd760d5ec45d2da6274066654d1cc37123ee75c85ec6192cb54ca5a0`, passes static independent review (2507 lines, 264200 bytes).

The entire original 1528-line snapshot body is preserved byte-for-byte. All six component inner bodies match their separately recorded source hashes exactly: common-plane coefficient identities, binary factor matching, the full C4 coordinate interface, polynomial nonsquare criterion, isolated-vertex theorem, and scoped C4 open-case certificates. The only integration changes are the import union and enclosing section/namespace wrappers. No pre-namespace commands were lost. The existing deprecated complex compatibility import publicly imports the preferred module, so suppressing the duplicate preferred import is sound.

Auxiliary-level opens are contained in named sections. C4Coordinates and IsolatedVertex retain their intended full names; the former trace namespace becomes `L_gct_231_aux.C4OpenCertificates` with no stale qualified references. An independent declaration scan finds 264 fully qualified names and no collisions. The source satisfies the reviewed format restrictions and introduces no admitted proof, new axiom, unsafe declaration, native decision command, or unscoped option. It contains no theorem asserting the posted existential problem.

Standalone checker/full log: `/tmp/oec/pequalnp-pilot-75/gct231/integration/independent_review.py` and `independent-review.log`, completed 2026-11-25T12:08:01.698493+00:00. This was source-only; the combined build and component mathematical proof audits are separate. No named file was changed by this review.
