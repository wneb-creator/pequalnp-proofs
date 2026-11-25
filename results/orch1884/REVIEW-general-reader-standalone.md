# Independent review: full general effective-reader assembly

UTC: 2026-11-25T16:14:22.385811+00:00

Verdict: PASS for mathematical composition, exact source assembly, internal renames, and final-format scan. Full standalone build is RUNNING/PENDING; no successful standalone build or exact-target checker verdict is asserted.

Source: `results/orch1884/lemmas/GeneralReaderStandalone.lean`
SHA256: `fe3aba339859099b2b5f38b9ad44ab8b41f5072079b12cf7d059160e9104d55e`
Size: 523379 bytes; 7103 lines; only 909 bytes remain under512KiB.

## Exact reconstruction

I independently reconstructed the base from original checked L_meta_4332 using the generator’s explicit deletion ranges. Every retained proof/certificate byte is unchanged apart from the namespace rename. The isNot declaration at original234–236 is retained. The generic nineFloorOfCert bridge is the same separately checked helper, instantiated with unchanged monoRoot and signedRoot to give monotone16 and signed15. No certificate is merely assumed.

The full source then includes the checked circuit compiler, the checked general reader contraction, and its checked concrete wrapper. The compiler’s old cross-module reach_to_signed/signed_floor block is deleted and its single floor call uses the in-file nineSignedFloor instead. Duplicate imports are removed. I reconstructed these transformations exactly and matched the final source byte-for-byte.

- `results/orch1884/lemmas/GeneralReaderBase.lean`: SHA256 `8242ee789c29d292de4d5c50bde66241f8de54356a1df1ac9ad6f559531604dd`.
- `results/orch1884/lemmas/NineGeneralFloor.lean`: SHA256 `f1b11610b17cdde28749ae7841f9079528fe9e5071729ce8598dfa78b2513370`.
- `results/orch1884/lemmas/GeneralReaderBound.lean`: SHA256 `67ed300c2ceb05f5f4ddff3a318b6a0db467ad7b2d8c16ea69820cf645629e4d`.
- `results/orch1884/lemmas/GeneralConcreteReaderBound.lean`: SHA256 `078cb21543e9f4f0433b65f3fbd04adacfa4556de41873d6587d684b6c380a43`.

Ten existing internal helper names are shortened. For each rename, I independently confirmed that the destination token was absent, the source declaration existed, and the complete reverse-token substitution exactly restores the pre-rename assembly. The renames save4745bytes and do not change theorem statements or certificate values. Exact occurrence counts are preserved in general-reader-assembly-audit.json.

## Mathematics and remaining scope

NineGeneralFloor supplies a genuine total sixteen-gate lower bound for the exact nine-variable cofactor: zero paid NOTs use the monotone16 certificate; otherwise the signed15 non-NOT floor plus positive NOT count yields16. The reader contraction fixes x0=false and supplied negative x0=true, deletes every effectively reading gate, and compiles the rest with standard false-default semantics. Its explicit cofactor premise is discharged by this total floor. Consequently the final FanInTwo statement16 + effectiveReaders <= size is unconditional apart from its declared computation assumptions, and size<=18 gives at most two effective readers.

The final theorem still assumes identity-ordered ten inputs plus free negation of x0. It neither performs arbitrary-map/unary normalization nor contradicts the remaining one/two-reader cases. It is a substantial partial helper, not the posted L-meta-1884 theorem. There is no target-theorem declaration falsely claiming completion.

## Format and verification status

Only import is PEqualNP.Defs at the start; no scratch-module import or old outside-module reference remains. All declarations are in the L_meta_1884 helper namespaces. Every option is a permitted numeric scoped limit. No sorry, axiom, native_decide, forbidden namespace substring, double quote, attribute, unsafe/meta declaration, or unsupported option was found. No credential material was observed. The two local generators only read the named proof files and write the named output sources.

The component dependency tests and small general-floor bridge have successful empty logs. The full523379-byte assembly is a distinct compilation obligation currently pending. Any further source edit must recheck the909-byte remaining limit and refresh the exact build/review hash. The reviewer did not author the new compiler, contraction, or assembly; the read-only pruning suggestions were independently compiled only when the full build completes.
