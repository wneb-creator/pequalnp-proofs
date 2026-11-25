# Independent review: standalone effective-reader assembly

UTC: 2026-11-25T15:59:48.088350+00:00
Current verdict: PASS for mathematical assembly integrity and final format after the correction documented below. Standalone compilation remains pending. This is a partial preservation file, not the posted target proof.

Source: `results/orch1884/lemmas/ReaderStandalone.lean`
Current SHA256: `58addd4cb4376a368eeb19407dca3262569b7771d9c9fd07116a2760838ce36e`
Current size: 497959 bytes; 6956 lines.

The source exactly concatenates the following four checked components, deleting only repeated imports and replacing the old Mono18 namespace with PEqualNP.Outside.L_meta_1884.ReaderCertificate. No statement, hypothesis, certificate, or proof body changed.

- `results/orch2590/lemmas/MonoBase.lean`: SHA256 `e1d85e65b52da547c990de4b3ac2da8fa966657990324c3ef784d1dcee2f050e`.
- `results/orch1884/lemmas/NineCircuitFloor.lean`: SHA256 `445fcd30f2db31bb9adef82dec09dd90536ebdaa9326173427553a29108d44d8`.
- `results/orch1884/lemmas/ReaderBound.lean`: SHA256 `539e05e920c9a187680a12f748528d879407aaf7b65f562cabff493b8e0c533d`.
- `results/orch1884/lemmas/ConcreteReaderBound.lean`: SHA256 `031cd73a2321e6cb59b5523772e51e80d4ca74e3d31e5afc1e6c4b545c0513c0`.

The final claims remain the Monotone2 identity-input/free-negative-input effective-reader floor and its at-most-two-readers corollary. These do not prove L-meta-1884. The source is below 512 KiB, uses only PEqualNP.Defs, and contains no sorry, axiom, native_decide, forbidden root substring, quotes, attributes, unsafe/meta declaration, or observed credential material.

## Original format finding (now resolved)

The previously reviewed ReaderBound.lean lines 2–3 had global `set_option maxHeartbeats 0` and `set_option maxRecDepth 8192`, copied to assembly lines 6750–6751. CONTRIBUTING.md lines 62–64 requires each option to be on its own line of the form `set_option <name> <number> in`, directly above the declaration it serves. The two inherited lines lack `in` and violate this explicit rule. Remove them or scope them to the declarations needing those limits, recheck the small helper, regenerate the assembly, and rerun its build before claiming final-format success. Root and the author were notified; the reviewer did not alter their proof source.

## Resolved format finding — 2026-11-25T16:03:11.862365+00:00

Current ReaderBound source SHA256 is 252337b6833eadddc4165cd6dbac32f87de9a9e746c70c4e7009d45251839715 (12198 bytes). It differs from the previously reviewed source only by removing the two global-option lines; reconstructing those lines restores the old source hash exactly. The fixed helper recompiled with exit 0, and complete reader-scoped-checked.stdout/.stderr are empty. No replacement options were needed.

The regenerated standalone is 497959 bytes, SHA256 `58addd4cb4376a368eeb19407dca3262569b7771d9c9fd07116a2760838ce36e`. It exactly reconstructs from the four current component sources and the same namespace rename. Every remaining option is now a numeric scoped maxRecDepth/maxHeartbeats option. Mathematical assembly integrity and final-format checks therefore PASS for this new hash. The standalone itself is still UNBUILT; the interrupted old build does not validate this new assembly. The named 395-line source is unaffected.

Unary18Check was also scanned again: every option already has the required scoped `in` form; it did not inherit the ReaderBound issue.
