# Independent validation review: checked monotone cofactor certificate

UTC: 2026-11-25T15:51:49.129773+00:00
Verdict: PASS. The previously preserved MonoBase source now has a successful standalone Lean export, confirmed by the author/root. This confirms the nine-variable certificate only; downstream full ten-variable assemblies remain separately pending.

Exact source: `results/orch2590/lemmas/MonoBase.lean` (not PrunedMonoBase.lean)
SHA256: `e1d85e65b52da547c990de4b3ac2da8fa966657990324c3ef784d1dcee2f050e`
Size: 479175 bytes; 6622 lines.
Export: `results/orch2590/lemmas/MonoBase.olean`; SHA256 `fd8c245893d6eabfe9c650557a123b21ba15039252c462a78cd2e9c79dfd74dc`.

The source bytes exactly equal the version already preserved at HEAD. I also independently reconstructed generate_mono_base.py's specified source ranges from checked L_meta_4332, namespace substitution, and NineMonoFloorSnippet tail; that reconstruction exactly equals the current source. No theorem hypothesis or certificate data changed during this validation run. The earlier semantic review in results/orch2590/REVIEW-mono18.md therefore still applies to this certificate prefix.

The author reports the new run exited 0. Complete archived logs exactly match the scratch run logs:

[
  {
    "path": "results/orch1884/mono-base-checked.stdout",
    "bytes": 55549,
    "sha256": "0df6b57a924818d53f23a6b0d06e1d2b7d3e9ab5d43fda17e8c055d016fcaea1",
    "warning_count": 181,
    "error_count": 0
  },
  {
    "path": "results/orch1884/mono-base-checked.stderr",
    "bytes": 0,
    "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    "warning_count": 0,
    "error_count": 0
  }
]

The stdout contains only warnings (deprecated names, unused simp arguments/variables, and exponentiation-threshold notices); stderr is empty. No error diagnostic was found. This is a Lean compilation result, not the posted-statement checker's verdict.

The exported monoRoot excludes a normalized monotone live computation of the exact nine-variable graph with at most fifteen gates. nineMonoFloorOfCert uses the essential-input witnesses and lower_impossible to expose the general Lower false inputs graph 16 interface. Thus the floor is unconditional in its declared lower-bound model, with constants handled by that model's existing rules. No new axiom or assumed certificate is introduced. This alone does not prove the full ten-variable eighteen-gate bound or the L-meta-1884 goal; those depend on extension files and their own compilation.

Only import: PEqualNP.Defs. All declarations retain the previously preserved namespace PEqualNP.Outside.L_meta_2590.Mono18. That old-gap namespace is appropriate for this reusable archived dependency, but a future named L1884 submission must assemble and rename it within that target file and rerun validation. The source is below 512 KiB. No sorry, axiom, native_decide, forbidden namespace substring, double quote, attribute, unsafe/meta declaration, or unsupported option occurs. No credential material was observed. The reviewer did not author the certificate or the pruning generator.
