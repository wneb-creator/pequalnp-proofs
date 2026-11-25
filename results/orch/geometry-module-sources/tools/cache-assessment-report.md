# Full Mathlib cache assessment

The repository checker explicitly imports the complete `Mathlib` environment in `lean/CheckLemma.lean` (statementLibrary at lines63–64; importModules with trustLevel0 at lines355–356). The current targeted cache is enough to compile the proof file, but does not contain every module required by that environment. The checker reported a missing Batteries.olean. No checker code was changed and no full-cache download was attempted.

The Mathlib root file directly imports8,689 Mathlib modules. Of those,2,173 have oleans present and6,516 are missing. Existing targeted dependencies occupy about2.46GB in lean/.lake/packages. The filesystem is8.42GB total; it had431MB free before the counterexample agent safely removed a212MB raw CNF already preserved byte-for-byte in compressed form, yielding about642MB free.

For the2,173 present direct Mathlib imports, the combined public/private/server olean, ilean and IR files have a mean size762,850bytes and median466,978bytes per module. Applying those statistics to6,516 missing modules estimates4.97GB and3.04GB respectively. These are distribution-based estimates, not a verified total download/extraction size. They exclude generated C files and compressed download staging.

Potential generated/editor-artifact cleanup across the existing toolchain and Lake files totals approximately445MB:259.8MB of generated C and184.9MB of ilean metadata. This would leave only about1.09GB free. Static archives occupy another427.6MB, but removing toolchain libraries would impair native relinking and is not treated as safe cleanup. The apparent130MB of elan command aliases is nine hardlinks to one14.5MB inode and cannot yield130MB of space.

The large private/server olean and IR files cannot safely be discarded to make room. Lean4.36 Environment.lean2443–2456 explicitly reads all three olean parts for module-system modules; its default private-level importer also requests IR (lines2547–2555). In particular, stripping private theorem information would not be a legitimate way to satisfy the trust-level-zero checker.

Conclusion: the available storage and clearly safe reclamation do not support the estimated full cache. This is a resource limitation, not evidence that the proof or checker is wrong. Root instructed that the full Mathlib fetch should not be attempted. No Mathlib source build, checker modification, credential action, or unsafe library deletion was performed.

Detailed measurements: cache-disk-census.json, cache-full-mathlib-estimate.json, cache-reclaim-assessment.json, and cache-missing-mathlib-modules.txt in the same archived diagnostics directory. The complete failed checker output is maintained by root separately.
