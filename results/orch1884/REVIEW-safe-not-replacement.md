# Independent review: SafeNotReplacement

UTC: 2026-11-25T16:40:52.724674+00:00

Verdict: PASS for the conditional actual-circuit replacement theorem. Source SHA256 `89b30b469d213b103e2826f7adfac4ae4d16c8c5a9a1a5b37e344e4f673ea98b`, 4287 bytes/99 lines. Author reported session38316 exit0; complete second-run stdout/stderr in scratch1884-safe-not-002 are empty. The failed first-run diagnostics are preserved separately and are not cited as validation. This reviewer did not rebuild.

The statement replaces a selected NOT gate with AND[] (the library true constant) at the same index. It assumes every gate after the selected NOT is AND orOR and that a true selected NOT operand implies the original output is true on the considered input. No assumption on the prefix, wire validity, input-list length, arity, output position, or number of NOT gates in the prefix is silently used.

`above` compares equal-length banks at every index. `append_above` treats existing, new and invalid indices separately, and `run_above` preserves comparison through arbitrary-arity AND/OR suffixes. If the selected operand is false, its old NOT value already equals the replacementtrue. If the operand is true, the safe premise makes the original outputtrue; increasing that gate value fromfalse totrue and propagating through the monotone suffix keeps the new outputtrue. This proves equality in both Boolean cases. The headDfalse operand exactly matches the library NOT convention, including empty and multi-input NOT lists.

The polymorphic function wrapper merely applies that pointwise theorem using the explicit original computation premise. The source changes no gate count and does not itself perform constant propagation or establish the safe-operand premise for Petersen. Those are separate obligations for the full target.

Only PEqualNP.Defs is imported, and the namespace is L_meta_1884.SafeNot. No options, attributes, string literals, forbidden constructs, new axioms, native_decide, unsafe declarations, or secret-like content occur. The file is below512KiB.
