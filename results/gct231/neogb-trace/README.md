# Sparse exact QQ certificate adapter

This independently reviewed adapter records ideal-membership certificates from the serial rational neogb core. Its toy controls and the previously solved rowzero system pass exact arithmetic replay. The resulting rowzero Lean theorem is checked. This archive does not prove or refute the full L-gct-231 statement.

The rowzero run completes in0.009seconds. Its57,269-byte trace contains43 verified output identities. The useful certificate has22 steps,239 polynomial terms and168 parent-combination terms. `NeoTraceRowzero.lean` is9,528bytes/46lines. The audit driver compiled successfully in11.503seconds (exit0,peakRSS3,935,240KiB) and reports only propext,Classical.choice,Quot.sound. The proof is a direct rational `linear_combination` certificate; no external solver result is trusted by Lean.

The adapter dumps original generators and every actual symbolic matrix input, tracks exact integer row scaling/subtraction, records content normalization through the leading-coefficient ratio, and dumps each inserted basis polynomial. The unchanged `replay_f4_trace.py` checks every matrix input is a scalar monomial multiple of an already proved polynomial and checks every output identity over exact rationals. `review/` adds a separately written direct polynomial-state replay and a separate certificate-DAG verifier, plus exact source-conversion checks. The review was frozen before compilation; `review/BUILD_UPDATE.md` records the later successful build.

The C instrumentation is strictly serial, characteristic zero, linear-algebra option2. It does not support the parallel/native engine or the ab-first option. The divisible-pivot branch uses conceptual multiplier1 even though the core's temporary variable may be stale. Initial normalization and monomial-multiplication provenance are checked from actual polynomials, avoiding reliance on dormant trace metadata.

## Reproduction

Use the official msolve v0.11.0 commit cc044551f8e202d00691990fd3fd0b1226a88ea2. The known pivot-count bookkeeping correction is preserved as `qqfix.patch`. With the pristine source under `msolve/`, the corrected gb.c/la_qq.c under `qqfix/`, and the supplied wrapper/helper files beside them, `make_cert_trace.py` creates a separate `certificate-trace/` source tree. The original source and existing engines are not modified. Build commands are in `metadata.json`; no vendor tree, library or executable is archived. `certificate-hooks.patch` shows all hook changes relative to the already corrected serial core.

`run_neogb_trace.py` bounds wall time and address space, saves complete stdout/stderr and basis JSON, and emits an exact F4-style companion input for the reviewed replay script. The rowzero source conversion only renames s,t,u,r to x0,x1,x2,x3. All inputs, traces, certificates, conversion metadata, toy results, build outputs and independent review files needed to assess these claims are included.

The first overlay-generation attempt failed an expected single-match assertion because two conversion functions contained the same line; its complete diagnostic is retained. The successful overlay scopes the hook to the actual option2 basis-conversion function. No failed overlay was compiled.
