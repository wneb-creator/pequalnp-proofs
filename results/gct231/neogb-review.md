# Independent sparse-engine review

Verdict: no blocking defect was found in the reviewed wrapper, exact-QQ mode, or three-assignment bookkeeping fix. The fix matches the downstream pivot-count invariant, and nine independent exact controls pass. This validates the scoped research-tool path; it is neither a proof of the complete upstream engine nor an ideal-membership certificate or Lean proof.

Review completed **2026-11-25 10:25:42 UTC**. The reviewer source and complete log are:

    /tmp/oec/pequalnp-pilot-75/gct231/sparse-engine/independent_review.py
    /tmp/oec/pequalnp-pilot-75/gct231/sparse-engine/independent_review.log

Individual run logs, metadata, inputs, outputs, and comparison summaries are in the adjacent `independent-review/` directory. The 17 hashes in the frozen `provenance.json` were checked before and after the runs and remained unchanged. No heavy compilation was performed.

## ABI, arithmetic mode, and serialization

The wrapper's `export_f4` call matches the pinned header and implementation argument order. It selects characteristic zero for QQ, DRL order, no elimination block, one thread, linear-algebra option 2, and final basis reduction. The inspected dispatch sends QQ mode 2 to exact sparse rational elimination, and finite-field mode 2 to its exact sparse counterpart.

The QQ importer expects an array of pointers to interleaved GMP numerator and denominator objects. The wrapper builds precisely that layout. The importer clears each polynomial's denominators internally. The QQ exporter returns a contiguous array of GMP integers, which the wrapper prints and frees using the matching API. The finite-field coefficient and exponent layouts likewise agree. Output term-count checks and the runner's unit-basis predicate have the intended meaning for successful output in the selected field.

The binary's dynamic section names `libneogb_qqfix.so` and the expected scratch-directory runpath. Its binary and library hashes match the provenance record. The patched `gb.c` is byte-identical to the upstream file; its include search selects the separate patched `la_qq.c` while using the other upstream sources.

## Why the bookkeeping fix is appropriate

After exact QQ elimination, the matrix records the actual number of new pivots in `mat->np`. The original QQ wrappers failed to copy that count into the metadata object. The next update calls `update_basis_f4(..., md->np)` and loops over that many new basis elements. Leaving the previous value there can access rows that were not produced, matching the supplied AddressSanitizer failure.

The two added assignments after the respective QQ elimination routines restore `st->np = mat->np`. The third assignment makes the interreduction path maintain the same count invariant. The finite-field routines already update these two counts together. An exact source comparison confirms that these three assignments are the entire change to `la_qq.c`; no coefficient arithmetic, pivot selection, or reduction rule was changed.

## Limits and independent controls

The runner enforces wall time, CPU time, address-space limits, and disabled core dumps on the child process. Timeout or abnormal exit is recorded as unknown/error rather than completion. It parses basis output only after successful child exit, so an old output file is not interpreted as a successful timed-out result. Callers must inspect the metadata status, as the control scripts do.

All six frozen QQ/F1009 controls were rerun in a separate directory. Three additional QQ systems test nontrivial rational output, a three-variable unit ideal, and redundant generators with zero reductions. The added controls use a one-pair-per-round limit to exercise repeated updates. In every case the complete exported basis, normalized to monic form, matches an independently computed SymPy reduced Groebner basis in the same DRL order. Unit/nonunit metadata also agrees.

The intended input contract remains sparse, nonzero, combined terms; the controls independently check that monomials within each supplied generator are distinct. This review does not elevate a future engine unit-basis result to a checked proof without an independently replayed ideal-membership certificate.
