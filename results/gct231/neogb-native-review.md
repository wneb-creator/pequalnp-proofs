# Independent native solver review

Reviewed 2026-11-25 UTC by the independent review agent. Verdict: the native variant's stated source changes, exact-mode selection, thread limits, saved provenance, and 64 small control outputs pass review. This is a tested research engine, not an ideal-membership certificate or Lean proof.

The frozen provenance file is `/tmp/oec/pequalnp-pilot-75/gct231/sparse-engine/native/provenance.json`, SHA256 `f107a8ea3d4b3499690a25dd5fed9c3b83cca2ce2fb3837992a64adf3c6a9542`. All ten recorded native hashes and all seventeen original solver hashes were independently checked. The original validated QQ engine remains unchanged. The native `gb.c` equals the prior source, and native `la_qq.c` equals the reviewed three-assignment QQ bookkeeping fix.

The only additional core change removes the OpenMP pragma from basis-row conversion. That loop's `deg` variable and constant flag otherwise have shared writes. Removing its pragma restores the original serial evaluation order and preserves the coefficient operations. The separate sparse-elimination loops remain parallel. This review does not claim an exhaustive audit of upstream concurrency.

The wrapper retains the same ABI, input/output representation, and exact sparse mode 2. It accepts one through three threads, disables dynamic teams, and permits only one active parallel level. The runner preserves wall-clock and address-space limits and changes the process CPU allowance to `wall_seconds * threads + 2` soft / `+ 3` hard, accounting for aggregate thread CPU time. It records both executable and shared-library hashes; only a completed exit-zero run is parsed for a unit basis. No timeout or failed run becomes a nonexistence result.

The recorded compiler flags are `-O3 -march=native -fopenmp -DHAVE_AVX2 -DHAVE_AVX512_F`; no fast-math flag is added. The machine/compiler evidence includes AVX2 and AVX512F. The wrapper runpath resolves the sibling frozen native library, whose dynamic dependencies include GMP and OpenMP. This binary is specific to the recorded machine capabilities.

The independent replay reads each saved input and output, verifies its binary/library/input/output hashes and limits, reconstructs the polynomial system, and compares the complete monic reduced basis against Sympy in the same characteristic and grevlex order. All 64 cases pass: 45 unit/nonunit/rational cases over QQ and four prime fields at one, two, and three threads; nine three-variable or redundant-reduction cases; and ten 81-term-row cases over the same five fields at one and three threads. The wider-row tests add evidence for long inputs; they do not constitute instrumented branch coverage. The frozen provenance records the initial 54 cases; the additional ten are separately preserved without changing its recorded sources or binaries.

Reproducer and complete log:

- `/tmp/oec/pequalnp-pilot-75/gct231/sparse-engine/native/independent_native_review.py`
- `/tmp/oec/pequalnp-pilot-75/gct231/sparse-engine/native/independent-native-review.log`
- `/tmp/oec/pequalnp-pilot-75/gct231/sparse-engine/native/independent-native-results.json`

Command, from `/workspace/pequalnp-proofs`:

```text
python /tmp/oec/pequalnp-pilot-75/gct231/sparse-engine/native/independent_native_review.py > /tmp/oec/pequalnp-pilot-75/gct231/sparse-engine/native/independent-native-review.log 2>&1
```

The command completed with exit zero. No compilation or solver rerun was required. An initial reviewer-only literal typo, corrected before the successful replay, is preserved in `independent-native-review-attempt01.log`.
