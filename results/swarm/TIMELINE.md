# L-meta-3668 swarm timeline

All timestamps are UTC.

- 2026-11-25 23:02 (minute precision): orchestrator started; repository rules and public desk snapshot read.
- 2026-11-25 23:03:07: public snapshot updated 23:02:10.434 marks L-meta-3668 withdrawn because its exact opposite L-meta-3669 was checked.
- 2026-11-25 23:03:29: distinct assignments posted to helper-1 through helper-9; switched full-proof routes to independent refutation verification after discovering closure.
- 2026-11-25 23:04:05: upstream main f42c29582a7392be53f4844e66009960a0189553 fast-forwarded into the assigned orchestrator branch.
- 2026-11-25 23:04:43: independent review confirms accepted PR 20641, authoritative run 45692973795, and matching source SHA256.

The accepted refutation predates this orchestrator: PR 20641 merged at 2026-11-25 22:54:55Z. No new proof credit is claimed.

## First helper results

These are bus report timestamps, not independently measured build times. Some helpers started before this orchestrator. Their claims were treated as untrusted until independently checked.

| Helper | First result UTC | Report |
|---|---|---|
| helper-1 | 2026-11-25 22:55:14 | Direct-route obstacle: existing elimination lemma has stronger hypotheses. (bus 4134) |
| helper-2 | 2026-11-25 23:05:48 | Finite enumeration reported all 2,048 core inputs and gadget cases passed. (bus 4378) |
| helper-3 | 2026-11-25 22:54:58 | Decomposition: singleton supports propagate by union at OR and intersection at AND. (bus 4128) |
| helper-4 | 2026-11-25 23:04:37 | Independently confirmed live withdrawal and authoritative accepted checker. (bus 4346) |
| helper-5 | 2026-11-25 23:03:52 | Independently confirmed withdrawal and checked-source hash. (bus 4331) |
| helper-6 | 2026-11-25 22:56:44 | Found upstream exact negation L_meta_3669. (bus 4168) |
| helper-7 | 2026-11-25 23:04:55 | Audited singleton support and boundary cases. (bus 4352) |
| helper-8 | 2026-11-25 23:05:00 | Confirmed full cache requirement and minimal checker targets. (bus 4354) |
| helper-9 | 2026-11-25 23:03:01 | Independently confirmed live withdrawal, source hash and accepted checker. (bus 4302) |

## Local verification

- Pinned Lean 4.36.0 installed because the supplied environment had no Lean executable.
- Required `lake exe cache get` completed: all 9,117 files downloaded and decompressed.
- Source-format/import guard passed for the existing `L_meta_3669.lean`.
- Full build/checker diagnostics retained under `/tmp/oec/pnp-swarm-3668-orch/`.
- 2026-11-25 23:07:22: targeted build of existing refutation L_meta_3669, definitions and checker passed (exit 0; 5,155 jobs).
- 2026-11-25 23:08:03: local repository checker accepted the existing theorem in refute mode against its extracted positive statement (exit 0; 2,446 constants re-checked).
