# S06 solver performance and certified finite subcases

Owner: Mencius/S06. Updated2026-11-24 03:34UTC. Concrete results delivered within10minutes. Scratch root for every artifact below: `/tmp/oec/pequalnp-pilot-18/orch/S06/`.

## Outcome and scope

**3,692 unit-based RUP additions have been independently replay-checked against the unchanged original DAG CNF.** The unchanged DSR checker returned exit0/`s VALID` with `--forward --rup-only`. These clauses preserve the CNF's satisfying assignments. They do not refute the full CNF.

The work also supplies replayable UNSAT certificates for16 overlapping prefix-selector subcases,12 source choices inside theAAAA case, and one furtherAAAA source choice found by a single bounded solver control. No complete suffix-operation case, assigned shard, or global Lean statement has been refuted. No Lean source was written or compiled. No S01 normalization is assumed in any clause or certificate here.

Parent CNF SHA256: `38d93ec59a86378a8434b232d19b2b53e8cbc3c715e81432ee94db59ca6ace08` (11968variables,114566clauses). All checks use DSR SHA256 `e6894b5b74ac2c09b494344f397ec5111547aaa782cdb399f1a8b6835ecef84b`.

## Recommendation for the coordinator

After S08 reviews the final RUP package and the coordinator authorizes a launch, use the two available CPUs for **one serial solver/checker pair over17 unsolved exactAAAA fanin cubes,20seconds per cube**, at most340seconds of requested search wall time plus startup/checking overhead. Keep original supervisor19723 running.

`AAAA-right17-partition/manifest.json` contains each exact CNF/metadata hash and a complete proposed online-runner command as a JSON argument array. No command in this manifest has been executed. Use the unchanged CaDiCaL `--unsat` and online runner; solver/checker address-space caps are1024/2048MiB. The abort-file path is passed only as a sentinel; no lease operation is performed.

The suggested order is source wires14,15,16,17, then18..29, then12. Wire13 is already refuted by the retained direct certificate below. This prioritizes nearby cases where scalar propagation fixed over10400 of11968variables and an actual adjacent control completed in0.22s. Runtime for the unsolved cases remains unknown;20seconds is a budget choice, not a solve-time prediction. A timeout is UNKNOWN/ABORTED and leaves that cube open. A result for all18cubes would exhaust onlyAAAA; AOAA/AAOA/AAAO remain separate.

This is the most concrete capped second-search recommendation from the measured evidence. No new long solver or portfolio has been launched. After the coordinator's latest hold instruction, all further solver launches were held.

## Replayable preprocessing packages

Earlier stages remain unchanged so S08 can review the initially reported569-clause package independently of later stages.

| Stage | Added clauses | Proof path / SHA256 | Result CNF path / SHA256 |
|---|---:|---|---|
| First-level |569|`combined.drat` / `dad278648ab57d19bc4af884261eba40c0931c6f234ceb6485f998c50cf3991b`|`augmented.cnf` / `459714296e1b81ca589d3ad1f020606812e4cb29a1ad0cdf3273a94c0b702f0c`|
| Prefix lookahead |994|`strong.drat` / `b26cafe87463ab3b6a806275f67bbf146e2945fbf5e637aa3775a2c2f6fca992`|`strong.cnf` / `7eed87fcaa73613b91fecd7a56ede475679860012323ca5a3a37b2868cd5c1a4`|
| Suffix fanin lookahead |3692|`suffix-fanin/lifted-all.drat` / `f319ae4b04ce7c6910389dc7f60ed61c353417192c47a44def9b35cc784683c8`|`suffix-fanin/augmented.cnf` / `2d20f5647012ed07af999643828cd3ac7916d4f61417d966579a49862b05e879`|

The final replayable proof is119955bytes. The final CNF has118258clauses, unchanged variable numbering, and exactly the original clause body followed by these3692clauses. Metadata preserves the original decoding arrays and explicitly records parent/proof hashes. A future SAT model can use the unchanged original-model/all2048-input validator. A future UNSAT result for an augmented CNF must retain its preprocessing provenance; production online proof digests are still not replayable artifacts.

`probe.cpp`, SHA256 `2deef9ec207f5225f4d31c25351998733f3b39e533d2234d02c99b0cf11a09a6`, implements deterministic occurrence-list unit propagation and bounded exhaustive failed-literal probing. It is not trusted for soundness: every emitted clause sequence is checked independently by DSR. `build_probe_package.py`, `second_level.py`, and `suffix_fanin.py` reproduce the respective stages. Build/generation/full checker logs remain in this directory; stage manifests are `package.json`, `second-level.json`, `suffix-fanin/manifest.json`, and `suffix-fanin-summary.json`.

Initial root propagation fixes130variables. Probing derives195unit clauses and fixes379variables. Under the four existing operation cubes, further probing derives231/77/29/37units respectively forAAAA/AOAA/AAOA/AAAO. A local unit under cubeC is lifted to the clause `not C OR unit`; all lifted clauses are checked directly against the original CNF. The first five scalar jobs took under2s aggregate. Prefix-selector and suffix-fanin probing add425 and2698further clauses. These are implication consequences, not new normalizations.

Exact replay command for the final package:

```sh
/tmp/oec/pequalnp-pilot-18/solver/dsr-trim/bin/dsr-trim --forward --rup-only \
  /tmp/oec/pequalnp-pilot-18/original-dag-strong/original.cnf \
  /tmp/oec/pequalnp-pilot-18/orch/S06/suffix-fanin/lifted-all.drat
```

Expected verdict: `s VALID`, not `s VERIFIED UNSAT`. Full logs: `combined-check.*`, `strong-check.*`, `suffix-fanin-check.*`. Actual CDCL speedup from these additions has not been benchmarked.

## Exact certified subcases and partition

**Prefix family.** For every zero-based gate g in1..16, the original CNF plus the unit `rights[g][1]` is UNSAT: no model can select input wire1 as that gate's right operand. Sixteen fresh DSR RUP-only checks returned exit0/`s VERIFIED UNSAT`. `certified-subcases/manifest.json` gives exact variable IDs, exact statements, commands and every log/CNF hash. The shared995-line proof is18105bytes, SHA256 `5965d6717c76455b052dc1e6309d52c6c8253dc53e9d47a43f4270c07c8b39e4`. These subcases overlap and are not an exhaustive family. The same proof's final empty-clause claim is correctly rejected against the original CNF without a subcase unit: `negative-control.json`, `negative-empty-check.*`.

**AAAA partition.** Set operation variables2807,3072,3341,3614TRUE. Exactly-one right17 selectors partition this case by source wire0..29. The RUP package excludes0..11; twelve explicit empty-clause RUP checks verify those exclusions. Eighteen cases12..29 remain. A further coverage check adds the negation of every remaining selector and derives a unit-propagation contradiction. Thus the18cases coverAAAA. They are pairwise disjoint because the original exactly-one encoding forbids selecting two right operands. `prepare_partition.py` generates all inputs and performs these checker-only controls; it never invokes a solver. Full checks and hashes are in `AAAA-right17-partition/manifest.json` and its adjacent stdout/stderr files.

**One measured solver control.** Before the coordinator's latest hold message, one announced isolated run tested the original CNF plusAAAA and `rights[17][13]`, exactly the five units `[2807,3072,3341,3614,2851]`. CaDiCaL exited20/`s UNSATISFIABLE` in0.2206seconds; DSR independently replayed the retained proof and exited0/`s VERIFIED UNSAT`. This is a direct original-CNF subcase certificate, with no preprocessing or S01 consequence assumed.

- Exact input SHA256: `8cd01c32fc548d1457990d27ecdf83adcee657fc213963092caf72edfcf5641b`.
- Retained ASCII DRAT proof: `bounded-control/proof.drat`,1243473bytes, SHA256 `3e15055185b8fa99377cbda2b77ca7a5631cb22886665f7c23e461d2ed1920fe`.
- Solver SHA256: `2a0137451efde370d67b88aec26f1e902870f095b1204b07049a103bc6bbd647`.
- Full result, commands, all source/input/proof/log hashes: `bounded-control/result.json`; all four full solver/checker logs are adjacent.
- Limits were10000conflicts,5solver seconds,7supervisor seconds,1GiB address space and32MiB retained-proof file size. No limit was hit.

This control certificate is separate from the unit-based RUP packages. No further solver has been launched. No entire operation case is claimed checked UNSAT.

## Active-run measurements and remaining obstruction

At03:33:34, recovery2 elapsed811.6s, emitted309.0MB/7.64million proof records, and had peak RSS105.8MiB solver/399.5MiB checker. The relay had393216bytes pending, below its1MiB bound. The earlier03:25:49snapshot had164.1MB/4.84million records and80.2MB/229.6MB peak RSS. Full snapshots and a window calculation are `live-snapshot-1.json`, `live-snapshot-2.json`, `live-rate-analysis.json`.

The465.995s window averaged5993records/s, which would take another15411s to the100million-record guard if maintained. This is only a measured-window extrapolation, not a forecast or remaining-search estimate. The earlier startup-average118minute extrapolation was substantially faster and should not be used as a deadline. No current record/memory/relay guard warrants restarting supervisor19723. Continue observing checker address space because its3GB limit concerns virtual allocation, not only RSS.

The precise obstruction is unchanged: all four broad operation cases survived scalar probing, and the checked subcases do not exhaust any broad case. Their conditional fixed points and CNF hashes are preserved for further search. S01's pending existence normalization could removeAOAA from a new search, but it is not an implication of the existing CNF and was not mixed into this work. S04 found no original-DAG completeness blocker, and S03's40-row sufficiency proof now supports candidate verification. The next useful S06 step is the coordinated capped exact-cube sweep above, not further unaudited encoding restrictions.

Only this report, S06 scratch artifacts and flock-protected NOTES appends were written. No active worker, named Lean file, other agent output, lease, credentials, git history or remote service was modified.
