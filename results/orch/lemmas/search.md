# Counterexample search

- Exact semantics checked: FanInTwo excludes MOD/MAJ; every gate counts, including NOT; invalid reads are false.
- Petersen function has 76 false inputs (independent sets), 15 maximal false inputs, 15 minimal true inputs.
- Installed official Z3 5.3.3 in job scratch. CEGIS script: /tmp/oec/pequalnp-pilot-114/search/synth.py.
- Running 19 gates, exactly one NOT, all gates live, strict distinct ordered operands for AND/OR, output final gate. Initial constraints: minimal true plus maximal false masks, zero and all-ones; full truth-table check adds counterexamples. This searches a restricted family; an unknown/unsat does not prove the posted theorem.
- Full log: /tmp/oec/pequalnp-pilot-114/search/synth-19-1.log.

## Validation and additional searches

- Fixed known 20-gate monotone circuit passed the SAT encoding and direct evaluation on all 1024 inputs. Data: scratch/search/known20-verified.json; complete solver output: synth-smoke.log.
- Second SAT run: 19 gates, exactly two NOT gates, first gate AND of adjacent vertices 0 and 1.
- Evolutionary bit-parallel search initially reached error18 (weighted false positives by13); the candidate has a dead NOT and an18-gate monotone core missing edges(1,2) and(5,7), so it is not a witness.
- Near-candidate local SAT repair and active-NOT-only evolution were initiated then stopped to respect the3-CPU budget. No result from those aborted searches.
- All output is preserved in scratch/search/*.log. No Lean proof/refutation found yet.

- Parent requested pause for lease-ownership audit; all active search processes suspended. Logs and current best remain saved. Process records in scratch/search/paused-processes.json. No complete witness found.

- Final archival: parent confirmed the allocation retry returned the same pre-existing lease. No further search performed. Small authored scripts, complete logs, known 20-gate validation data, and the approximate candidate are archived under results/orch/search/. All three previously suspended search processes were terminated after checking their recorded command lines. No 19-gate witness, UNSAT result, or Lean proof was produced.
