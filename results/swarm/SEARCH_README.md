# L-meta-2583 circuit search handoff

Status recorded at 2026-11-25T23:48:50.507542+00:00: no satisfying candidate has been found. The strongest original-core query is pending. A search timeout or interrupted run is UNKNOWN, never an UNSAT certificate or a full-gap proof.

The frozen encoder is `core_sat.py`, SHA256 `85052b974b15013629aabef9b268397d8891061813a5711b8372b449b9e9118b`. Do not change it while comparing these runs. The encoder, principal notes and audit summaries are archived alongside this README; other detailed diagnostic files remain in the scratch directory. Scratch directory: `/tmp/oec/pnp-swarm-2583-orch/`; working directory for commands: `/workspace/pequalnp-proofs`.

## Reproduce the strongest query

These commands use a fresh prefix. The existing pending query is `q3core23-first-orbit.cnf`, with metadata `q3core23-first-orbit.json` and complete solver output `q3core23-first-orbit-solver.log` (12,729 variables, 356,325 clauses). Its metadata SHA256 is `214b016e74fb187e5996c475fdf7bf53021b7512c017a1be41add2e6cebd5fc9`.

```sh
PNP_SWARM_SEARCH_DIR='/tmp/oec/pnp-swarm-2583-orch'
PNP_SWARM_ENCODER='/workspace/pequalnp-proofs/results/swarm/core_sat.py'
PNP_SWARM_SEARCH_PREFIX="${PNP_SWARM_SEARCH_DIR}/q3core23-reproduced"
python3 "${PNP_SWARM_ENCODER}" generate \
  --gates 23 --order 3 --line-ids '0,1,4,8,12' \
  --output "${PNP_SWARM_SEARCH_PREFIX}" \
  --at-most --incomparable-operands --all-gates-pair-active \
  --all-active-gates-used --essential-inputs-used --order-independent-gates \
  --op-critical-domains --critical-output-witnesses --first-input-orbit \
  > "${PNP_SWARM_SEARCH_PREFIX}-generate.log" 2>&1
"${PNP_SWARM_SEARCH_DIR}/cadical/build/cadical" -t 2400 \
  "${PNP_SWARM_SEARCH_PREFIX}.cnf" \
  > "${PNP_SWARM_SEARCH_PREFIX}-solver.log" 2>&1
```

Read the solver verdict before decoding. Run these next commands only when the complete solver log reports SATISFIABLE and contains a model:

```sh
python3 "${PNP_SWARM_ENCODER}" decode \
  --metadata "${PNP_SWARM_SEARCH_PREFIX}.json" \
  --solver-output "${PNP_SWARM_SEARCH_PREFIX}-solver.log" \
  --output "${PNP_SWARM_SEARCH_PREFIX}-circuit.json" \
  > "${PNP_SWARM_SEARCH_PREFIX}-decode.log" 2>&1
python3 "${PNP_SWARM_ENCODER}" extend \
  --metadata "${PNP_SWARM_SEARCH_PREFIX}.json" \
  --circuit "${PNP_SWARM_SEARCH_PREFIX}-circuit.json" \
  --output "${PNP_SWARM_SEARCH_PREFIX}-full63.json" \
  > "${PNP_SWARM_SEARCH_PREFIX}-extend.log" 2>&1
```

`decode` trims the inactive suffix and exhaustively checks all 65,536 core inputs. `extend` adds exactly 40 gates for the eight omitted line stars, so a core of at most 23 gates yields a full plane circuit of at most 63 gates. It independently checks the full plane's 52 positive and 704 maximal-false boundary inputs. Preserve the complete logs and model; no target solver was started by the handoff-writing task.

## What the results establish

- A decoded and extended candidate is evidence for a refutation. To finish, encode that concrete circuit and its checks in Lean, apply the checked `RefutationBridge.refute_of_eight_chunks`, and pass the official `refute` checker on the exact posted statement. Python checks alone do not count as a submitted refutation.
- The bridge requires AO2, size at most 63, one 169-bit positive check, and eight 1024-bit negative checks. Its checked ReadK1 lower bound is 64. No candidate satisfying all premises has been found.
- UNSAT for this particular core proves only the absence of an at-most-23 circuit for this restricted construction, subject to the SAT encoding and any proof-certificate validation. It does **not** prove the full projective-plane lower bound or L-meta-2583: a full-plane counterexample need not arise by extending this core.
- The 13-input leaf-stripped core's at-most-20 query is a separate search. A stripped-core candidate does **not** automatically extend to a full 63-gate circuit. The `extend` command explicitly rejects stripped metadata.
- The pruning flags are justified by choosing a globally minimum exact circuit; they are not properties of every arbitrary exact circuit. The first-input orbit flag uses only verified graph automorphisms and applies to both gate operations.

## Geometry and frozen-source verification

`final-search-geometry-audit.json` checks that final target metadata retains the original core labels after symmetry reduction. Core point IDs are `[0,1,2,3,4,5,6,7,8,10,12]`; line IDs are `[0,1,4,8,12]`. Its 20 edges are exactly the corresponding restriction of the lex-normalized F3 projective plane. Every generated input permutation preserves the complete core edge set; a permutation need not extend to a full-plane automorphism because the represented core function remains unchanged in its original labels.

The extension's full 13 row masks exactly match `RefutationBridge.lean`:
`[1170,113,2584,4372,15,4674,2338,7169,1352,1572,897,2244,4264]`.
Bridge SHA256: `0321cd3d5f5049052b0cb5e00b3f221fee2875f8daff06c8f6332feef192177c`. Fresh Lean compile and endpoint axiom audits pass with only the standard three axioms. `first-orbit-extension-control.log` checks the transformed canonical 24-gate core extends to 64 gates and passes all 52/704 full-plane boundary checks. That positive control is not a refutation.

## Audit artifacts

- `op-specific-witness-proof.txt`, `op-critical-encoding-notes.md`, `op-critical-audit.log/json`: operation-specific boundary domains.
- `critical-output-encoding-notes.md`, `critical-output-audit.log/json`: selected-row counterfactual output witnesses.
- `first-input-orbit-encoding-notes.md`, `first-input-orbit-audit.log/json`: 12 verified automorphisms, first-pair symmetry, canonical transformations, full-clause controls, unchanged defaults.
- `core-sat-op-critical.diff`, `core-sat-critical-output.diff`, `core-sat-first-input-orbit.diff` and corresponding `core_sat_before_*.py` preserve reviewed changes.
- `audit_op_critical.py`, `audit_critical_output.py`, `audit_first_input_orbit.py` reproduce calibration audits.
- `recovery-refutation-bridge-review.txt`, `recovery-refutation-bridge-build-v3.log`, `recovery-refutation-bridge-axioms.log`, `recovery-refutation-packed-audit.json` document the conditional bridge.

## Wall-time limits and pending status

The following post-restart runs remain pending at this snapshot; no SAT or UNSAT verdict is recorded:

| Complete solver log | Wall limit | Status |
| --- | ---: | --- |
| `q3core23-ordered-restart-solver.log` | 3000 s | Pending |
| `q3core23-satmode-restart-solver.log` | 3000 s | Pending |
| `q3core23-opcritical-solver.log` | 2400 s | Pending |
| `q3core23-critical-output-solver.log` | 2400 s | Pending |
| `q3core23-first-orbit-solver.log` | 2400 s | Pending; orchestrator reports start about 23:47 UTC, limit about 00:27 UTC |

Earlier `q3core23-solver.log` and `q3core20-stripped-solver.log` reached their 3600-second limits with `c UNKNOWN` and exit 0. Other pre-restart pending runs were interrupted around 23:20 UTC; their incomplete logs must not be called completed timeouts or UNSAT. Later status updates should retain these distinctions.
