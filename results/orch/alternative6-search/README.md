# Alternative six-point stochastic search

This source-set search targets the19-input,24-edge local core for plane points[0,1,2,3,8,15]. The ordinary star circuit has29 gates. A28-gate local witness would lift to the exact42-input plane circuit with124 gates using the checked AlternativeLiftComplete conditional theorem (six aggregate-input OR gates and90 remaining-star gates).

The model has seven/eight AND nodes and one/two shared linear OR helpers. It uses the previously reviewed SharedDirty annealing, mutation, active-cone cost, and decoder. Changes are the problem data, degree-aware sampling for four-neighbor point stars, metadata, and thresholds29/28. A valid29-gate circuit with an active dirty AND is saved as a warm start; a28-gate circuit is saved as a prospective witness and still requires Lean checking.

The complete monotone basis has24 positive edge-pair inputs and64 negative assignments indexed by the six point bits. Every saved circuit is expanded into concrete binary AND/OR gates and scalar-checked on all88 cases. The data agrees with Alternative6CertificateChecked and the checked29-gate baseline.

Validation: status_audit checked120 valid baselines (costs29/31/33) and1200 mutated physical expansions. Independent counterexample_search review checked200 valid baselines and600 baseline/mutant expansions against scalar88-case semantics, topology and exact gate count. Complete logs are included. No28-gate circuit had been found when this package was frozen; the long run had not yet started.

Run from repository root:
```
python3 results/orch/alternative6-search/SearchStochasticAlternative6.py --seed 14772911 --seconds 1200 --output-dir /tmp/oec/pequalnp-pilot-29/stochastic-alternative6-run-003
```
