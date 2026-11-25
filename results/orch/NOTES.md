# L-meta-2592 orchestration

Desk assigned Petersen edge-function lower bound for <=19 fan-in-two gates with at least one NOT. Only PEqualNP.Defs project import allowed. Exact data: /tmp/oec/pequalnp-pilot-121/desk-001.json. Three live reductions already reported, so prioritize full proof/counterexample. Root alone owns desk and git delivery.

Strategies: proof_route = existing bounds/decomposition; circuit_search = finite synthesis; not_elimination = structural argument; status_review = independent audit. Use separate strategy notes and lemmas, notify root of results.

## Verified current reduction status

Public desk data saved /tmp/oec/pequalnp-pilot-121/gaps.json. All three easy reduction halves already checked: L-meta-4725 (15+NOT lower bound), L-meta-7389 (canonical normalization), L-meta-8295 (cut after last NOT). Remaining open child statements: L-meta-4727 (1..4 NOT), L-meta-7391 (canonical19), L-meta-8297 (last-NOT separator). Reproducing existing easy halves is useful infrastructure but not new proof progress. Aim for stronger gate deletion or explicit witness.

## First strategy review

The seven-row block-cover conjecture requiring ps.length+bs.length >=12 is false: a budget11 auxiliary construction exists. This is not a counterexample to L-meta-2592. Stronger samples are needed for the ledger route. The direct eight-profile lower bound is a different statement and cannot simply replace the ledger condition. A monolithic finite kernel check exceeded memory; smaller certificate chunks are being prepared. The one-NOT decomposition and Petersen generator lemmas are compiled and their actual-circuit link is in progress. Witness searches remain inconclusive.
