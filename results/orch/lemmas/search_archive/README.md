# Restricted Petersen template search

This archive records a completed computational search, not a Lean proof. All 15 template cases returned Z3 UNSAT. There is no Lean certificate and no claim of a general circuit lower bound or a proof of L-meta-2592.

## Exact family

The ten primary inputs are the vertices numbered in the posted Petersen edge function. Each case fixes an 11-gate monotone prefix: eight binary OR gates compute the three-neighbor ORs of centers 4, 1, 8, 7; three AND gates multiply the first three ORs by their centers. The fourth center 7 is left for the unknown completion. Each three-input OR has three choices of its first pair. Permuting the first three centers and their incident variables gives 15 representatives of the 81 choices. The explicit 15 prefixes are included; the solver results apply to those explicit prefixes independently of the orbit argument.

K4 labeling behind the prefix enumeration: centers A=4, B=1, C=8, D=7; edge variables AB=0, AC=3, AD=9, BC=6, BD=2, CD=5. The symmetry group fixes D and permutes A, B, C.

After the fixed prefix, the solver permits exactly seven more binary AND/OR gates, with repeated operands allowed, and requires the last wire to output the target. Each new non-output gate is used later. Thus shorter useful completions can be padded by identity gates and unused new gates can be removed. No NOT is allowed. The total size is 18 gates, including the fixed prefix. This is only a restricted family; other circuit architectures are not excluded.

The solver initially constrains the 15 edge inputs to true and the 15 maximal independent-set inputs to false. Any exact target circuit must satisfy these 30 tests. A SAT model would additionally be evaluated on all 1024 inputs and refined if incorrect. All 15 runs instead returned UNSAT on their first check, with no timeout and no candidate.

## Exact command run

Run began 2026-11-25T14:03:25Z and ended 2026-11-25T14:13:13Z.

```sh
python3 /tmp/oec/pequalnp-pilot-92/search-template-batch.py --gates 7 --min-not 0 --max-not 0 --timeout 120000 --rounds 2 > /tmp/oec/pequalnp-pilot-92/search-template-batch7.log 2>&1
```

The driver writes one complete combined stdout/stderr log per prefix, all included here. It invokes search-z3-template.py with the explicit prefix file, --critical, --allow-redundant, and the gate/NOT/time limits above. The scripts use the original scratch directory paths; reproduce by placing these archived files at those paths or changing only those paths. Z3 is loaded locally through ctypes from /usr/lib/x86_64-linux-gnu/libz3.so.4. Its reported version is in z3-version.txt. No network or credentials are used.

## Sanity check

The same template encoder was checked against a fixed 21-gate monotone circuit, consisting of an 11-gate prefix and a known 10-gate completion. It returned SAT and independent evaluation found zero errors on all 1024 assignments. The exact prefix, completion seed, and complete validation log are included.

```sh
python3 /tmp/oec/pequalnp-pilot-92/search-z3-template.py --gates 10 --prefix /tmp/oec/pequalnp-pilot-92/search-prefix11.json --seed 0 --edits 0 --seedfile /tmp/oec/pequalnp-pilot-92/search-template-validation-seed.json --min-not 0 --critical --timeout 1000 --rounds 1 > /tmp/oec/pequalnp-pilot-92/search-template-validation.log 2>&1
```

This archive is frozen. Later NOT-completion and projected-function AIG searches are separate.
