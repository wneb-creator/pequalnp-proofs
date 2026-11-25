# Shared-C6 route exclusion

This is a completed computational search, not a Lean proof. Z3 returned UNSAT after390.147seconds. No Lean certificate was produced, and this does not prove the general Petersen gap.

## Exact instance

Six inputs form cycle0-1-2-3-4-5-0. Three OR gates are fixed first: (0 OR3), (2 OR5), (1 OR4). They are supplied to seven unknown gates, each AND, OR, or NOT of earlier wires, with one to three NOT gates. Repeated operands and unused gates are allowed. NOT ignores its second selector, canonically fixed to input0. The last unknown gate is the output. All64assignments are constrained exactly. Identity padding covers shorter nonconstant completions; constant/unary operations can be eliminated using Boolean identities. The full search has1533Boolean variables.

A completion would lift to a19-gate Petersen circuit by mapping cycle inputs to original vertices[0,4,3,2,7,5], sharing the three ORs with the stars centered at1,8,9, then combining the four outputs. The generic lifting utility is included and was independently tested on a20-gate positive control over all1024assignments. No19-gate witness was found.

## Exact command

```sh
python3 /tmp/oec/pequalnp-pilot-92/search-c6.py --gates 7 --prefix /tmp/oec/pequalnp-pilot-92/search-c6-prefix3.json --min-not 1 --max-not 3 --allow-redundant --timeout 600000 --rounds 1 > /tmp/oec/pequalnp-pilot-92/search-c6-shared3.log 2>&1
```

The complete combined stdout/stderr is included. The archived source restores the exact pre-phase-hint version used for this run. It uses Python ctypes and the installed libz3.so.4(version4.13.3.0), with no network or credentials. Source uses original scratch paths; restore files to those paths or change paths only when reproducing.

## Known control

A known eight-gate monotone completion, with the same three fixed ORs, was fixed in the encoder. It returned SAT in0.101seconds and independently matched all64rows. That completion lifts to a20-gate Petersen circuit, with zero errors on all1024rows. It is not a counterexample.

```sh
python3 /tmp/oec/pequalnp-pilot-92/search-c6.py --gates 8 --prefix /tmp/oec/pequalnp-pilot-92/search-c6-prefix3.json --seed 0 --edits 0 --seedfile /tmp/oec/pequalnp-pilot-92/search-c6-prefix3-validation-seed.json --min-not 0 --max-not 0 --timeout 1000 --rounds 1 > /tmp/oec/pequalnp-pilot-92/search-c6-prefix3-validation.log 2>&1
python3 /tmp/oec/pequalnp-pilot-92/search-lift-c6.py /tmp/oec/pequalnp-pilot-92/search-c6-witness-g11-seed0.json /tmp/oec/pequalnp-pilot-92/search-lift-validation20.json
```

The separate checked lower bound for an isolatedC6(L_meta_4354) only excludes seven total gates; it does not imply this stronger shared-bank search result. This archive is frozen.
