# Final K4-private counted-AND SAT trials

All three trials target the independently audited14input16edge core from global points2,3,8,15 at exactly18gates, on its complete16positive+16maximal-negative basis, with24input automorphisms and ten first-gate pair orbits. They use distinct backward binary fan-ins, every nonfinal gate used, positive-firing/negative-failure pruning, operand incomparability and topological ordering. The fixed AND counts and minimum-dirty requirements are explicit search restrictions, not proven necessary conditions for every raw local circuit.

Completed outcomes:
- Exactly6AND gates:180second wall cap, UNKNOWN,127.93process seconds.
- Exactly7AND gates and at least2dirty ANDs:150second cap, UNKNOWN,121.79process seconds.
- Exactly8AND gates and at least2dirty ANDs:150second cap, UNKNOWN,133.14process seconds.

No model, target witness or UNSAT result was produced. These timeouts establish no lower bound. No additional solver was launched after the8AND trial, reserving memory for final Lean verification. An unpruned query was generated but never run and is not counted as a trial.

Full generation/solver stdout and stderr, exact problem metadata, source and baseline/core/automorphism data are retained. Large generated CNFs/maps are reproducible and omitted. Baseline19 and finite geometry/basis/lift-overhead audit are documented in sibling k4private-search/; the106gate lift cost is computationally audited, but no target18witness or Lean lift is claimed.

With CaDiCaL available on PATH, reproduce the7AND trial from this snapshot directory using separate option/value arguments:

```
python3 SearchDirtyCount.py --case plane_local --points '2,3,8,15' --statement statement.txt --gates 18 --and-count 7 --min-dirty 2 --first-pair-orbits k4private-automorphisms.json --output /tmp/oec/pequalnp-pilot-29/reproduce-k4private-counted.cnf
cadical -t 150 /tmp/oec/pequalnp-pilot-29/reproduce-k4private-counted.cnf
```

Save complete stdout/stderr. The6AND variant uses Search.py, --and-count 6 as separate option/value tokens, no minimum-dirty flag and180seconds; the8AND variant changes 7 to 8. The original executable path under /tmp/oec/pequalnp-pilot-29/lean-4.36.0-linux/bin was current-container-only.
