# Four-point K4-incidence plus private aggregate core

Global points2,3,8,15 induce six distinct pair-lines and four groups of two private lines. After aggregating each private pair by one OR, the local graph has14inputs and16edges: the subdivision incidence of K4 plus one private right vertex per point. Its known star circuit has19gates; the target is18. A correct18gate local circuit would yield a124gate plane circuit with overhead4private ORs +17remaining five-neighbor stars(5gates each)+17output merges=106. The exact finite geometry and cost calculation were independently audited; no Lean lift or target witness is claimed here.

The complete monotone extremal basis has16positive edge-pair inputs and16maximal-negative assignments, indexed by the four point bits. The author and independent audit checked all16,384possible inputs. The known19gate baseline was scalar-checked exhaustively and assigned to every one of101,640generated CNFclauses. It was canonically serialized over24verified input automorphisms; ten unordered first-gate pair orbits partition all91input pairs, and the calibration baseline obeys the added first-pair orbit restriction.

The generic18gate SAT trial uses reviewed Search.py with distinct strict-backward binary fan-ins, every nonfinal gate used, positive-firing/negative-failure pruning, operand incomparability, topological ordering and first-gate automorphisms. Its180second real-time cap ended UNKNOWN, exit0,141.48process seconds. This is no UNSAT or target-witness result, and exact-size pruning alone would not exclude every smaller size. The follow-up exactly6-AND variant is separate and is not included in this snapshot.

Reproduce from this snapshot directory with CaDiCaL available on PATH, saving complete stdout/stderr for each command:

```
python3 Search.py --case plane_local --points '2,3,8,15' --statement statement.txt --gates 19 --output /tmp/oec/pequalnp-pilot-29/reproduce-k4private19.cnf
python3 SearchK4PrivatePrepare.py --cnf /tmp/oec/pequalnp-pilot-29/reproduce-k4private19.cnf --output-dir /tmp/oec/pequalnp-pilot-29/reproduce-k4private-data
python3 Search.py --case plane_local --points '2,3,8,15' --statement statement.txt --gates 18 --first-pair-orbits k4private-automorphisms.json --output /tmp/oec/pequalnp-pilot-29/reproduce-k4private18.cnf
cadical -t 180 /tmp/oec/pequalnp-pilot-29/reproduce-k4private18.cnf
```

Generated CNFs/maps are reproducible and omitted; all source, core data, fixtures, complete logs and independent review are retained.

The original run used the current-container-only bundled binary at /tmp/oec/pequalnp-pilot-29/lean-4.36.0-linux/bin/cadical. That absolute binary path is not a portable prerequisite; use a local CaDiCaL executable supporting the documented -t time-limit option.
