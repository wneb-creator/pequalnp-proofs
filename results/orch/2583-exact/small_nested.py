"""Find a small bipartite graph circuit with output-relevant nested AND gates."""
import argparse
import itertools
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, "/tmp/oec/pequalnp-pilot-98/exact")
from synth import CNF

ap = argparse.ArgumentParser()
ap.add_argument("directory", type=Path)
ap.add_argument("--seconds", type=int, default=30)
ap.add_argument("--gates", type=int, default=8)
ap.add_argument("--allow-flat", action="store_true")
ap.add_argument("--graph", type=Path)
ap.add_argument("--first-orbits", action="store_true")
args = ap.parse_args()
assert 1 <= args.gates <= 32 and args.seconds >= 1
args.directory.mkdir(parents=True, exist_ok=True)
n, m = 6, args.gates
edges = [(a, 3 + b) for a in range(3) for b in range(3) if a != b]
if args.graph:
    graph = json.loads(args.graph.read_text())
    n = graph["inputs"]
    edges = list(map(tuple, graph["edges"]))
assert 3 <= n <= 20 and edges
assert all(0 <= a < n and 0 <= b < n and a != b for a, b in edges)
c = CNF()
left, right, op = [], [], []


def mux(z, selectors, values):
    for s, v in zip(selectors, values):
        c.clause(-s, -z, v)
        c.clause(-s, z, -v)


for i in range(m):
    left.append([c.var() for _ in range(n + i)])
    right.append([c.var() for _ in range(n + i)])
    op.append(c.var())  # true = AND, false = OR
    c.one(left[i])
    c.one(right[i])
    for a in range(n + i):
        for b in range(a):
            c.clause(-left[i][a], -right[i][b])
for i in range(m - 1):
    c.clause(*(left[j][n + i] for j in range(i + 1, m)),
             *(right[j][n + i] for j in range(i + 1, m)))
    # A ready gate with lexicographically smallest (max fanin,min fanin) can
    # always be selected next; its newly unlocked children have a larger max.
    # This canonical ordering uses no fixed numbered seed.
    for b in range(n + i):
        for d in range(b):
            c.clause(-right[i][b], -right[i + 1][d])
        for a in range(b + 1):
            for aa in range(a):
                c.clause(-right[i][b], -right[i + 1][b], -left[i][a], -left[i + 1][aa])

orbit_count = None
if args.first_orbits:
    assert args.graph
    point_side, line_side = graph["bipartition"]
    assert point_side == list(range(len(point_side)))
    assert line_side == list(range(len(point_side), n))
    patterns = [sum(int((a, b) in edges) << j for j, b in enumerate(line_side)) for a in point_side]
    assert len(set(patterns)) == len(patterns)
    pattern_index = {pattern: i for i, pattern in enumerate(patterns)}
    automorphisms = []
    edge_set = set(edges)
    for perm in itertools.permutations(range(len(line_side))):
        mapped = [sum(((mask >> j) & 1) << perm[j] for j in range(len(line_side)))
                  for mask in patterns]
        if set(mapped) != set(patterns):
            continue
        aut = [pattern_index[mask] for mask in mapped] + [line_side[perm[j]] for j in range(len(line_side))]
        assert {(aut[a], aut[b]) for a, b in edges} == edge_set
        automorphisms.append(aut)
    representatives = set()
    for a in range(n):
        for b in range(a, n):
            representative = min((max(aut[a], aut[b]), min(aut[a], aut[b])) for aut in automorphisms)
            representatives.add(representative)
            if (b, a) != representative:
                c.clause(-left[0][a], -right[0][b])
    orbit_count = len(representatives)

if not args.allow_flat:
    witnesses = []
    for i in range(m - 1):
        reach = [c.var() for _ in range(n + m)]
        for k in range(n + i + 1):
            c.clause(reach[k] if k == n + i else -reach[k])
        for j in range(i + 1, m):
            a, b, z = c.var(), c.var(), reach[n + j]
            mux(a, left[j], reach)
            mux(b, right[j], reach)
            c.clause(z, -a)
            c.clause(z, -b)
            c.clause(-z, a, b)
            witness = c.var()
            witnesses.append(witness)
            c.clause(-witness, op[i])
            c.clause(-witness, op[j])
            c.clause(-witness, z)
            c.clause(witness, -op[i], -op[j], -z)
    c.clause(*witnesses)

def target(x):
    return any((x >> a) & (x >> b) & 1 for a, b in edges)


# This is complete for the AND/OR candidates by monotonicity.  Validate every
# assignment independently after SAT; no monotonicity assumption on external
# candidate files is needed.
minimal_true = {(1 << a) | (1 << b) for a, b in edges}
point_side = sorted({a for a, b in edges})
line_side = sorted({b for a, b in edges})
assert not set(point_side) & set(line_side)
assert set(point_side) | set(line_side) == set(range(n))
maximal_false = set()
for subset in range(1 << len(line_side)):
    lines = {line_side[j] for j in range(len(line_side)) if (subset >> j) & 1}
    points = {a for a in point_side if not any(u == a and b in lines for u, b in edges)}
    closure = {b for b in line_side if not any(a in points and v == b for a, v in edges)}
    if closure == lines:
        maximal_false.add(sum(1 << k for k in points | lines))
rows = sorted(minimal_true | maximal_false)
for x in rows:
    values = [c.var() for _ in range(n + m)]
    for k in range(n):
        c.clause(values[k] if (x >> k) & 1 else -values[k])
    for i in range(m):
        a, b, z = c.var(), c.var(), values[n + i]
        mux(a, left[i], values)
        mux(b, right[i], values)
        o = op[i]
        c.clause(-o, -z, a)
        c.clause(-o, -z, b)
        c.clause(-o, z, -a, -b)
        c.clause(o, z, -a)
        c.clause(o, z, -b)
        c.clause(o, -z, a, b)
    c.clause(values[-1] if target(x) else -values[-1])
formula = args.directory / "formula.cnf"
c.write(formula)
print(json.dumps(dict(variables=c.n, clauses=len(c.cl), gates=m,
                      inputs=n, basis_rows=len(rows),
                      nested_required=not args.allow_flat, first_pair_orbits=orbit_count)), flush=True)
with (args.directory / "solver.log").open("w") as stream:
    try:
        completed = subprocess.run([
            "/tmp/oec/pequalnp-pilot-98/exact/kissat/build/kissat",
            f"--time={args.seconds}", "--seed=98", str(formula)],
            stdout=stream, stderr=subprocess.STDOUT, timeout=args.seconds + 30)
    except subprocess.TimeoutExpired:
        print("UNKNOWN: solver exceeded wall timeout; complete output preserved", flush=True)
        raise SystemExit(0)
print(f"solver_exit={completed.returncode}", flush=True)
if completed.returncode == 10:
    positive = set()
    for line in (args.directory / "solver.log").read_text().splitlines():
        if line.startswith("v "):
            positive.update(int(s) for s in line.split()[1:] if int(s) > 0)
    gates = [dict(op="and" if op[i] in positive else "or",
                  a=next(a for a, s in enumerate(left[i]) if s in positive),
                  b=next(b for b, s in enumerate(right[i]) if s in positive))
             for i in range(m)]
    used = {g[key] for g in gates for key in ("a", "b")}
    assert all(n + i in used for i in range(m - 1))
    ancestors = [set() for _ in range(n)]
    nested = False
    for i, g in enumerate(gates):
        parents = ancestors[g["a"]] | ancestors[g["b"]]
        if g["op"] == "and" and any(gates[j]["op"] == "and" for j in parents):
            nested = True
        ancestors.append(parents | {i})
    assert args.allow_flat or nested
    # Python integers hold the entire 2^n-row truth table bitwise.  This check
    # does not rely on the boundary-basis completeness used for SAT encoding.
    values = []
    byte_count = 1 << (n - 3)
    for k in range(n):
        if k < 3:
            pattern = bytes([sum(((j >> k) & 1) << j for j in range(8))]) * byte_count
        else:
            run = 1 << (k - 3)
            pattern = (bytes(run) + b"\xff" * run) * (1 << (n - k - 1))
        values.append(int.from_bytes(pattern, "little"))
    target_table = 0
    for a, b in edges:
        target_table |= values[a] & values[b]
    for g in gates:
        a, b = values[g["a"]], values[g["b"]]
        values.append(a & b if g["op"] == "and" else a | b)
    assert values[-1] == target_table
    result = dict(inputs=n, gates=gates, output=n + m - 1)
    (args.directory / "WITNESS.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"WITNESS: all {1 << n} assignments independently checked; nested={nested}", flush=True)
