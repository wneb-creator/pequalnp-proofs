"""Replay the saved C6 SAT witness evaluation; performs no search."""
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("metadata", type=Path)
parser.add_argument("solver_output", type=Path)
args = parser.parse_args()
meta = json.loads(args.metadata.read_text())
lines = args.solver_output.read_text().splitlines()
assert "s SATISFIABLE" in lines, "saved solver output is not SAT"
model = {}
for line in lines:
    if line.startswith("v "):
        for literal in map(int, line[2:].split()):
            if literal:
                old = model.get(abs(literal))
                value = literal > 0
                assert old is None or old == value, "inconsistent saved assignment"
                model[abs(literal)] = value

gates = []
n = meta["n"]
for index, (left, right, op) in enumerate(zip(meta["left"], meta["right"], meta["op"])):
    selected_left = [i for i, variable in enumerate(left) if model[variable]]
    selected_right = [i for i, variable in enumerate(right) if model[variable]]
    assert len(selected_left) == len(selected_right) == 1
    a, b = selected_left[0], selected_right[0]
    assert 0 <= a < n + index and 0 <= b < n + index
    gates.append(("and" if model[op] else "or", a, b))
assert len(gates) == meta["size"]
print("Saved solver status: SATISFIABLE")
print("Gates:", json.dumps(gates))
print("Output wire:", n + len(gates) - 1)

for mask in range(1 << n):
    wires = [bool(mask & (1 << i)) for i in range(n)]
    for op, a, b in gates:
        wires.append(wires[a] and wires[b] if op == "and" else wires[a] or wires[b])
    expected = any(bool(mask & (1 << a)) and bool(mask & (1 << b)) for a, b in meta["edges"])
    assert wires[-1] == expected, (mask, wires[-1], expected)
print("Truth assignments verified:", 1 << n)

failed_pairs = []
for p, line in meta["edges"]:
    vectors = [
        {(int(i == p), int(i == line))} if i in (p, line) else set()
        for i in range(n)
    ]
    for op, a, b in gates:
        if op == "or":
            vectors.append(vectors[a] | vectors[b])
        else:
            vectors.append({
                (min(x + u, 2), min(y + v, 2))
                for x, y in vectors[a] for u, v in vectors[b]
            })
    print("Pair", (p, line), "capped vectors:", sorted(vectors[-1]))
    if not any(x <= 1 and y <= 1 for x, y in vectors[-1]):
        failed_pairs.append([p, line])
assert meta["edge"] in failed_pairs, "distinguished pair unexpectedly has a read-1 tree"
print("Pairs without a read-1 tree:", json.dumps(failed_pairs))
print("PASS: saved witness computes C6 incidence and fails read-1 on the distinguished pair.")
