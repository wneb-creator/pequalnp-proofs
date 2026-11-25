"""Explicit controls for the three compressed graph instances and graft maps."""
import json
from pathlib import Path

directory = Path(__file__).resolve().parent
for number in (1, 2, 3):
    graph = json.loads((directory / f"lines5-type{number}-compressed.json").read_text())
    n = graph["inputs"]
    gates, stars = [], []

    def gate(op, a, b):
        gates.append(dict(op=op, a=a, b=b))
        return n + len(gates) - 1

    for ell in graph["bipartition"][1]:
        points = [a for a, b in graph["edges"] if b == ell]
        wire = points[0]
        for point in points[1:]:
            wire = gate("or", wire, point)
        stars.append(gate("and", wire, ell))
    output = stars[0]
    for star in stars[1:]:
        output = gate("or", output, star)
    assert len(gates) == graph["target_gates"] + 1
    witness = dict(inputs=n, gates=gates, output=output)
    (directory / f"type{number}-baseline.json").write_text(json.dumps(witness, indent=2) + "\n")
    print(f"type={number} baseline_gates={len(gates)} outside_ORs={graph['outside_or_gates']}")
