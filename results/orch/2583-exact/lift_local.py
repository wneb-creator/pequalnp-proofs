"""Lift a compressed five-line witness to the entire PG(2,3) incidence circuit."""
import argparse
import json
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("graph", type=Path)
ap.add_argument("witness", type=Path)
ap.add_argument("output", type=Path)
args = ap.parse_args()
directory = Path(__file__).resolve().parent
plane = json.loads((directory.parent / "2583-search" / "plane3.json").read_text())
graph, witness = [json.loads(path.read_text()) for path in (args.graph, args.witness)]
assert graph["inputs"] == witness["inputs"]
gates = []


def gate(op, a, b):
    assert op in ("and", "or") and 0 <= a < 26 + len(gates) and 0 <= b < 26 + len(gates)
    gates.append(dict(op=op, a=a, b=b))
    return 25 + len(gates)


mapping = []
for group in graph["point_input_groups"]:
    wire = group[0]
    for point in group[1:]:
        wire = gate("or", wire, point)
    mapping.append(wire)
assert len(gates) == graph["outside_or_gates"]
mapping += [13 + ell for ell in graph["selected_lines"]]
assert len(mapping) == graph["inputs"]
for i, g in enumerate(witness["gates"]):
    assert g["a"] < graph["inputs"] + i and g["b"] < graph["inputs"] + i
    mapping.append(gate(g["op"], mapping[g["a"]], mapping[g["b"]]))
selected_output = mapping[witness["output"]]
other_stars = []
for ell, points in enumerate(plane["lines"]):
    if ell in graph["selected_lines"]:
        continue
    wire = points[0]
    for point in points[1:]:
        wire = gate("or", wire, point)
    other_stars.append(gate("and", wire, 13 + ell))
output = selected_output
for star in other_stars:
    output = gate("or", output, star)
expected_size = graph["outside_or_gates"] + len(witness["gates"]) + 40
assert len(gates) == expected_size
for x, value in [(x, True) for x in plane["minimal_true"]] + [(x, False) for x in plane["maximal_false"]]:
    values = [bool((x >> k) & 1) for k in range(26)]
    for g in gates:
        a, b = values[g["a"]], values[g["b"]]
        values.append(a and b if g["op"] == "and" else a or b)
    assert values[output] == value, (x, value)
result = dict(inputs=26, gates=gates, output=output, local_graph=str(args.graph),
              local_witness=str(args.witness), verified_complete_monotone_basis=756)
args.output.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(dict(gates=len(gates), verified_complete_monotone_basis=756)))
