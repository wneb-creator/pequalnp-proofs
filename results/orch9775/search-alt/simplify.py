"""Reduce a correct AO2 witness by its exact monotone extremal specification."""
import json
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
data = json.loads((here / "data.json").read_text())
samples = data["rows"]
desired = (1 << len(data["positive"])) - 1
full_inputs = [sum(((m >> v) & 1) << m for m in range(1 << 14)) for v in range(14)]
full_target = 0
for a, b in data["edges"]:
    full_target |= full_inputs[a] & full_inputs[b]

def evaluate(gates, output):
    wires = full_inputs.copy()
    for op, a, b in gates:
        assert op in (0, 1) and 0 <= a < len(wires) and 0 <= b < len(wires)
        wires.append(wires[a] & wires[b] if op == 0 else wires[a] | wires[b])
    return wires[output]

def simplify(candidate):
    old = candidate["gates"]
    output = candidate.get("output", 13 + len(old))
    assert evaluate(old, output) == full_target
    values = [sum(((row >> v) & 1) << k for k, row in enumerate(samples)) for v in range(14)]
    first = {value: i for i, value in enumerate(values)}
    mapping = list(range(14))
    gates = []
    for op, a, b in old:
        a, b = mapping[a], mapping[b]
        value = values[a] & values[b] if op == 0 else values[a] | values[b]
        if value not in first:
            first[value] = len(values)
            values.append(value)
            gates.append([op, a, b])
        mapping.append(first[value])
    assert values[mapping[output]] == desired
    # Any wire with this exact extremal signature computes the target, because
    # every gate is monotone and these rows bound every Boolean assignment.
    output = first[desired]
    live = {output}
    for i in range(len(gates) - 1, -1, -1):
        if 14 + i in live:
            live.update(gates[i][1:])
    compact, renaming = [], list(range(14))
    for i, (op, a, b) in enumerate(gates):
        if 14 + i in live:
            renaming.append(14 + len(compact))
            compact.append([op, renaming[a], renaming[b]])
        else:
            renaming.append(None)
    output = renaming[output]
    assert evaluate(compact, output) == full_target
    return dict(inputs=14, gates=compact, output=output,
                full_assignments_checked=16384, original_slots=len(old),
                size=len(compact))

if __name__ == "__main__":
    for name in sys.argv[1:]:
        path = Path(name)
        reduced = simplify(json.loads(path.read_text()))
        destination = path.with_name(path.stem + "-reduced.json")
        destination.write_text(json.dumps(reduced, indent=2) + "\n")
        print(json.dumps({"source": str(path), "destination": str(destination),
                          "size": reduced["size"], "full_assignments_checked": 16384}))
