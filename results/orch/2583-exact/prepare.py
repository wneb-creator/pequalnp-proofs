"""Convert independently generated projective-plane data and a seed to SAT input."""
import argparse
import json
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("plane", type=Path)
ap.add_argument("seed", type=Path)
ap.add_argument("output", type=Path)
args = ap.parse_args()
plane = json.loads(args.plane.read_text())
seed = json.loads(args.seed.read_text())
assert plane["inputs"] == seed["inputs"]
rows = [(x, 1) for x in plane["minimal_true"]]
rows += [(x, 0) for x in plane["maximal_false"]]
assert len(set(x for x, value in rows)) == len(rows)
lines = [f'{seed["inputs"]} {len(seed["gates"])} {seed["output"]} {len(rows)}']
for i, gate in enumerate(seed["gates"]):
    assert gate["op"] in ("and", "or")
    assert 0 <= gate["a"] < seed["inputs"] + i
    assert 0 <= gate["b"] < seed["inputs"] + i
    a, b = sorted((gate["a"], gate["b"]))
    lines.append(f'{0 if gate["op"] == "and" else 1} {a} {b}')
lines += [f"{x} {value}" for x, value in rows]
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text("\n".join(lines) + "\n")
print(json.dumps(dict(inputs=seed["inputs"], gates=len(seed["gates"]), rows=len(rows))))
