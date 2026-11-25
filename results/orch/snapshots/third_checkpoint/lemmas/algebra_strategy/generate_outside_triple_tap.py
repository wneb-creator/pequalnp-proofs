import itertools
import json
from pathlib import Path

base = Path("results/orch/lemmas")
core = json.loads((base / "circuit_search/subsets/k6_p3.json").read_text())
full = json.loads((base / "circuit_search/geometry.json").read_text())
input_original = core["input_original"]
original_to_local = {v: i for i, v in enumerate(input_original)}
line_mask = sum(1 << i for i in range(6, 17))
row_neighbors = [sum(1 << b for a, b in core["edges"] if a == p) for p in range(6)]

def f(mask):
    return any(mask >> p & 1 and mask & row_neighbors[p] for p in range(6))

cases = []
for outside in [4]:
    if outside in core["original_rows"]:
        continue
    present = [original_to_local[b] for a, b in full["edges"]
               if a == outside and b in original_to_local]
    for pair in itertools.combinations(present, 3):
        qmask = sum(1 << x for x in pair)
        maximal = set()
        for points in range(64):
            neighbors = 0
            for p in range(6):
                if points >> p & 1:
                    neighbors |= row_neighbors[p]
            lines = line_mask & ~neighbors & ~qmask
            closure = sum(1 << p for p in range(6) if not(row_neighbors[p] & lines))
            maximum = closure | lines
            assert not f(maximum) and not(maximum & qmask)
            assert all(f(maximum | 1 << i) for i in range(17)
                       if not(maximum >> i & 1) and not(qmask >> i & 1))
            maximal.add(maximum)
        masks = sorted(set(m for m, target in core["tests"]) | maximal |
                       {1 << x for x in pair})
        constraints = [{"input": m, "residual": bool(f(m)),
                        "tap": None if f(m) else bool(m & qmask)} for m in masks]
        gates = core["seed"]["gates"] + [[1, pair[0], pair[1]], [1, 17 + len(core["seed"]["gates"]), pair[2]]]
        seed = {"gates": gates, "residual_output": core["seed"]["output"],
                "tap_output": 17 + len(gates) - 1}
        for row in constraints:
            values = [bool(row["input"] >> i & 1) for i in range(17)]
            for op, a, b in gates:
                values.append(values[a] or values[b] if op else values[a] and values[b])
            assert values[seed["residual_output"]] == row["residual"]
            if row["tap"] is not None:
                assert values[seed["tap_output"]] == row["tap"]
        cases.append({"name": f"outside{outside}_triple{pair[0]}_{pair[1]}_{pair[2]}",
                      "inputs": 17, "max_gates": 30,
                      "outside_original_point": outside,
                      "tap_input_indices": list(pair),
                      "tap_original_lines": [input_original[x] for x in pair],
                      "tap_zero_maxima": sorted(maximal),
                      "constraints": constraints, "seed": seed})
assert len(cases) == 1
pack = {"description": "Exact30-gate k6 core plus conditional outside-line triple tap",
        "input_original": input_original, "edges": core["edges"], "cases": cases}
(base / "algebra_strategy/k6_outside_triple_tap.json").write_text(json.dumps(pack, indent=2))
print(f"{len(cases)} complete care packs; all31-gate baselines verified")
for case in cases:
    print(case["name"], len(case["constraints"]), "tests",
          len(case["tap_zero_maxima"]), "tap-zero maxima")
