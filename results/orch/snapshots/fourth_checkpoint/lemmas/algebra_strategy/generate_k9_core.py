import json
from pathlib import Path
base = Path("results/orch/lemmas")
folder = base / "algebra_strategy"
full = json.loads((base / "circuit_search/geometry.json").read_text())
old = json.loads((base / "circuit_search/subsets/k6_p3.json").read_text())
old_approx = json.loads((folder / "k6-budget25-peeled16.json").read_text())
arc = [4, 8, 10, 12]
rows = [r for r in range(13) if r not in arc]
assert all(sum((r, line) in map(tuple, full["edges"]) for r in arc) <= 2
           for line in range(13, 26))
input_original = rows + list(range(13, 26))
local = {original: index for index, original in enumerate(input_original)}
edges = [[local[a], local[b]] for a, b in full["edges"] if a in rows]
n = len(input_original)
assert n == 22 and len(edges) == 36
neighbors = [sum(1 << b for a, b in edges if a == r) for r in range(9)]
line_mask = sum(1 << i for i in range(9, 22))
negatives = []
for points in range(1 << 9):
    covered = 0
    for i in range(9):
        if points >> i & 1:
            covered |= neighbors[i]
    lines = line_mask & ~covered
    if any(not(points >> i & 1) and not(neighbors[i] & lines) for i in range(9)):
        continue
    negatives.append(points | lines)
tests = [[(1 << a) | (1 << b), 1] for a, b in edges] + [[mask, 0] for mask in negatives]
assert len(negatives) == 228 and len(tests) == 264

def rowstar(gates, point):
    lines = [b for a, b in edges if a == point]
    result = lines[0]
    for line in lines[1:]:
        gates.append([1, result, line])
        result = n + len(gates) - 1
    gates.append([0, point, result])
    return n + len(gates) - 1

canonical = []
terms = [rowstar(canonical, p) for p in range(9)]
output = terms[0]
for term in terms[1:]:
    canonical.append([1, output, term])
    output = n + len(canonical) - 1
assert len(canonical) == 44
old_map = [local[original] for original in old["input_original"]]
def remap(wire):
    return old_map[wire] if wire < 17 else n + wire - 17
approx = [[op, remap(a), remap(b)] for op, a, b in old_approx]
approx_output = n + len(approx) - 1
for original_point in rows:
    if original_point not in old["original_rows"]:
        term = rowstar(approx, local[original_point])
        approx.append([1, approx_output, term])
        approx_output = n + len(approx) - 1
assert len(approx) == 43

def errors(gates, out):
    missed = false_accepts = 0
    for mask, target in tests:
        values = [bool(mask >> i & 1) for i in range(n)]
        for op, a, b in gates:
            values.append(values[a] or values[b] if op else values[a] and values[b])
        missed += bool(target and not values[out])
        false_accepts += bool(not target and values[out])
    return missed, false_accepts
assert errors(canonical, output) == (0, 0)
assert errors(approx, approx_output) == (0, 67)
degrees = [sum(b == line for a, b in edges) for line in range(9, 22)]
assert min(degrees) == 2
case = {"name": "k9_arc_4_8_10_12", "inputs": n, "max_gates": 43,
        "input_original": input_original, "original_rows": rows,
        "complement_arc": arc, "edges": edges, "tests": tests,
        "seed": {"gates": canonical, "output": output},
        "approximation": {"gates": approx, "output": approx_output,
                          "missed_positive_edges": 0, "false_maximal_negatives": 67},
        "line_degree_hist": [degrees.count(d) for d in range(5)],
        "extension_cost": 20, "extension_statement": "Append the four omitted full stars;43+20=63."}
(folder / "k9_arc_4_8_10_12.json").write_text(json.dumps(case, indent=2))
(folder / "k9_arc_4_8_10_12_approx.json").write_text(json.dumps(approx))
print("rows", rows, "arc", arc, "inputs", n, "edges", len(edges), "tests", len(tests))
print("line degree histogram", case["line_degree_hist"], "canonical44 exact", "approx43 errors0/67")
print("A43-gate exact witness extends to63 by adding four stars,20gates.")
