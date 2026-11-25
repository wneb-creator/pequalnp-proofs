import json
from pathlib import Path
base = Path("results/orch/lemmas")
folder = base / "algebra_strategy"
case = json.loads((base / "circuit_search/subsets/k6_p3.json").read_text())
expected_edges = set(map(tuple, case["edges"])) | {(0, 11), (2, 6), (2, 9), (2, 13)}
for source, destination in [("cover17-pairs-result.json", "k6-cover17-sharing-lines.json"),
                            ("cover17-subset-result.json", "k6-cover17-sharing-redundant.json")]:
    cover = json.loads((folder / source).read_text())["rectangles"]
    actual_edges = {(a, b) for rectangle in cover for a in rectangle["rows"]
                    for b in rectangle["lines"]}
    assert actual_edges == expected_edges
    pairs = sorted({tuple(p) for rectangle in cover for p in rectangle["pairs"]})
    gates = []
    def gate(op, a, b):
        gates.append([op, a, b])
        return 17 + len(gates) - 1
    def join(wires):
        result = wires[0]
        for wire in wires[1:]:
            result = gate(1, result, wire)
        return result
    pair_wires = {pair: gate(1, *pair) for pair in pairs}
    terms = []
    for rectangle in cover:
        sides = []
        for name in ("rows", "lines"):
            vertices = rectangle[name]
            chosen = [tuple(pair) for pair in rectangle["pairs"] if pair[0] in vertices]
            used = [v for pair in chosen for v in pair]
            assert len(set(used)) == len(used)
            wires = [pair_wires[pair] for pair in chosen] + [v for v in vertices if v not in used]
            sides.append(join(wires))
        terms.append(gate(0, *sides))
    output = join(terms)
    assert len(gates) == 28
    miss = errors = 0
    for mask, target in case["tests"]:
        values = [bool(mask >> i & 1) for i in range(17)]
        for op, a, b in gates:
            values.append(values[a] or values[b] if op else values[a] and values[b])
        miss += bool(target and not values[output])
        errors += bool(not target and values[output])
    assert miss == 0 and errors == 17
    (folder / destination).write_text(json.dumps(gates))
    print(destination, len(gates), "gates", miss, "missing positives", errors, "false maximal negatives")
