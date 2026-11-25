import json
from pathlib import Path

base = Path("results/orch/lemmas")
folder = base / "algebra_strategy"
case = json.loads((base / "circuit_search/subsets/k6_p3.json").read_text())
original = json.loads((folder / "k6-budget25-original.json").read_text())
reordered = [g.copy() for g in original]
reordered[1] = [1, 9, 11]
reordered[2] = [1, 6, 18]
reordered[16] = [1, 18, 12]
peeled = [g.copy() for g in reordered]
peeled[6] = [1, 15, 16]
peeled[7] = [0, 17, 21]
peeled[13] = [0, 2, 23]
edges = {(1 << a) | (1 << b) for a, b in case["edges"]}

def minimal(masks):
    result = []
    for mask in sorted(set(masks), key=int.bit_count):
        if not any(small & mask == small for small in result):
            result.append(mask)
    return result

for name, gates in [("original", original), ("reordered", reordered), ("peeled16", peeled)]:
    (folder / f"k6-budget25-{name}.json").write_text(json.dumps(gates))
    missed = false_accepts = 0
    for mask, target in case["tests"]:
        values = [bool(mask >> i & 1) for i in range(17)]
        for op, a, b in gates:
            values.append(values[a] or values[b] if op else values[a] and values[b])
        missed += bool(target and not values[-1])
        false_accepts += bool(not target and values[-1])
    monomials = [[1 << i] for i in range(17)]
    for op, a, b in gates:
        monomials.append(minimal(monomials[a] + monomials[b] if op else
                                 [x | y for x in monomials[a] for y in monomials[b]]))
    extra = [m for m in monomials[-1] if not any(e & m == e for e in edges)]
    print(json.dumps({"candidate": name, "gates": len(gates), "missed_edges": missed,
                      "false_maximal_negatives": false_accepts,
                      "extra_minterms": [[i for i in range(17) if m >> i & 1] for m in extra]}))
