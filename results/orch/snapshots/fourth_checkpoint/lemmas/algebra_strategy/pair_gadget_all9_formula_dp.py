import json
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
edges = [(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 6), (1, 7), (1, 8)]
negatives = [sum(1 << i for i in range(2, 9)),
             (1 << 0) | sum(1 << i for i in range(6, 9)),
             (1 << 1) | sum(1 << i for i in range(3, 6)), 3]
raw_tests = [[(1 << a) | (1 << b), 1] for a, b in edges] + [[m, 0] for m in negatives]
tests = []
for raw, target in raw_tests:
    extended = raw
    for i in range(3):
        for j in range(3):
            if raw >> (3 + i) & 1 or raw >> (6 + j) & 1:
                extended |= 1 << (9 + 3*i + j)
    tests.append([extended, target])
signatures = [sum(bool(mask >> i & 1) << j for j, (mask, _) in enumerate(tests))
              for i in range(18)]
target = sum(value << j for j, (_, value) in enumerate(tests))
cost = [99] * 4096
expr = [None] * 4096
layers = [[] for _ in range(10)]
for i, signature in enumerate(signatures):
    if cost[signature] == 99:
        cost[signature] = 0
        expr[signature] = ["input", i]
        layers[0].append(signature)
start = time.monotonic()
print("terminals", signatures, "target", target, flush=True)
for size in range(1, 10):
    found = layers[size]
    for left_cost in range((size - 1) // 2 + 1):
        right_cost = size - 1 - left_cost
        lefts, rights = layers[left_cost], layers[right_cost]
        for a in lefts:
            for b in rights:
                if left_cost == right_cost and a > b:
                    continue
                result = a & b
                if cost[result] > size:
                    cost[result] = size
                    expr[result] = [0, a, b]
                    found.append(result)
                result = a | b
                if cost[result] > size:
                    cost[result] = size
                    expr[result] = [1, a, b]
                    found.append(result)
    print("cost", size, "new_signatures", len(found), "total", sum(map(len, layers[:size+1])),
          "seconds", time.monotonic() - start, "target_cost", cost[target], flush=True)
    if cost[target] <= size:
        break
result = {"inputs": 18, "raw_inputs": 9, "free_features": [[1, 3+i, 6+j] for i in range(3) for j in range(3)],
          "raw_tests": raw_tests, "tests": tests, "formula_cost": cost[target],
          "layer_counts": list(map(len, layers)), "elapsed_seconds": time.monotonic() - start}
if cost[target] < 99:
    gates = []
    cache = {}
    def emit(signature):
        node = expr[signature]
        if node[0] == "input":
            return node[1]
        if signature in cache:
            return cache[signature]
        a, b = emit(node[1]), emit(node[2])
        gates.append([node[0], a, b])
        cache[signature] = 18 + len(gates) - 1
        return cache[signature]
    output = emit(target)
    for mask in range(512):
        values = [bool(mask >> i & 1) for i in range(9)]
        values += [values[3 + i] or values[6 + j] for i in range(3) for j in range(3)]
        for op, a, b in gates:
            values.append(values[a] or values[b] if op else values[a] and values[b])
        expected = any(mask >> a & 1 and mask >> b & 1 for a, b in edges)
        assert values[output] == expected
    result.update(gates=gates, output=output, dag_gate_count=len(gates))
    print("WITNESS", json.dumps({"formula_cost": cost[target], "dag_gate_count": len(gates),
                                "gates": gates, "output": output}), flush=True)
(HERE / "pair-gadget-all9-formula-result.json").write_text(json.dumps(result, indent=2))
