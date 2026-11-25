import collections
import itertools
import json
import pathlib
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "circuit_search"))
from generate_full_guard_seeds import Builder
case = json.loads((HERE / "k9_arc_4_8_10_12.json").read_text())
neighbors = [{b for a, b in case["edges"] if a == p} for p in range(9)]
tests = case["tests"]
signatures = [sum(((mask >> i) & 1) << j for j, (mask, _) in enumerate(tests)) for i in range(22)]
target = sum(label << j for j, (_, label) in enumerate(tests))
positive_mask = (1 << 36) - 1
negative_mask = ((1 << len(tests)) - 1) ^ positive_mask
start = time.monotonic()
seeds = []
seen = set()
checked = 0
best = 10000
minimum_sizes = {}
stop = False
for size in (3, 4, 5):
    for group in itertools.combinations(range(9), size):
        for guard_count in range(2, min(size, 4) + 1):
            for selected in itertools.combinations(group, guard_count):
                for mode in range(4):
                    checked += 1
                    if time.monotonic() - start > 30:
                        stop = True
                        break
                    builder = Builder(inputs=22)
                    remaining = [p for p in range(9) if p not in group]
                    guard_order = list(selected)
                    if mode % 2:
                        guard_order.reverse()
                        remaining.reverse()
                    if mode >= 2:
                        for p in remaining:
                            builder.union(neighbors[p])
                    guard_wires = []
                    for p in guard_order:
                        others = builder.union(set(group) - {p})
                        own_neighbors = builder.union(neighbors[p])
                        guard_wires.append(builder.gate(1, others, own_neighbors))
                    merged = builder.gate(0, builder.union(group),
                                          builder.union(set().union(*(neighbors[p] for p in group))))
                    for guard in guard_wires:
                        merged = builder.gate(0, merged, guard)
                    terms = [merged] + [builder.gate(0, p, builder.union(neighbors[p])) for p in remaining]
                    output = terms[0]
                    for term in terms[1:]:
                        output = builder.gate(1, output, term)
                    gates = builder.compact(output)
                    key = (size, guard_count)
                    minimum_sizes[key] = min(minimum_sizes.get(key, 1000), len(gates))
                    if len(gates) > 43:
                        continue
                    values = signatures.copy()
                    for op, a, b in gates:
                        values.append(values[a] | values[b] if op else values[a] & values[b])
                    result = values[-1]
                    assert result & positive_mask == positive_mask
                    # The merged point/line factor and valid outside stars reject every pure-side input.
                    for mask in [(1 << 9) - 1, ((1 << 13) - 1) << 9] + [1 << i for i in range(22)]:
                        vals = [bool(mask >> i & 1) for i in range(22)]
                        for op, a, b in gates:
                            vals.append(vals[a] or vals[b] if op else vals[a] and vals[b])
                        assert not vals[-1]
                    bad = (result & negative_mask).bit_count()
                    signature_key = (result, tuple(map(tuple, gates)))
                    if signature_key in seen:
                        continue
                    seen.add(signature_key)
                    seed = {"group": list(group), "guarded": list(selected), "mode": mode,
                            "gates": gates, "output": 21 + len(gates), "size": len(gates),
                            "maximal_negative_errors": bad}
                    seeds.append(seed)
                    if bad < best:
                        best = bad
                        print("BEST", bad, "gates", len(gates), "group", group, "guarded", selected, flush=True)
                if stop: break
            if stop: break
        if stop: break
    if stop: break
(HERE / "k9-multiguard-seeds.json").write_text(json.dumps(seeds))
summary = {"checked": checked, "elapsed_seconds": time.monotonic() - start,
           "stopped_by_budget": stop, "seeds": len(seeds),
           "best_errors": best if seeds else None,
           "minimum_sizes": {str(key): value for key, value in minimum_sizes.items()}}
(HERE / "k9-multiguard-summary.json").write_text(json.dumps(summary, indent=2))
print(json.dumps(summary), flush=True)
