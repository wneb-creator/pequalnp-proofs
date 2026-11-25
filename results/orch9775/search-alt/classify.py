"""Exact live-DAG singleton-support/fanout classification for correct circuits."""
import json
import sys
from pathlib import Path
from simplify import evaluate, full_target

def classify(candidate):
    gates = candidate["gates"]
    output = candidate.get("output", 13 + len(gates))
    assert evaluate(gates, output) == full_target
    live = {output}
    for i in range(len(gates) - 1, -1, -1):
        if 14 + i in live:
            live.update(gates[i][1:])
    support = [1 << v for v in range(14)]
    readers = [set() for _ in range(14 + len(gates))]
    strict = True
    for i, (op, a, b) in enumerate(gates):
        assert op in (0, 1) and a < 14 + i and b < 14 + i
        support.append(support[a] & support[b] if op == 0 else support[a] | support[b])
        if 14 + i in live:
            readers[a].add(i)
            readers[b].add(i)
            strict &= a != b
    # Cross-check the bit-set recurrence by fourteen separate scalar executions.
    for v in range(14):
        values = [u == v for u in range(14)]
        for op, a, b in gates:
            values.append((values[a] and values[b]) if op == 0 else (values[a] or values[b]))
        assert all(bool(s >> v & 1) == value for s, value in zip(support, values))
    branches = [w for w in live if len(readers[w]) >= 2]
    eligible = 0
    for w in branches:
        eligible |= support[w]
    bplus = sum(len(readers[w]) - 1 for w in branches if support[w])
    bzero = sum(len(readers[w]) - 1 for w in branches if not support[w])
    size = sum(w >= 14 for w in live)
    all_inputs_live = all(v in live and readers[v] for v in range(14))
    all_inner_live = all(readers[w] for w in live if w != output)
    if strict and all_inputs_live and all_inner_live:
        assert bplus + bzero + 14 == size + 1
    return dict(live_size=size, strict_distinct_operands=bool(strict),
                all_inputs_live=bool(all_inputs_live), all_inner_live=bool(all_inner_live),
                Bplus=bplus, Bzero=bzero, ineligible_mask=((1 << 14) - 1) ^ eligible,
                empty_support_branches=[dict(wire=w, readers=sorted(readers[w]))
                                        for w in branches if not support[w]],
                singleton_assignments_checked=14, full_assignments_checked=16384)

if __name__ == "__main__":
    for name in sys.argv[1:]:
        path = Path(name)
        result = classify(json.loads(path.read_text()))
        destination = path.with_name(path.stem + "-classification.json")
        destination.write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps(dict(source=str(path), classification=result)))
