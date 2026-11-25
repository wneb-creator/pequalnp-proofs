import json
import sys
from pathlib import Path

def signatures(n, gates, tests):
    vals = [sum(((x >> i) & 1) << j for j, (x, _) in enumerate(tests)) for i in range(n)]
    for op, a, b in gates:
        vals.append((vals[a] | vals[b]) if op else (vals[a] & vals[b]))
    return vals

def prune_once(n, gates, tests):
    vals = signatures(n, gates, tests)
    positive = sum(bool(y) << i for i, (_, y) in enumerate(tests))
    negative = ((1 << len(tests))-1) ^ positive
    replacement = list(range(n))
    updated = {}
    for i, (op, a, b) in enumerate(gates, n):
        a, b = replacement[a], replacement[b]
        chosen = None
        candidates = [j for j in range(i) if vals[i] & ~vals[j] & positive == 0
                      and vals[j] & ~vals[i] & negative == 0]
        if candidates:
            j = max(candidates, key=lambda j: ((vals[j] & positive).bit_count(),
                                               -(vals[j] & negative).bit_count(), -j))
            chosen = replacement[j]
        elif vals[i] & positive == 0:
            chosen = -1
        if chosen is None:
            if a == b:
                chosen = a
            elif a == -1 or b == -1:
                chosen = (b if a == -1 else a) if op else -1
            else:
                chosen = i
                updated[i] = [op, a, b]
        replacement.append(chosen)
    output = replacement[-1]
    assert output >= 0
    used = set()
    def visit(i):
        if i < n or i in used:
            return
        used.add(i)
        _, a, b = updated[i]
        visit(a)
        visit(b)
    visit(output)
    renaming = {i: i for i in range(n)}
    for j, old in enumerate(sorted(used), n):
        renaming[old] = j
    result = [[op, renaming[a], renaming[b]] for old in sorted(used) for op, a, b in [updated[old]]]
    new = signatures(n, result, tests)[renaming[output]]
    old = vals[-1]
    assert old & ~new & positive == 0
    assert new & ~old & negative == 0
    return result

if __name__ == '__main__':
    case_path, circuit_path, output_path = map(Path, sys.argv[1:])
    case = json.loads(case_path.read_text())
    gates = json.loads(circuit_path.read_text())
    original = len(gates)
    while True:
        new = prune_once(case['inputs'], gates, case['tests'])
        if new == gates:
            break
        gates = new
    output_path.write_text(json.dumps(gates, indent=2))
    v = signatures(case['inputs'], gates, case['tests'])[-1]
    missed = sum(y and not (v >> i & 1) for i, (_, y) in enumerate(case['tests']))
    false = sum(not y and (v >> i & 1) for i, (_, y) in enumerate(case['tests']))
    print('gates', original, '->', len(gates), 'missed', missed, 'false', false)
