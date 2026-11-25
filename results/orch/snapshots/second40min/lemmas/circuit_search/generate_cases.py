import json
from pathlib import Path

root = Path(__file__).resolve().parent
geometry = json.loads((root / 'geometry.json').read_text())
profiles = json.loads((root.parent / 'algebra_strategy/subset_profiles.json').read_text())
out = root / 'subsets'
out.mkdir(exist_ok=True)
index = []
for ks, groups in profiles.items():
    k = int(ks)
    for gi, group in enumerate(groups):
        rows = group['rows']
        original_edges = [(a, b) for a, b in geometry['edges'] if a in rows]
        lines = sorted({b for a, b in original_edges})
        relabel = rows + lines
        edges = [(relabel.index(a), relabel.index(b)) for a, b in original_edges]
        n = len(relabel)
        neighborhoods = [sum(1 << (b-k) for a, b in edges if a == p) for p in range(k)]
        negatives = []
        for s in range(1 << k):
            union = 0
            for p in range(k):
                if s >> p & 1:
                    union |= neighborhoods[p]
            t = ((1 << len(lines))-1) ^ union
            closure = sum(1 << p for p in range(k) if neighborhoods[p] & t == 0)
            if closure == s:
                negatives.append(s | (t << k))
        tests = [[(1 << a) | (1 << b), 1] for a, b in edges] + [[x, 0] for x in negatives]
        gates = []
        def add(op, a, b):
            gates.append([op, a, b])
            return n + len(gates)-1
        def disj(xs):
            result = xs[0]
            for x in xs[1:]:
                result = add(1, result, x)
            return result
        stars = []
        for p in range(k):
            stars.append(add(0, p, disj([b for a, b in edges if a == p])))
        output = disj(stars)
        assert len(gates) == 5*k-1
        for x, expected in tests:
            v = [bool(x >> i & 1) for i in range(n)]
            for op, a, b in gates:
                v.append((v[a] or v[b]) if op else (v[a] and v[b]))
            assert v[output] == bool(expected)
        case = dict(name=f'k{k}_p{gi}', inputs=n, max_gates=5*k-2, input_original=relabel,
                    original_rows=rows, edges=edges, tests=tests,
                    seed=dict(gates=gates, output=output), line_degree_hist=group['line_degree_hist'])
        (out / f'k{k}_p{gi}.json').write_text(json.dumps(case, indent=2))
        index.append({q: case[q] for q in ['name', 'inputs', 'max_gates', 'original_rows', 'line_degree_hist']} | {'test_count': len(tests)})
(out / 'index.json').write_text(json.dumps(index, indent=2))
for case in index:
    print(case)
