from pathlib import Path
import itertools, json

root = Path('/tmp/oec/pequalnp-pilot-184/clean-and-search')
cases = json.loads((root / 'cases.json').read_text())
for c in cases:
    n = c['n']
    edges = {tuple(sorted(e)) for e in c['edges']}
    automorphisms = [p for p in itertools.permutations(range(n)) if {tuple(sorted((p[a], p[b]))) for a, b in edges} == edges]
    best = None
    for perm in automorphisms:
        names = dict(enumerate(perm))
        pending = dict(enumerate(c['witness_gates']))
        gates = []
        while pending:
            ready = []
            for j, (op, a, b) in pending.items():
                if a in names and b in names:
                    left, right = sorted((names[a], names[b]))
                    ready.append(((op, left, right), j))
            desc, old = min(ready)
            names[n + old] = n + len(gates)
            gates.append(desc)
            del pending[old]
        assert names[c['witness_output']] == n + len(gates) - 1
        if best is None or gates < best: best = gates
    c['witness_gates'] = best
    for r in range(1 << n):
        graph_value = any((r >> a & 1) and (r >> b & 1) for a, b in edges)
        wires = [bool(r >> i & 1) for i in range(n)]
        for op, a, b in best:
            value = (wires[a] and wires[b]) if op == 0 else (wires[a] or wires[b])
            wires.append(value)
            assert op != 0 or not value or graph_value
        assert wires[-1] == bool(graph_value)
(root / 'cases-lex.json').write_text(json.dumps(cases, indent=2) + '\n')
print('Canonically reordered safe upper witnesses for', len(cases), 'graphs')
