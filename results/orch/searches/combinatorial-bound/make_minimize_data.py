import itertools
import json
import random
from pathlib import Path

ROOT = Path('/tmp/oec/pequalnp-pilot-71/combinatorial-bound')
SRC = Path('/tmp/oec/pequalnp-pilot-71/structural')
rng = random.Random(718276)
models = []
for name, size in [('theta', 12), ('fano', 27)]:
    source = json.loads((SRC / f'{name}-exact-control{size}.json').read_text())
    n, edges = source['n'], source['edges']
    rows = source['rows']
    assert len(rows) <= 64
    want = sum(1 << i for i in range(len(source['mis']), len(rows)))
    inputs = [sum(1 << r for r, mask in enumerate(rows) if mask >> v & 1) for v in range(n)]
    covers = []
    for count in range(n + 1):
        for cover in itertools.combinations(range(n), count):
            if all(a in cover or b in cover for a, b in edges):
                covers.append(cover)
        if covers:
            break
    seeds = []
    for _ in range(128):
        cover = list(rng.choice(covers)); rng.shuffle(cover)
        stars = {v: [] for v in cover}
        for a, b in edges:
            center = rng.choice([v for v in (a, b) if v in stars])
            stars[center].append(b if center == a else a)
        gates = []
        def add(op, a, b):
            gates.append([op, a, b]); return n + len(gates) - 1
        outputs = []
        for v in cover:
            neighbors = stars[v]
            if not neighbors: continue
            rng.shuffle(neighbors)
            wires = neighbors[:]
            while len(wires) > 1:
                a = wires.pop(rng.randrange(len(wires)))
                b = wires.pop(rng.randrange(len(wires)))
                wires.append(add(1, a, b))
            outputs.append(add(0, v, wires[0]))
        while len(outputs) > 1:
            a = outputs.pop(rng.randrange(len(outputs)))
            b = outputs.pop(rng.randrange(len(outputs)))
            outputs.append(add(1, a, b))
        assert len(gates) == size
        values = inputs[:]
        for op, a, b in gates:
            values.append(values[a] | values[b] if op else values[a] & values[b])
        assert values[outputs[0]] == want
        seeds.append({'gates': gates, 'output': outputs[0]})
    model = dict(name=name, n=n, k=size-1, rows=rows, target=want, inputs=inputs,
                 edges=edges, seeds=seeds)
    models.append(model)
(ROOT/'minimize-data.json').write_text(json.dumps(models, indent=2)+'\n')
with (ROOT/'minimize-data.txt').open('w') as f:
    f.write(str(len(models))+'\n')
    for m in models:
        f.write(f"{m['name']} {m['n']} {m['k']} {len(m['rows'])} {len(m['seeds'])}\n")
        f.write(str(m['target'])+'\n')
        f.write(' '.join(map(str,m['inputs']))+'\n')
        for s in m['seeds']:
            f.write(str(s['output'])+'\n')
            for g in s['gates']:f.write(' '.join(map(str,g))+'\n')
print(json.dumps([{k:m[k] for k in ['name','n','k']}|{'decisive_rows':len(m['rows']),'seeds':len(m['seeds'])} for m in models]))
