from pathlib import Path
import json, subprocess

root = Path('/tmp/oec/pequalnp-pilot-184/clean-and-search')
cases = json.loads((root / 'cases.json').read_text())
for c in cases:
    n, s = c['n'], c['upper_bound']
    cnf = root / (c['name'] + '-upper-safe.cnf')
    generated = subprocess.run([
        'python3', str(root / 'gen.py'), str(n), str(s),
        str(root / (c['name'] + '.edges.json')), str(cnf), 'safe'
    ], text=True, capture_output=True, check=True)
    assert not generated.stderr
    metadata = json.loads(generated.stdout)
    rows = metadata['rows']
    A = (1 << n) + n + s + 2
    ix = lambda kd, j, a: (kd * (s + 1) + j) * A + a + 1
    positive = set()
    for j, (op, a, b) in enumerate(c['witness_gates']):
        a, b = sorted((a, b))
        positive.update((ix(0, j, op), ix(1, j, a), ix(2, j, b)))
    for r in rows:
        wires = [bool(r >> i & 1) for i in range(n)]
        for j, (op, a, b) in enumerate(c['witness_gates']):
            a, b = sorted((a, b))
            u, v = wires[a], wires[b]
            w = u and v if op == 0 else u or v
            if u: positive.add(ix(4, j, r))
            if v: positive.add(ix(5, j, r))
            if w: positive.add(ix(3, j, r))
            wires.append(w)
    count = 0
    for line in cnf.read_text().splitlines():
        if line.startswith('p '): continue
        clause = list(map(int, line.split()))[:-1]
        assert any((v > 0) == (abs(v) in positive) for v in clause), (c['name'], clause)
        count += 1
    print(c['name'], 'safe upper bound', s, 'satisfies all', count, 'generated clauses', flush=True)
