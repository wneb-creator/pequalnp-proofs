from pathlib import Path
import gzip
import hashlib
import importlib.util
import itertools
import json

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('encoding', ROOT / 'unknown_bipartite_and.py')
encoding = importlib.util.module_from_spec(spec)
spec.loader.exec_module(encoding)

for gates, control in [(3, False), (4, True)]:
    stem = 'unknown-bipartite-' + str(gates) + ('-control' if control else '')
    summary = json.loads((ROOT / (stem + '.json')).read_text())
    c, edge_vars, sides, outputs = encoding.encode(gates, control)
    formula = f'p cnf {c.n} {len(c.clauses)}\n' + ''.join(
        ' '.join(map(str, clause)) + ' 0\n' for clause in c.clauses)
    assert hashlib.sha256(formula.encode()).hexdigest() == summary['cnf_sha256']
    assert c.n == summary['variables'] and len(c.clauses) == summary['clauses']
    output = gzip.decompress((ROOT / (stem + '.stdout.gz')).read_bytes()).decode()
    if control:
        assert 's SATISFIABLE\n' in output and summary['returncode'] == 10
        model = set()
        for line in output.splitlines():
            if line.startswith('v '):
                model.update(int(x) for x in line[2:].split() if int(x) > 0)
        assert all(any((x > 0) == (abs(x) in model) for x in clause) for clause in c.clauses)
        candidate = summary['candidate']
        edges = {(i, j) for i in range(4) for j in range(4) if edge_vars[i][j] in model}
        assert edges == {tuple(e) for e in candidate['edges']} == {(i, i) for i in range(4)}
        decoded = [[[i for i, v in enumerate(side) if v in model] for side in gate] for gate in sides]
        chosen = [i for i, v in enumerate(outputs) if v in model]
        assert decoded == candidate['gates'] and chosen == candidate['outputs']
        for mask in range(256):
            values = [bool(mask & (1 << i)) for i in range(8)]
            for gate_id, (left, right) in enumerate(decoded):
                assert left and right and all(0 <= i < 8 + gate_id for i in left + right)
                values.append(any(values[i] for i in left) and any(values[i] for i in right))
            actual = any(values[8 + i] for i in chosen)
            expected = any(mask & (1 << i) and mask & (1 << (4 + j)) for i, j in edges)
            assert actual == expected
    else:
        assert 's UNSATISFIABLE\n' in output and summary['returncode'] == 20
    print(stem + ': deterministic CNF and archived result checked')

manifest = json.loads((ROOT / 'manifest.json').read_text())
for entry in manifest['files']:
    data = (ROOT / entry['file']).read_bytes()
    assert len(data) == entry['bytes'] and hashlib.sha256(data).hexdigest() == entry['sha256']
    if entry.get('encoding') == 'gzip':
        original = gzip.decompress(data)
        assert len(original) == entry['original_bytes']
        assert hashlib.sha256(original).hexdigest() == entry['original_sha256']
print('All file hashes and gzip payloads checked; four-AND control passes all 256 inputs.')
