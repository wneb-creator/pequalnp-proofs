"""Independent archive hashes, SAT-model checks, and Petersen positive controls."""
import hashlib
import json
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-99')
FANO = BASE / 'gap2583/counterexample'


def main():
    manifest = json.loads((FANO / 'archive-review-manifest.json').read_text())
    assert isinstance(manifest, dict) and isinstance(manifest['files'], list)
    names = set()
    for entry in manifest['files']:
        assert isinstance(entry, dict) and set(entry) == {'path', 'size', 'sha256'}
        path = Path(entry['path'])
        assert path.is_relative_to(BASE) and path not in names
        names.add(path)
        content = path.read_bytes()
        assert len(content) == entry['size']
        assert hashlib.sha256(content).hexdigest() == entry['sha256'], str(path)
    print('PASS immutable manifest:', len(names), 'files,', sum(e['size'] for e in manifest['files']), 'bytes')
    for prefix in ['fano27-control', 'fano27-visible-control']:
        model = {}
        for line in (FANO / (prefix + '.stdout')).read_text().splitlines():
            if line.startswith('v '):
                for literal in map(int, line[2:].split()):
                    if literal:
                        assert abs(literal) not in model or model[abs(literal)] == (literal > 0)
                        model[abs(literal)] = literal > 0
        count = 0
        with (FANO / (prefix + '.cnf')).open() as stream:
            for line in stream:
                if not line.strip() or line.startswith('c'):
                    continue
                if line.startswith('p '):
                    _, tag, variables, expected = line.split()
                    assert tag == 'cnf'
                    variables, expected = int(variables), int(expected)
                    continue
                values = list(map(int, line.split()))
                assert values[-1] == 0 and 0 not in values[:-1]
                assert all(abs(v) <= variables for v in values[:-1])
                assert any(model[abs(v)] == (v > 0) for v in values[:-1]), (prefix, count)
                count += 1
        assert count == expected
        meta = json.loads((FANO / (prefix + '.meta.json')).read_text())
        gates = []
        for j in range(meta['gates']):
            left = [k for k, v in enumerate(meta['a'][j]) if model[v]]
            right = [k for k, v in enumerate(meta['b'][j]) if model[v]]
            assert len(left) == len(right) == 1
            gates.append([int(model[meta['ops'][j]]), left[0], right[0]])
        circuit = json.loads((FANO / (prefix + '.circuit.json')).read_text())
        assert gates == circuit['gates']
        assert circuit['output'] == 13 + len(gates)
        print('PASS', prefix, ': all', count, 'CNF clauses, one-hot sources, independent model decode')
    pet = BASE / 'counterexample'
    edges = {(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
             (5,7),(7,9),(9,6),(6,8),(8,5)}
    for name, size, not_count in [('canonical21-sanity-decoded.json', 21, 1),
                                   ('canonical22-exact2-sanity-decoded.json', 22, 2)]:
        circuit = json.loads((pet / name).read_text())
        assert len(circuit['gates']) == size
        assert sum(op == 3 for op, _, _ in circuit['gates']) == not_count
        for row in range(1024):
            values = [bool(row & (1 << j)) for j in range(10)]
            for op, a, b in circuit['gates']:
                assert op in (0,1,2,3) and 0 <= a <= len(values) and 0 <= b <= len(values)
                left = values[a] if a < len(values) else False
                right = values[b] if b < len(values) else False
                values.append((left and right) if op == 0 else (left or right) if op == 1 else
                              True if op == 2 else not left)
            actual = values[circuit['output']] if circuit['output'] < len(values) else False
            expected = any((row & (1 << a)) and (row & (1 << b)) for a, b in edges)
            assert actual == expected, (name, row)
        print('PASS', name, ': 1024 full rows,', not_count, 'NOT gates, arbitrary-output/default-false semantics')
    for entry in manifest['files']:
        path = Path(entry['path'])
        if path.suffix == '.stdout':
            verdicts = [line for line in path.read_text().splitlines() if line.startswith('s ') or line == 'c UNKNOWN']
            if verdicts:
                print('SOLVER STATUS', path.name, verdicts)
    for name in ['archive-review-supplement.json', 'archive-review-completed.json']:
        supplement = json.loads((FANO / name).read_text())
        assert isinstance(supplement, dict) and isinstance(supplement['files'], list)
        for entry in supplement['files']:
            path = Path(entry['path'])
            assert path.is_relative_to(BASE) and path not in names
            names.add(path)
            content = path.read_bytes()
            assert len(content) == entry['size']
            assert hashlib.sha256(content).hexdigest() == entry['sha256'], str(path)
        print('PASS', name, ':', len(supplement['files']), 'immutable files')
    incomplete = json.loads((FANO / 'fano26-best-incomplete.json').read_text())
    fano_edges = {(p, 7 + l) for l in range(7) for p in ((l + d) % 7 for d in (0, 1, 3))}
    edge_masks = {(1 << p) + (1 << l) for p, l in fano_edges}
    wrong = []
    for row in range(1 << 14):
        values = [bool(row & (1 << i)) for i in range(14)]
        for op, a, b in incomplete['gates']:
            assert op in (0, 1) and 0 <= a < len(values) and 0 <= b < len(values)
            values.append((values[a] and values[b]) if op == 0 else (values[a] or values[b]))
        target = any(row & edge == edge for edge in edge_masks)
        if values[incomplete['output']] != target:
            wrong.append(row)
    assert len(wrong) == 47 and len(set(wrong) & edge_masks) == 1
    print('PASS incomplete candidate rejected: 47 full truth errors, one minimal-edge error')
    print('TOTAL IMMUTABLE ARCHIVE FILES', len(names))
    print('ALL ARCHIVE CONTROLS PASSED')


if __name__ == '__main__':
    main()
