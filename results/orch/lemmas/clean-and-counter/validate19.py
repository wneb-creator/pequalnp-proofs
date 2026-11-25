import json
from pathlib import Path

edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
         (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
records = []
for path in sorted(Path('.').glob('best-category-*.json')):
    data = json.loads(path.read_text())
    fp, fn, unsafe = [], [], set()
    for assignment in range(1024):
        values = [bool(assignment >> i & 1) for i in range(10)]
        target = any(values[a] and values[b] for a, b in edges)
        for gate_index, gate in enumerate(data['gates']):
            op, *indices = gate
            args = [values[i] if i < len(values) else False for i in indices]
            assert op in ('and', 'or') and len(args) <= 2
            value = all(args) if op == 'and' else any(args)
            values.append(value)
            if op == 'and' and value and not target:
                unsafe.add(gate_index)
        actual = values[data['output']] if data['output'] < len(values) else False
        if actual and not target:
            fp.append(assignment)
        if target and not actual:
            fn.append(assignment)
    assert len(fp) == data['false_positives']
    assert len(fn) == data['false_negatives']
    records.append({'file': path.name, 'gate_count': len(data['gates']),
                    'false_positives': fp, 'false_negatives': fn,
                    'unsafe_and_gates': sorted(unsafe)})
    print(path.name, 'FP', len(fp), 'FN', len(fn), 'unsafe ANDs', sorted(unsafe))
Path('search19-independent-validation.json').write_text(json.dumps(records, indent=2) + '\n')
