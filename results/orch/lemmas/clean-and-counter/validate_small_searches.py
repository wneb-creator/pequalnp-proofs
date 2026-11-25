import json
from pathlib import Path

cases = {
    'c7': [(i, (i + 1) % 7) for i in range(7)],
    'theta233': [(0, 2), (2, 1), (0, 3), (3, 4), (4, 1), (0, 5), (5, 6), (6, 1)],
}
records = []
for name, edges in cases.items():
    paths = sorted(Path(name).glob('best-category-*.json'))
    if name == 'theta233':
        paths.append(Path(name) / 'one-error-candidate.json')
    for path in paths:
        data = json.loads(path.read_text())
        fp, fn, unsafe = [], [], set()
        for assignment in range(128):
            values = [bool(assignment >> i & 1) for i in range(7)]
            target = any(values[a] and values[b] for a, b in edges)
            for gate_index, gate in enumerate(data['gates']):
                op, *indices = gate
                args = [values[i] if i < len(values) else False for i in indices]
                assert op in ('and', 'or') and len(args) <= 2
                value = all(args) if op == 'and' else any(args)
                values.append(value)
                if op == 'and' and value and not target:
                    unsafe.add(gate_index)
            output = data['output']
            actual = values[output] if output < len(values) else False
            if actual and not target:
                fp.append(assignment)
            if target and not actual:
                fn.append(assignment)
        assert len(fp) == data['false_positives']
        assert len(fn) == data['false_negatives']
        record = {'file': str(path), 'gate_count': len(data['gates']),
                  'false_positives': fp, 'false_negatives': fn,
                  'unsafe_and_gates': sorted(unsafe)}
        records.append(record)
        print(path, 'FP', len(fp), 'FN', len(fn), 'unsafe ANDs', sorted(unsafe))
Path('small-search-independent-validation.json').write_text(json.dumps(records, indent=2) + '\n')
