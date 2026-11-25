import json
from pathlib import Path

EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
         (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]


def validate(path, seeded=True):
    data = json.loads(path.read_text())
    false_positives = []
    false_negatives = []
    for assignment in range(1024):
        values = [bool(assignment >> i & 1) for i in range(10)]
        if seeded:
            values.append(values[0] and values[2])
        for gate in data['gates']:
            op, *indices = gate
            inputs = [values[i] if i < len(values) else False for i in indices]
            if op == 'and':
                result = all(inputs)
            elif op == 'or':
                result = any(inputs)
            elif op == 'not':
                result = not (inputs[0] if inputs else False)
            else:
                raise ValueError(op)
            assert len(indices) <= 2
            values.append(result)
        result = values[data['output']] if data['output'] < len(values) else False
        expected = any((assignment >> a & 1) and (assignment >> b & 1)
                       for a, b in EDGES)
        if result and not expected:
            false_positives.append(assignment)
        if expected and not result:
            false_negatives.append(assignment)
    record = {'file': path.name, 'gates': len(data['gates']),
              'false_positives': false_positives, 'false_negatives': false_negatives}
    if 'false_positives' in data:
        assert len(false_positives) == data['false_positives'], record
        assert len(false_negatives) == data['false_negatives'], record
    return record


records = [validate(Path('twenty-gates.json'), seeded=False)]
records.append(validate(Path('four-error-candidate.json')))
records += [validate(p) for p in sorted(Path('.').glob('best-category-*.json'))]
Path('independent-validation.json').write_text(json.dumps(records, indent=2) + '\n')
for item in records:
    print(item['file'], 'gates', item['gates'], 'FP', len(item['false_positives']),
          'FN', len(item['false_negatives']))
