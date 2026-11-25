import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def audit(path):
    data = path.read_bytes()
    r = json.loads(data)
    P, L = r['P'], r['L']
    n, E = P + L, set(map(tuple, r['edges']))
    assert all(0 <= p < P and 0 <= l < L for p, l in E)
    assert all((p, p) in E for p in range(P))
    family = r.get('family', 'c4free')
    if family == 'c4free':
        assert not any(all((p, l) in E for p in pp for l in ll)
                       for pp in itertools.combinations(range(P), 2)
                       for ll in itertools.combinations(range(L), 2))
    elif family == 'fooling':
        assert not any((p, q) in E and (q, p) in E
                       for p, q in itertools.combinations(range(P), 2))
    else:
        raise ValueError(family)
    for i, pair in enumerate(r['macro']):
        assert len(pair) == 2
        for indices in pair:
            assert indices and all(0 <= j < n + i for j in indices)
    assert r['final'] and all(0 <= j < n + len(r['macro']) for j in r['final'])
    false_positive = false_negative = 0
    examples = []
    for x in range(1 << n):
        values = [bool(x & (1 << i)) for i in range(n)]
        for a, b in r['macro']:
            values.append(any(values[j] for j in a) and any(values[j] for j in b))
        computed = any(values[j] for j in r['final'])
        expected = any(bool(x & (1 << p)) and bool(x & (1 << (P + l))) for p, l in E)
        false_positive += computed and not expected
        false_negative += expected and not computed
        if computed != expected and len(examples) < 8:
            examples.append({'assignment': x, 'true_inputs': [i for i in range(n) if x >> i & 1],
                             'computed': computed, 'expected': expected})
    assert false_positive == r['false_positive_count']
    assert false_negative == 0
    return {'file': str(path.relative_to(ROOT)), 'sha256': hashlib.sha256(data).hexdigest(),
            'family': family, 'and_count': len(r['macro']), 'edge_count': len(E),
            'false_positives': false_positive, 'false_negatives': false_negative,
            'rejection_examples': examples}


if __name__ == '__main__':
    files = sorted(ROOT.glob('variable-*/iteration-*-model.json'))
    rows = [audit(path) for path in files]
    (ROOT / 'model-rejection-audit.json').write_text(json.dumps(rows, indent=2))
    print('AUDIT PASS', len(rows), 'models;', sum(r['false_positives'] > 0 for r in rows),
          'rejected;', sum(r['false_positives'] == 0 for r in rows), 'exact witnesses')
