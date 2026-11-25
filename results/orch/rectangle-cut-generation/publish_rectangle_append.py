import argparse
import hashlib
import json
import os
from pathlib import Path

BASE = Path(__file__).resolve().parent


def encode(matrices):
    lines = [f'PNP_RECT_V1 {len(matrices)}']
    for m in matrices:
        assert sum(map(sum, m['weights'])) == m['total'] > 0
        p, n = len(m['positive_rows']), len(m['negative_rows'])
        assert 0 < p <= 21 and 0 < n <= 21
        assert len(set(m['positive_rows'])) == p and len(set(m['negative_rows'])) == n
        assert len(m['weights']) == p and all(len(row) == n for row in m['weights'])
        assert all(isinstance(w, int) and abs(w) <= 1000000 for row in m['weights'] for w in row)
        lines += [f'{m["id"]} {p} {n} {m["total"]}',
                  ' '.join(map(str, m['positive_rows'])),
                  ' '.join(map(str, m['negative_rows']))]
        lines += [' '.join(map(str, row)) for row in m['weights']]
    return '\n'.join(lines) + '\n'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('previous', type=int)
    ap.add_argument('extra', nargs='+')
    args = ap.parse_args()
    root = BASE / 'dynamic-loader'
    old = json.loads((root / f'matrices-v{args.previous}.json').read_text())
    expected = encode(old)
    assert (root / f'rectangles-v{args.previous}.txt').read_text() == expected
    assert (root / 'rectangles.txt').read_text() == expected
    extra = []
    for filename in args.extra:
        value = json.loads(Path(filename).read_text())
        extra += value if isinstance(value, list) else [value]
    known = {m['name'] for m in old}
    for i, m in enumerate(extra, max(m['id'] for m in old) + 1):
        assert m['name'] not in known
        known.add(m['name'])
        m['id'] = i
    matrices = old + extra
    data = encode(matrices)
    assert data.split('\n', 1)[1].startswith(expected.split('\n', 1)[1])
    version = args.previous + 1
    final = root / f'rectangles-v{version}.txt'
    metadata = root / f'matrices-v{version}.json'
    assert not final.exists() and not metadata.exists()
    final.write_text(data)
    metadata.write_text(json.dumps(matrices, indent=2) + '\n')
    temp = root / 'rectangles.tmp'
    temp.write_text(data)
    os.replace(temp, root / 'rectangles.txt')
    print(json.dumps({'version': version, 'count': len(matrices),
                      'new_ids': [m['id'] for m in extra],
                      'sha256': hashlib.sha256(data.encode()).hexdigest(),
                      'file': str(final)}), flush=True)


if __name__ == '__main__':
    main()
