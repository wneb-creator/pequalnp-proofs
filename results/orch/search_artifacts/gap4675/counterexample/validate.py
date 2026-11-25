import argparse
import functools
import json
from pathlib import Path

@functools.lru_cache(None)
def inputs(n):
    full = (1 << (1 << n)) - 1
    return [((full // ((1 << (1 << i)) + 1)) << (1 << i)) & full for i in range(n)]

def check(graph_path, circuit_path):
    g = json.loads(Path(graph_path).read_text())
    c = json.loads(Path(circuit_path).read_text())
    n, p = g['n'], g['p']
    edges = {tuple(e) for e in g['edges']}
    assert len(edges) == len(g['edges']) and 0 < p < n
    assert all(0 <= a < p <= b < n for a, b in edges)
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    assert all(len(adj[a] & adj[b]) <= 1 for a in range(p) for b in range(a + 1, p))
    w = list(inputs(n))
    reach = [1 << i for i in range(n)]
    point_mask, all_mask = (1 << p) - 1, (1 << n) - 1
    mixed = 0
    for j, (op, a, b) in enumerate(c['gates']):
        assert op in (0, 1) and 0 <= a < n + j and 0 <= b < n + j
        w.append((w[a] | w[b]) if op else (w[a] & w[b]))
        reach.append((reach[a] | reach[b]) if op else 0)
        mixed += bool(op and (reach[-1] & point_mask) and (reach[-1] & (all_mask ^ point_mask)))
    assert 0 <= c['output'] < len(w)
    expected = 0
    for a, b in edges:
        expected |= w[a] & w[b]
    wrong = (expected ^ w[c['output']]).bit_count()
    # An independent augmenting-path implementation constructs exact certificates.
    matched_right = {}
    def augment(a, visited):
        for b in sorted(adj[a]):
            if b in visited:
                continue
            visited.add(b)
            if b not in matched_right or augment(matched_right[b], visited):
                matched_right[b] = a
                return True
        return False
    for a in range(p):
        augment(a, set())
    matching = [(a, b) for b, a in matched_right.items()]
    assert len({a for a, b in matching}) == len({b for a, b in matching}) == len(matching)
    matched_left = {a: b for a, b in matching}
    seen_left = set(range(p)) - set(matched_left)
    seen_right = set()
    while True:
        before = (len(seen_left), len(seen_right))
        for a in list(seen_left):
            seen_right.update(b for b in adj[a] if matched_left.get(a) != b)
        seen_left.update(matched_right[b] for b in seen_right if b in matched_right)
        if before == (len(seen_left), len(seen_right)):
            break
    cover = (set(range(p)) - seen_left) | seen_right
    assert all(a in cover or b in cover for a, b in edges)
    assert len(cover) == len(matching) == g['tau']
    if 'matching' in g:
        supplied = [tuple(e) for e in g['matching']]
        assert all(e in edges for e in supplied)
        assert len({a for a, b in supplied}) == len({b for a, b in supplied}) == len(supplied) == g['tau']
        mask = g['cover_mask']
        assert mask.bit_count() == g['tau'] and not (mask >> n)
        assert all((mask >> a & 1) or (mask >> b & 1) for a, b in edges)
    margin = len(c['gates']) - len(edges) - len(cover) + 1
    return {'graph': str(graph_path), 'circuit': str(circuit_path), 'n': n, 'p': p, 'edges': len(edges),
            'gates': len(c['gates']), 'full_rows': 1 << n, 'wrong_rows': wrong, 'tCount': mixed,
            'tau': len(cover), 'matching': matching, 'cover': sorted(cover), 'margin': margin,
            'is_counterexample': wrong == 0 and mixed == 0 and margin < 0}

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('graph')
    parser.add_argument('circuits', nargs='+')
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    results = [check(args.graph, path) for path in args.circuits]
    Path(args.output).write_text(json.dumps(results, indent=2) + '\n')
    for result in results:
        print('FULL CHECK', result['gates'], 'gates;', result['full_rows'], 'rows; errors', result['wrong_rows'],
              'T', result['tCount'], 'margin', result['margin'], 'CE', result['is_counterexample'])
