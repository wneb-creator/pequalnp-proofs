import itertools
import json
from pathlib import Path


def girth_witness(neighbors):
    n = len(neighbors)
    for a in range(n):
        for b in range(a + 1, n):
            common = neighbors[a] & neighbors[b]
            if (neighbors[a] >> b & 1) and common:
                return ('triangle', a, b, (common & -common).bit_length() - 1)
            if common.bit_count() >= 2:
                first = common & -common
                second = common ^ first
                return ('four_cycle', a, first.bit_length() - 1, b,
                        (second & -second).bit_length() - 1)
    return None


def minimal_covers(n, edges):
    covers = []
    for mask in range(1 << n):
        if not all(mask >> a & 1 or mask >> b & 1 for a, b in edges):
            continue
        if all(any((mask ^ (1 << v)) >> a & 1 == 0 and
                   (mask ^ (1 << v)) >> b & 1 == 0 for a, b in edges)
               for v in range(n) if mask >> v & 1):
            covers.append(mask)
    return covers


rows = []
examples = {}
for n in range(7):
    pairs = list(itertools.combinations(range(n), 2))
    core_count = 0
    extension_count = 0
    unexpected = []
    for mask in range(1 << len(pairs)):
        edges = [e for i, e in enumerate(pairs) if mask >> i & 1]
        neighbors = [0] * n
        for a, b in edges:
            neighbors[a] |= 1 << b
            neighbors[b] |= 1 << a
        if girth_witness(neighbors):
            continue
        core_count += 1
        covers = minimal_covers(n, edges)
        extended = neighbors + [0] * len(covers)
        for i, cover in enumerate(covers):
            extended[n + i] = cover
            for v in range(n):
                if cover >> v & 1:
                    extended[v] |= 1 << (n + i)
        obstruction = girth_witness(extended)
        degree = max((v.bit_count() for v in neighbors), default=0)
        expected = degree <= 1 and len(edges) <= 2
        if obstruction is None:
            extension_count += 1
        if (obstruction is None) != expected:
            unexpected.append({'edges': edges, 'covers': covers,
                               'obstruction': obstruction})
        if n == 3 and edges == [(0, 1), (0, 2)]:
            examples['degree_two'] = {'edges': edges, 'covers': covers,
                                      'obstruction': obstruction}
        if n == 6 and edges == [(0, 1), (2, 3), (4, 5)]:
            examples['three_edge_matching'] = {'edges': edges, 'covers': covers,
                                               'obstruction': obstruction}
    rows.append({'n': n, 'all_labeled_graphs': 1 << len(pairs),
                 'girth_at_least_five_cores': core_count,
                 'girth_at_least_five_extensions': extension_count,
                 'unexpected': unexpected})
    print(rows[-1], flush=True)
    assert not unexpected

Path('cover-extension-results.json').write_text(
    json.dumps({'rows': rows, 'examples': examples}, indent=2) + '\n')
