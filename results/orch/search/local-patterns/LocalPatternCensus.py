"""Enumerate line-intersection histograms of selected plane-point subsets."""
import argparse
import itertools
import json
import re
from pathlib import Path


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--statement', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    edges = [(int(a), int(b)) for a, b in
             re.findall(r'\((\d+), (\d+)\)', args.statement.read_text())]
    assert len(edges) == len(set(edges)) == 105
    lines = [sum(1 << a for a, b in edges if b == v) for v in range(21, 42)]
    assert all(line.bit_count() == 5 for line in lines)
    result = []
    for k in range(4, 9):
        counts = {}
        for points in itertools.combinations(range(21), k):
            mask = sum(1 << point for point in points)
            histogram = [0] * 6
            for line in lines:
                histogram[(line & mask).bit_count()] += 1
            key = tuple(histogram)
            if key not in counts:
                counts[key] = [0, points]
            counts[key][0] += 1
        for histogram, (count, points) in sorted(counts.items()):
            groups = {}
            for v in range(21, 42):
                support = tuple(i for i, point in enumerate(points) if (point, v) in edges)
                if support:
                    groups.setdefault(support, []).append(v)
            outside = sum(len(group) - 1 for group in groups.values())
            local_edges = sum(len(support) for support in groups)
            assert local_edges + outside == 5 * k
            negatives = set()
            for selected in range(1 << k):
                allowed = [support for support in groups
                           if not any(selected >> point & 1 for point in support)]
                closed = sum(1 << point for point in range(k)
                             if not any(point in support for support in allowed))
                negatives.add((closed, tuple(allowed)))
            row = {'points': points, 'k': k, 'histogram': histogram, 'count': count,
                   'groups': len(groups), 'inputs': k + len(groups),
                   'core_edges': local_edges, 'outside_or_cost': outside,
                   'baseline_core': local_edges + k - 1,
                   'target_core': 6 * k - 2 - outside,
                   'closed_negative_tests': len(negatives)}
            result.append(row)
            print(json.dumps(row))
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('TOTAL_HISTOGRAM_CLASSES', len(result))


if __name__ == '__main__':
    main()
