"""Finite accounting and direct-read witnesses for mixed point/line decompositions.

This produces search data, not a Lean proof or a claimed circuit witness.
All data are regenerated from the posted 52-edge incidence predicate.
"""
from itertools import combinations
import json
from pathlib import Path


EDGES = [(p, 13 + l) for p in range(13) for l in range(13)
         if (p + l) % 13 in (0, 1, 3, 9)]
NEIGHBORS = {p: sorted(l for q, l in EDGES if q == p) for p in range(13)}


def prepare(owners, removed_line):
    punctured = [p for p in owners if removed_line in NEIGHBORS[p]]
    core_edges_full = [(p, l) for p, l in EDGES if p in owners and l != removed_line]
    raw_map = owners + sorted({l for _, l in core_edges_full})
    index = {v: i for i, v in enumerate(raw_map)}
    edges = [(index[p], index[l]) for p, l in core_edges_full]
    n = len(raw_map)
    features, groups, fixed, rows = [], [], [], []

    def feature(vertices):
        support = sorted(index[v] for v in vertices)
        if support not in features:
            features.append(support)
        return n + features.index(support)

    for p in range(13):
        if p in owners:
            continue
        available = sorted(set(NEIGHBORS[p]) & set(raw_map))
        assert len(available) <= 3
        row = dict(owner=p, neighbors=NEIGHBORS[p], core_lines=available)
        if len(available) >= 2:
            fixed.append(feature(available))
        if len(available) == 3:
            group = [feature(pair) for pair in combinations(available, 2)]
            groups.append(group)
            row['optional_group'] = group
        rows.append(row)
    assert 2 <= len(punctured) <= 3
    fixed.append(feature(punctured))
    if len(punctured) == 3:
        groups.append([feature(pair) for pair in combinations(punctured, 2)])

    def value(mask):
        return any(mask >> a & 1 and mask >> b & 1 for a, b in edges)

    support_masks = [sum(1 << i for i in support) for support in features]
    feature_values = [sum(bool(mask & support) << j
                          for j, support in enumerate(support_masks))
                      for mask in range(1 << n)]
    pivotal = []
    for i in range(n):
        for low in range(1 << n):
            high = low | (1 << i)
            if low == high:
                continue
            if not value(low) and value(high) and feature_values[low] == feature_values[high]:
                pivotal.append(dict(raw=i, full=raw_map[i], low=low, high=high,
                                    fixed_feature_values=feature_values[low]))
                break
        else:
            pivotal.append(dict(raw=i, full=raw_map[i], witness=None))

    closures = set()
    for pointmask in range(1 << len(owners)):
        mask = pointmask
        for j in range(len(owners), n):
            if not any(pointmask >> i & 1 and (i, j) in edges
                       for i in range(len(owners))):
                mask |= 1 << j
        closures.add(mask)
    negatives = sorted(mask for mask in closures
                       if not any(mask != other and mask & other == mask for other in closures))
    assert all(not value(mask) for mask in negatives)
    assert all(value(left | right) for left, right in combinations(negatives, 2))
    assert all(value(mask) or any(mask & negative == mask for negative in negatives)
               for mask in range(1 << n))
    outside_edges = [(p, l) for p, l in EDGES if p not in owners]
    outside_edges += [(p, removed_line) for p in punctured]
    assert set(core_edges_full).isdisjoint(outside_edges)
    assert set(core_edges_full) | set(outside_edges) == set(EDGES)
    outside_stars = 13 - len(owners)
    outside_star_cost = 5 * outside_stars - 1
    partial_line_cost = len(punctured)
    outside_cost = outside_star_cost + partial_line_cost + 1
    target = 63 - outside_cost - 1
    baseline = sum(sum(p == owner for p, _ in core_edges_full) for owner in owners)
    baseline += len(owners) - 1
    return dict(scope='Finite search packet and support witnesses only; no Lean theorem or solution.',
                owners=owners, punctured_line=removed_line, punctured_owners=punctured,
                raw_inputs=n, raw_map=raw_map, edges=edges, full_core_edges=core_edges_full,
                features=features, available_inputs=n + len(features),
                fixed_features=sorted(set(fixed)), optional_groups=groups,
                outside_rows=rows, outside_edges=outside_edges,
                outside_star_cost=outside_star_cost, partial_line_cost=partial_line_cost,
                outside_cost=outside_cost, final_or_cost=1, target_gates=target,
                raw_star_baseline_gates=baseline,
                raw_tests=[[sum(1 << i for i in edge), True] for edge in edges]
                          + [[mask, False] for mask in negatives],
                maximal_negatives=negatives, raw_pivotal_witnesses=pivotal,
                mandatory_raw_reads=sum('low' in item for item in pivotal),
                raw_support_gate_lower_bound=sum('low' in item for item in pivotal)-1)


if __name__ == '__main__':
    directory = Path(__file__).resolve().parent
    for label, owners in [('three-collinear', [0, 1, 3]), ('four-arc', [0, 1, 2, 6])]:
        data = prepare(owners, 13)
        path = directory / ('punctured-' + label + '.json')
        path.write_text(json.dumps(data, indent=2) + '\n')
        print(label, 'raw', data['raw_inputs'], 'edges', len(data['edges']),
              'features', len(data['features']), 'groups', len(data['optional_groups']),
              'negative family', len(data['maximal_negatives']),
              'outside', data['outside_cost'], 'target', data['target_gates'],
              'mandatory raw reads', data['mandatory_raw_reads'],
              'direct-support lower', data['raw_support_gate_lower_bound'])
