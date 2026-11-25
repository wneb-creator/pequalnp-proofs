"""Enumerate all C4-free 6-by-6 graphs of minimum degree at least two."""
import itertools
import json
import time
from collections import Counter
from functools import lru_cache
from pathlib import Path


N = 6
PERMS = list(itertools.permutations(range(N)))
TRANSFORMS = {
    perm: [sum(1 << perm[i] for i in range(N) if mask >> i & 1) for mask in range(1 << N)]
    for perm in PERMS}
PAIRS = list(itertools.combinations(range(N), 2))
CANDIDATES = [(mask, sum(1 << i for i, (a, b) in enumerate(PAIRS)
                         if mask >> a & 1 and mask >> b & 1))
              for mask in range(1 << N) if mask.bit_count() >= 2]


def transpose(rows):
    return tuple(sum(1 << a for a, row in enumerate(rows) if row >> b & 1) for b in range(N))


@lru_cache(None)
def degree_maps(degrees):
    groups = [[i for i, degree in enumerate(degrees) if degree == d] for d in sorted(set(degrees))]
    mappings = []
    for choices in itertools.product(*(itertools.permutations(group) for group in groups)):
        permutation = [0] * N
        for new, old in enumerate(itertools.chain.from_iterable(choices)):
            permutation[old] = new
        mappings.append(tuple(permutation))
    return mappings


def canonical_one_side(rows):
    degrees = tuple(sum(row >> b & 1 for row in rows) for b in range(N))
    return min(tuple(sorted(TRANSFORMS[perm][row] for row in rows)) for perm in degree_maps(degrees))


def canonical(rows):
    return min(canonical_one_side(rows), canonical_one_side(transpose(rows)))


def complete_orbit(rows):
    return {tuple(sorted(TRANSFORMS[perm][row] for row in oriented))
            for oriented in [rows, transpose(rows)] for perm in PERMS}


def enumerate_families():
    classes = Counter()
    families = 0
    visited = 0

    def recurse(start, chosen, used_pairs, degrees):
        nonlocal families, visited
        visited += 1
        remaining = N - len(chosen)
        if remaining == 0:
            if min(degrees) >= 2:
                families += 1
                classes[canonical(tuple(chosen))] += 1
            return
        for i in range(start, len(CANDIDATES) - remaining + 1):
            mask, pairs = CANDIDATES[i]
            if pairs & used_pairs:
                continue
            union = used_pairs | pairs
            if len(PAIRS) - union.bit_count() < remaining - 1:
                continue
            changed = tuple(d + (mask >> b & 1) for b, d in enumerate(degrees))
            if any(d + remaining - 1 < 2 for d in changed):
                continue
            recurse(i + 1, chosen + [mask], union, changed)

    recurse(0, [], 0, (0,) * N)
    return classes, families, visited


def graph_statistics(rows):
    edges = [(a, b) for a, row in enumerate(rows) for b in range(N) if row >> b & 1]
    assert all((a & b).bit_count() <= 1 for a, b in itertools.combinations(rows, 2))
    degrees = [row.bit_count() for row in rows] + [sum(row >> b & 1 for row in rows) for b in range(N)]
    assert min(degrees) >= 2
    matching = next(([(a, perm[a]) for a in range(N)] for perm in PERMS
                     if all(rows[a] >> perm[a] & 1 for a in range(N))), None)
    adjacency = [0] * (2 * N)
    for a, b in edges:
        adjacency[a] |= 1 << (N + b)
        adjacency[N + b] |= 1 << a
    independent = [True] * (1 << (2 * N))
    neighbours = [0] * (1 << (2 * N))
    for mask in range(1, 1 << (2 * N)):
        low = mask & -mask
        vertex = low.bit_length() - 1
        rest = mask ^ low
        independent[mask] = independent[rest] and not (adjacency[vertex] & rest)
        neighbours[mask] = neighbours[rest] | adjacency[vertex]
    full = (1 << (2 * N)) - 1
    maximal = [mask for mask in range(1 << (2 * N))
               if independent[mask] and mask | neighbours[mask] == full]
    return {
        'p': N, 'l': N, 'edges': edges, 'degrees': degrees,
        'perfect_matching': matching, 'cover_number': N if matching is not None else None,
        'maximal_independent_count': len(maximal), 'maximal_independent_masks': maximal,
        'MIS_size_distribution': dict(sorted(Counter(mask.bit_count() for mask in maximal).items())),
        'log2_AND_lower_bound': (len(maximal) - 1).bit_length(),
        'AND5_not_excluded_by_MIS': matching is not None and len(maximal) <= 32,
        'AND_counterexample_budget': 5}


def main():
    start = time.monotonic()
    root = Path(__file__).resolve().parent
    out = root / 'cases6'
    out.mkdir(exist_ok=True)
    classes, families, visited = enumerate_families()
    seen_orbits = set()
    records = []
    for rows, count in sorted(classes.items()):
        orbit = complete_orbit(rows)
        assert len(orbit) == count
        orbit_key = min(orbit)
        assert orbit_key not in seen_orbits
        seen_orbits.add(orbit_key)
        assert all(canonical(other) == rows for other in orbit)
        data = graph_statistics(rows)
        code = sum(row << (N * a) for a, row in enumerate(rows))
        data.update(mask=code, row_family_count=count, labeled_graph_count=count * 720,
                    canonical_rows=rows, full_orbit_check=True)
        (out / f'graph_{code}.json').write_text(json.dumps(data, indent=2) + '\n')
        records.append(data)
    assert sum(r['row_family_count'] for r in records) == families
    # Named controls are located by full side-permutation/swap canonicalization.
    cycle = tuple((1 << a) | (1 << ((a + 1) % N)) for a in range(N))
    cycle_key = canonical(cycle)
    punctured = tuple(sum(1 << b for b in range(N) if (a - b) % 7 in (0, 1, 3)) for a in range(N))
    punctured_key = canonical(punctured)
    controls = {}
    for name, key, expected_mis, expected_edges in [
            ('cycle12', cycle_key, 29, 12), ('fano_minus_incident_pair', punctured_key, 23, 16)]:
        record = next(r for r in records if tuple(r['canonical_rows']) == key)
        assert record['maximal_independent_count'] == expected_mis and len(record['edges']) == expected_edges
        controls[name] = record['mask']
    manifest = {
        'scope': 'All C4-free bipartite graphs on6+6 labeled vertices with every degree at least2, modulo independent side permutations and side swap.',
        'class_count': len(records), 'row_family_count': families, 'labeled_graph_count': families * 720,
        'recursion_nodes': visited, 'seconds': time.monotonic() - start,
        'perfect_matching_classes': sum(r['perfect_matching'] is not None for r in records),
        'AND5_not_excluded_by_MIS_classes': sum(r['AND5_not_excluded_by_MIS'] for r in records),
        'MIS_count_distribution': dict(sorted(Counter(r['maximal_independent_count'] for r in records).items())),
        'controls': controls, 'classes': records,
        'validation': 'Every class orbit independently enumerated under all720 column permutations and transpose; orbit size matches raw enumeration count; all orbit members recanonicalized. MIS counts exact over4096 masks. A displayed matching ofsize6 plus the point-side cover certifies cover number6.'}
    (root / 'case_manifest_6x6.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({k: manifest[k] for k in manifest if k not in ['classes', 'validation']}))


if __name__ == '__main__':
    main()
