from pathlib import Path
import collections, hashlib, itertools, json, time

started = time.monotonic()
root = Path('/workspace/pequalnp-proofs/results/orch/search/gap4970')
manifest = json.loads((root / 'case_manifest_6x6.json').read_text())
records = manifest['classes']
assert manifest['class_count'] == len(records) == 25

# Independent exhaustive enumeration: increasing masks, direct pair intersections,
# and no pair-budget or partial-degree pruning from the submitted generator.
eligible = [mask for mask in range(64) if mask.bit_count() >= 2]
families = set()
visited = 0


def enumerate_direct(rows, candidates):
    global visited
    visited += 1
    if len(rows) == 6:
        if all(sum((row >> b) & 1 for row in rows) >= 2 for b in range(6)):
            families.add(rows)
        return
    for j, row in enumerate(candidates):
        rest = [other for other in candidates[j + 1:] if (other & row).bit_count() <= 1]
        enumerate_direct(rows + (row,), rest)


enumerate_direct((), eligible)
assert len(families) == manifest['row_family_count'] == 9976
permutations = list(itertools.permutations(range(6)))
transforms = [[sum(1 << perm[i] for i in range(6) if mask & (1 << i)) for mask in range(64)] for perm in permutations]
covered = set()
mis_distribution = collections.Counter()
survivors = []
for record in records:
    rows = tuple(record['canonical_rows'])
    transpose = tuple(sum(1 << a for a in range(6) if rows[a] & (1 << b)) for b in range(6))
    orbit = {tuple(sorted(transform[row] for row in orientation)) for orientation in (rows, transpose) for transform in transforms}
    assert len(orbit) == record['row_family_count']
    assert not (covered & orbit)
    covered |= orbit
    assert record['labeled_graph_count'] == len(orbit) * 720
    assert record['mask'] == sum(row << (6 * a) for a, row in enumerate(rows))
    edges = {(a, b) for a, row in enumerate(rows) for b in range(6) if row & (1 << b)}
    assert edges == {tuple(edge) for edge in record['edges']}
    case = json.loads((root / 'cases6' / ('graph_' + str(record['mask']) + '.json')).read_text())
    assert case == record
    matching = [tuple(edge) for edge in record['perfect_matching']]
    assert len(matching) == 6 and set(matching) <= edges
    assert len({a for a, b in matching}) == len({b for a, b in matching}) == 6
    assert record['cover_number'] == 6
    # Independent MIS enumeration over only point-side choices. All allowed
    # line vertices must be present; every omitted point must touch one of them.
    maximal = set()
    for left in range(64):
        neighbourhood = 0
        for a in range(6):
            if left & (1 << a):
                neighbourhood |= rows[a]
        right = 63 ^ neighbourhood
        if all((left & (1 << a)) or (rows[a] & right) for a in range(6)):
            maximal.add(left | (right << 6))
    assert maximal == set(record['maximal_independent_masks'])
    assert len(maximal) == record['maximal_independent_count']
    assert {str(k): v for k, v in collections.Counter(mask.bit_count() for mask in maximal).items()} == record['MIS_size_distribution']
    assert record['log2_AND_lower_bound'] == (len(maximal) - 1).bit_length()
    assert record['AND5_not_excluded_by_MIS'] == (len(maximal) <= 32)
    assert record['AND_counterexample_budget'] == 5
    if len(maximal) <= 32:
        survivors.append(record['mask'])
    mis_distribution[len(maximal)] += 1

assert covered == families
assert manifest['labeled_graph_count'] == len(families) * 720 == 7182720
assert manifest['perfect_matching_classes'] == 25
assert len(survivors) == manifest['AND5_not_excluded_by_MIS_classes'] == 24
assert {str(k): v for k, v in mis_distribution.items()} == manifest['MIS_count_distribution']
result = {
    'verdict': 'PASS for the stated minimum-degree-at-least-two 6x6 graph census and exact MIS filtering; no circuit theorem or solver result is claimed',
    'generator_sha256': hashlib.sha256((root / 'make_cases_6x6.py').read_bytes()).hexdigest(),
    'manifest_sha256': hashlib.sha256((root / 'case_manifest_6x6.json').read_bytes()).hexdigest(),
    'independent_enumerator_nodes': visited,
    'row_families': len(families), 'isomorphism_classes': len(records),
    'labeled_graphs': len(families) * 720,
    'all_expanded_orbits_disjoint_and_exactly_cover_independent_enumeration': True,
    'all_perfect_matching_certificates_verified': True,
    'all_MIS_sets_verified_by_independent_64_point_subset_algorithm': True,
    'AND5_candidates_after_MIS_filter': len(survivors),
    'limitation': 'Graphs with a vertex of degree zero or one, other side sizes, and arbitrary posted-step instances are outside this finite census. Surviving MIS filtering does not establish a circuit exists.',
    'seconds': time.monotonic() - started,
}
Path('/tmp/oec/pequalnp-pilot-94/review-census6.result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
