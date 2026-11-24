"""Finite diagnostic for four-clause products below bipartite C4-free graph functions."""
import argparse
import itertools
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pairs = list(itertools.combinations(range(6), 2))
    positions = {pair: i for i, pair in enumerate(pairs)}
    pair_truth = [sum(1 << t for t in range(64) if t >> i & 1 and t >> j & 1)
                  for i, j in pairs]
    hosts = {}
    for tail in itertools.combinations(range(1, 6), 2):
        left = {0, *tail}
        cross = [pair for pair in pairs if (pair[0] in left) != (pair[1] in left)]
        for mask in range(1 << len(cross)):
            edges = [edge for i, edge in enumerate(cross) if mask >> i & 1]
            neighbors = [{b if a == i else a for a, b in edges if i in (a, b)}
                         for i in range(6)]
            if any(len(neighbors[a] & neighbors[b]) >= 2 for a, b in pairs):
                continue
            code, truth = 0, 0
            for edge in edges:
                code |= 1 << positions[edge]
                truth |= pair_truth[positions[edge]]
            hosts[code] = (edges, truth)
    rows, counterexamples = [], []
    permutations = list(itertools.permutations(range(4)))
    for patterns in itertools.combinations(range(1, 15), 6):
        accepted = [(i, j) for i, j in pairs if patterns[i] | patterns[j] == 15]
        if any(all(a in cover or b in cover for a, b in accepted)
               for cover in itertools.combinations(range(6), 2)):
            continue
        code = sum(1 << positions[edge] for edge in accepted)
        possible = [(host, edges, truth) for host, (edges, truth) in hosts.items()
                    if code & ~host == 0]
        if not possible:
            continue
        truth = 0
        for assignment in range(64):
            union = 0
            for i, pattern in enumerate(patterns):
                if assignment >> i & 1:
                    union |= pattern
            if union == 15:
                truth |= 1 << assignment
        failures = []
        for host, edges, host_truth in possible:
            bad = truth & ~host_truth
            if not bad:
                counterexamples.append({'patterns': patterns, 'host_edges': edges})
            failures.append({'host_code': host, 'bad_assignments': bad})
        canonical = min(tuple(sorted(sum(1 << permutation[b] for b in range(4) if pattern >> b & 1)
                                     for pattern in patterns)) for permutation in permutations)
        row = {'patterns': patterns, 'accepted_pairs': accepted,
               'canonical_clause_permutation': canonical,
               'possible_hosts': len(possible), 'failures': failures}
        rows.append(row)
    orbits = {}
    for row in rows:
        orbits.setdefault(tuple(row['canonical_clause_permutation']), []).append(row)
    summary = {'six_variable_hosts': len(hosts), 'pattern_families': 3003,
               'candidate_families': len(rows), 'clause_permutation_orbits': len(orbits),
               'counterexamples': counterexamples}
    result = {'summary': summary, 'rows': rows}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(summary))
    for canonical, orbit in sorted(orbits.items()):
        sample = orbit[0]
        print(json.dumps({'canonical': canonical, 'orbit_size': len(orbit),
                          'accepted_pairs': sample['accepted_pairs'],
                          'possible_hosts': sample['possible_hosts']}))
    print('Computational diagnostic only; no Lean theorem is asserted.')


if __name__ == '__main__':
    main()
