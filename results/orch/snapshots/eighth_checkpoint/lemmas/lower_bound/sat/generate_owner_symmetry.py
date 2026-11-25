import argparse
import itertools
import json
from pathlib import Path


def generate(case):
    n, r = case['inputs'], case['raw_inputs']
    owners = sorted({a for a, _ in case['edges']})
    assert len(owners) <= 6
    lines = sorted(set(range(r)) - set(owners))
    incident = {line: frozenset(a for a, b in case['edges'] if b == line) for line in lines}
    by_incident = {value: key for key, value in incident.items()}
    assert len(by_incident) == len(lines)
    features = [frozenset(f['raw_indices']) for f in case['features']]
    by_feature = {support: r + i for i, support in enumerate(features)}
    assert len(by_feature) == len(features)
    templates = case.get('zero_extra_template_groups')
    template_family = ({frozenset(frozenset(t) for t in group) for group in templates}
                       if templates else None)
    optional = {frozenset(group) for group in case.get('optional_prefix_groups', [])}
    permutations = []
    for perm in itertools.permutations(owners):
        mapping = dict(zip(owners, perm))
        target_incident = {line: frozenset(mapping[p] for p in incident[line]) for line in lines}
        if any(support not in by_incident for support in target_incident.values()):
            continue
        mapping.update({line: by_incident[support] for line, support in target_incident.items()})
        transformed = [frozenset(mapping[j] for j in support) for support in features]
        if any(support not in by_feature for support in transformed):
            continue
        full = [mapping[i] for i in range(r)] + [by_feature[support] for support in transformed]
        assert sorted(full) == list(range(n))
        assert sorted((full[a], full[b]) for a, b in case['edges']) == sorted(map(tuple, case['edges']))
        if {frozenset(full[i] for i in group) for group in optional} != optional:
            continue
        if templates and {frozenset(frozenset(full[i] for i in t) for t in group)
                          for group in templates} != template_family:
            continue
        permutations.append(full)
    lookup = {tuple(p) for p in permutations}
    assert len(lookup) == len(permutations)
    assert all(tuple(p[q[i]] for i in range(n)) in lookup
               for p in permutations for q in permutations)
    representatives = {min((tuple(sorted((p[a], p[b]))) for p in permutations),
                           key=lambda pair: (pair[1], pair[0]))
                       for a, b in itertools.combinations(range(n), 2)}
    return dict(inputs=n, raw_inputs=r, edges=case['edges'], permutations=permutations,
                first_pairs=[list(p) for p in sorted(representatives, key=lambda p: (p[1], p[0]))],
                group_order=len(permutations),
                status='All maps preserve edges, feature supports and outside-tree compatibility.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('packet', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    packet = json.loads(args.packet.read_text())
    case = packet[0] if isinstance(packet, list) else packet
    result = generate(case)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(group_order=result['group_order'], first_pair_orbits=len(result['first_pairs']))))
