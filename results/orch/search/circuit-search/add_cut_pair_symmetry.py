import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('cnf', type=Path)
parser.add_argument('actions', type=Path)
parser.add_argument('output', type=Path)
parser.add_argument('--variant', type=int)
args = parser.parse_args()
metadata = json.loads(args.cnf.with_suffix('.map.json').read_text())
assert 'variant_selectors' not in metadata, 'Use a selector-aware normalizer for joint families'
correlated = metadata['correlated']
assert correlated and metadata.get('prefix') is None
assert not any(key in metadata for key in ('repair', 'auxiliary_prefix', 'fixed_smoke_gates', 'cut_pair_symmetry'))
assert not metadata.get('minimal') and metadata.get('minimal_prefix', 0) == 0
assert metadata.get('shadow_missing', 0) == 0 and not metadata.get('dirty_and')
assert metadata.get('canonical_prefix') is False, 'Canonical-prefix restrictions are not supported'
assert metadata.get('ordered_max') is False, 'Maximum-fanin ordering is not supported'
assert metadata.get('liveness') is False, 'Correlated input liveness is not supported'
assert metadata.get('allow_initial_repeats') is True, 'Repeated initial fanins must be allowed'
assert metadata.get('allow_trivial') is True, 'Trivial gate signatures must be allowed for padding'
certificate = json.loads(args.actions.read_text())
if args.variant is not None:
    certificate = next(item for item in certificate['variants'] if item['variant'] == args.variant)
permutations = certificate['permutations']
ninputs = metadata['ninputs']
nreal = correlated['real_inputs']
supports = [[i] for i in range(nreal)] + correlated.get('free_or_supports', correlated.get('free_or_sums', []))
assert len(supports) == ninputs
group = {tuple(p) for p in permutations}
assert len(group) == len(permutations) and tuple(range(ninputs)) in group
edges = {tuple(sorted(edge)) for edge in metadata['edges']}
for permutation in permutations:
    assert sorted(permutation) == list(range(ninputs))
    underlying = permutation[:nreal]
    assert sorted(underlying) == list(range(nreal))
    assert {tuple(sorted((underlying[a], underlying[b]))) for a, b in edges} == edges
    for i, support in enumerate(supports):
        assert {underlying[j] for j in support} == set(supports[permutation[i]])
    for other in permutations:
        assert tuple(permutation[other[i]] for i in range(ninputs)) in group
pairs = [(a, b) for a in range(ninputs) for b in range(a, ninputs)]
representative = {pair: min(tuple(sorted((p[pair[0]], p[pair[1]]))) for p in permutations) for pair in pairs}
representatives = sorted(set(representative.values()))
assert representatives == sorted(map(tuple, certificate['all_first_pair_representatives']))
first = metadata['structure'][0]
clauses = [[-first['left'][a], -first['right'][b]] for a, b in pairs if representative[(a, b)] != (a, b)]
lines = args.cnf.read_text().splitlines(keepends=True)
headers = [i for i, line in enumerate(lines) if line.startswith('p cnf ')]
assert len(headers) == 1
header = headers[0]
_, _, variables, count = lines[header].split()
assert int(variables) == metadata['nv'] and int(count) == metadata['clauses']
assert not args.output.exists() and not args.output.with_suffix('.map.json').exists()
metadata['clauses'] += len(clauses)
lines[header] = f'p cnf {metadata["nv"]} {metadata["clauses"]}\n'
lines.extend(' '.join(map(str, clause)) + ' 0\n' for clause in clauses)
metadata['cut_pair_symmetry'] = {'automorphisms': len(permutations), 'all_pairs': len(pairs),
                                'representatives': representatives, 'added_clauses': len(clauses),
                                'repeated_pairs_included': True,
                                'scope': 'global first-pair normal form under validated correlated-input automorphisms and topological reorderings',
                                'base_sha256': hashlib.sha256(args.cnf.read_bytes()).hexdigest(),
                                'certificate_sha256': hashlib.sha256(args.actions.read_bytes()).hexdigest()}
args.output.write_text(''.join(lines))
args.output.with_suffix('.map.json').write_text(json.dumps(metadata, separators=(',', ':')) + '\n')
print(json.dumps(metadata['cut_pair_symmetry']))
