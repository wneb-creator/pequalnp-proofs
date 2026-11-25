import json
import sys

with open(sys.argv[1]) as source:
    data = json.load(source)
assert isinstance(data, dict) and isinstance(data.get('variants'), list)
result = []
for variant in data['variants']:
    if variant['variant'] not in (0, 6):
        continue
    permutations = variant['cut_signal_stabilizer']
    assert permutations and all(sorted(p) == list(range(17)) for p in permutations)
    pair_map = []
    for a in range(17):
        for b in range(a, 17):
            representative = min(tuple(sorted((p[a], p[b]))) for p in permutations)
            pair_map.append(dict(pair=[a,b], representative=list(representative)))
    representatives = sorted({tuple(row['representative']) for row in pair_map})
    result.append(dict(variant=variant['variant'], permutations=permutations,
                       all_first_pair_representatives=representatives,
                       complete_pair_map=pair_map))
with open(sys.argv[2], 'w') as target:
    json.dump(dict(variants=result), target, indent=2)
    target.write('\n')
print(json.dumps([dict(variant=v['variant'], automorphisms=len(v['permutations']),
                       pairs=len(v['complete_pair_map']),
                       orbits=len(v['all_first_pair_representatives'])) for v in result]))
