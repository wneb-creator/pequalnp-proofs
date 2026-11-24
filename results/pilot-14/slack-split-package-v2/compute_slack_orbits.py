from pathlib import Path
import json
p = Path(__file__).parent
data = json.loads((p / 'Data414.json').read_text())
rows = json.loads((p / 'slack-one-counts-nomemo.json').read_text())['rows']
mask = (1 << 828) - 1
phase = lambda x: x ^ mask if (x >> 477) & 1 else x
original = [(int(a, 0) << 414) | int(b, 0) for a, b in data['raw']]
raw = [phase(x) for x in original]
signals = [int(row['signal'], 0) for row in rows]
lookup = {s: i for i, s in enumerate(signals)}
recipes = {}
for i, a in enumerate(raw):
    for j, b in enumerate(raw):
        for sa in (0, 1):
            for sb in (0, 1):
                z = phase((a ^ (mask if sa else 0)) & (b ^ (mask if sb else 0)))
                recipes.setdefault(z, (i, j, sa, sb))
actions = []
for z in signals:
    i, j, sa, sb = recipes[z]
    fa = sa ^ int(original[i] != raw[i])
    fb = sb ^ int(original[j] != raw[j])
    actions.append([
        lookup[phase((original[perm[i]] ^ (mask if fa else 0)) &
                     (original[perm[j]] ^ (mask if fb else 0)))]
        for perm in data['autos']
    ])
groups = {}
for i, action in enumerate(actions):
    groups.setdefault(min(action), []).append(i)
proper = [
    {'representative': i, 'recipe': recipes[signals[i]], 'members': members,
     'calls': rows[i]['valid_calls'], 'moves': rows[i]['moves']}
    for i, members in groups.items() if signals[i] not in raw and signals[i] != 0
]
for group in proper:
    assert len({rows[i]['valid_calls'] for i in group['members']}) == 1
    assert len({rows[i]['moves'] for i in group['members']}) == 1
result = {'proper_orbits': proper, 'all_orbits': groups,
          'actions': actions, 'recipes': [recipes[z] for z in signals]}
(p / 'SlackOneOrbitData.json').write_text(json.dumps(result, separators=(',', ':')) + '\n')
print('orbits', len(groups), 'proper', len(proper),
      'representative calls', sum(g['calls'] for g in proper),
      'representative trials', sum(g['moves'] for g in proper))
