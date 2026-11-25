import itertools
import json
from pathlib import Path

base = Path('/tmp/oec/pequalnp-pilot-62')
data = json.loads((base / 'multi-output-line-neighborhoods.json').read_text())
requirements = []
for target in data['targets']:
    rows = sorted({data['negative_samples'][i] for i in target['negative_rows']})
    requirements.extend((target['positive_mask'],q) for q in rows
                        if not any(q != r and q & r == q for r in rows))

def cost(wires,target):
    best = {0:0}
    for wire in wires:
        for mask,count in list(best.items()):
            new = mask | (wire & target)
            best[new] = min(best.get(new,4),count+1)
    return best.get(target,4)

best = (0,None)
for union in itertools.combinations(range(13),4):
    for left in itertools.combinations(union,2):
        a = sum(1 << i for i in left)
        b = sum(1 << i for i in union if i not in left)
        if a > b: continue
        drop = 0
        for target,cap in requirements:
            if (a | b) & cap: continue
            wires = [1 << i for i in range(13) if target >> i & 1] + [a,b]
            drop += cost(wires,target) - cost(wires+[a | b],target)
        if drop > best[0]: best = (drop,(a,b))
result = {'max_drop_for_two_disjoint_pairs':best,'normalization_per_pencil':54}
(base / 'union-pair-potential.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
