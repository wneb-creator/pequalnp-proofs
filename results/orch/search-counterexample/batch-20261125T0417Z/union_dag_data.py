import json
from pathlib import Path

base = Path('/tmp/oec/pequalnp-pilot-62')
data = json.loads((base / 'multi-output-line-neighborhoods.json').read_text())
requirements = []
for target in data['targets']:
    mask = target['positive_mask']
    rows = sorted({data['negative_samples'][i] for i in target['negative_rows']})
    maximal = [q for q in rows if not any(q != r and q & r == q for r in rows)]
    requirements.extend((mask, q) for q in maximal)
with (base / 'union-dag-data.txt').open('w') as out:
    print(13, len(requirements), file=out)
    print(*(target['positive_mask'] for target in data['targets']), file=out)
    for p, q in requirements:
        print(p, q, file=out)
print(json.dumps({'requirements': len(requirements), 'target_count': 13}))
