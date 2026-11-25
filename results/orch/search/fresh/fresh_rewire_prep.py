import json
from pathlib import Path
r=json.loads(Path('fresh-singer-q3k7o3.json').read_text())
k=len(r['points']);b=len(r['lines']);groups=r['groups']
flags=[(p,k+j) for j,g in enumerate(groups) for p in g]
rows=[sum(1<<l for p,l in flags if p==i) for i in range(k)]
tests=[(1<<p)|(1<<l) for p,l in flags]+r['maximal_negative_masks']
Path('fresh-rewire-k7o3.in').write_text('\n'.join(' '.join(map(str,z)) for z in [[k,b,len(flags),len(tests)],rows,tests])+'\n')
