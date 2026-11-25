from pathlib import Path
from itertools import permutations
from collections import Counter
import json,time
start=time.monotonic();source=json.loads(Path('results/orch/lemmas/stochastic-p10-fourunit.json').read_text());N=[11,69,98,49,88,44,22];T=set(N[:4])
def remap(m,p):return sum(1<<p[i]for i in range(7)if m>>i&1)
autos=[p for p in permutations(range(7))if {remap(m,p)for m in N}==set(N)and{remap(m,p)for m in T}==T]
assert len(autos)==6
classes={}
for row in source['survivors']:
 images=[tuple(sorted(remap(m,p)for m in row['units']))for p in autos];key=min(images)
 classes.setdefault(key,[]).append(row)
rows=[dict(canonical=list(key),orbit_size=len(values),examples=values)for key,values in sorted(classes.items())]
r=dict(scope='Residual-unit permutations already quotiented by multisets; quotient by all six Fano line automorphisms preservingI0123. Abstract necessary-condition survivors only, not circuits.',automorphisms=[list(p)for p in autos],survivor_count=len(source['survivors']),classes=rows,seconds=time.monotonic()-start)
Path('results/orch/lemmas/stochastic-p10-fourunit-classes.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(dict(classes=[dict(canonical=x['canonical'],orbit_size=x['orbit_size'])for x in rows],class_count=len(rows),survivor_count=r['survivor_count'],seconds=r['seconds'])))
