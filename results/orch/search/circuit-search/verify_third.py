import itertools,json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
review=Path('/tmp/oec/pequalnp-pilot-70/sat-review')
meta=json.loads((base/'shadow3-26.map.json').read_text())
original=(base/'shadow3-26.cnf').read_text().splitlines()
extended=(review/'third-shadow3-26.cnf').read_text().splitlines()
assert extended[1:1+meta['clauses']]==original[1:]
assert extended[0]==f"p cnf {meta['nv']} {meta['clauses']+3715}"
lookup={}
for gate,g in enumerate(meta['structure'][:3]):
 for side in ['left','right']:
  for index,v in enumerate(g[side]):lookup[v]=(gate,side,index)
actual=set()
for line in extended[1+meta['clauses']:]:
 c=list(map(int,line.split()));assert len(c)==7 and c[-1]==0 and all(v<0 for v in c[:-1])
 labels=[lookup[-v] for v in c[:-1]]
 assert [(g,s) for g,s,i in labels]==[(0,'left'),(0,'right'),(1,'left'),(1,'right'),(2,'left'),(2,'right')]
 assert labels[0][2]==0
 actual.add(tuple(x[2] for x in labels[1:]))
assert len(actual)==3715
data=json.loads((review/'verified_symmetry.json').read_text())
autos=[p+[14,15] for p in data['automorphisms']]
expected=set()
for code in data['representatives']:
 first=(0,code//225);second=(code%225//15,code%15)
 group=[p for p in autos if {p[x] for x in first}==set(first) and {p[x] for x in second}==set(second)]
 assert group
 for a,b in itertools.combinations_with_replacement(range(16),2):
  smallest=min(tuple(sorted((p[a],p[b]))) for p in group)
  if (a,b)!=smallest:expected.add((first[1],second[0],second[1],a,b))
assert actual==expected
print('PASS: original clauses and variable IDs preserved; all 3715 added six-literal bans independently match stabilizer orbit minima')
