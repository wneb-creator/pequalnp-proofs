import json,sys,itertools
from pathlib import Path
meta=json.loads(Path(sys.argv[1]).read_text());log=Path(sys.argv[2]).read_text();dest=Path(sys.argv[3]);n=meta['n'];k=meta['k'];edges={tuple(e) for e in meta['edges']}
assert 's SATISFIABLE' in log
true={int(x) for line in log.splitlines() if line.startswith('v ') for x in line.split()[1:] if int(x)>0}
gates=[]
for j in range(k):
 pair=[next(i for i,x in enumerate(meta['choice'][j][p]) if x in true) for p in range(2)]
 assert all(0<=a<n+j for a in pair)
 gates.append(['and' if meta['ops'][j] in true else 'or',*pair])
values=[[bool(mask>>i&1) for mask in range(1<<n)] for i in range(n)];supports=[{i} for i in range(n)];ancestors=[set() for _ in range(n)];clean=[];tops=[];junk=[]
graph=[any(mask>>a&1 and mask>>b&1 for a,b in edges) for mask in range(1<<n)]
for j,(op,a,b) in enumerate(gates):
 values.append([x and y if op=='and' else x or y for x,y in zip(values[a],values[b])]);supports.append(set() if op=='and' else supports[a]|supports[b]);ancestors.append(ancestors[a]|ancestors[b]|({a-n} if a>=n else set())|({b-n} if b>=n else set()))
 cl=all(not v or g for v,g in zip(values[-1],graph));clean.append(cl)
 if op=='and':(tops if cl else junk).append(j)
assert values[-1]==graph
violations=[(i,j) for j,(op,a,b) in enumerate(gates) if op=='and' for i in tops if i in ancestors[n+j]]
if meta['mode']!='ordinary':assert not violations
star={tuple(sorted((p,q))) for j in tops for p in supports[gates[j][1]] for q in supports[gates[j][2]]}
ustar=sorted(edges-star)
if meta['mode'].startswith('ustar'):assert(0,1) in ustar
if meta['mode'].startswith('ustar') or meta['mode']=='junk':assert junk
nested=[(i,j) for j in junk for i in junk if i in ancestors[n+j]]
if 'nested' in meta['mode']:assert nested
if meta.get('reduced'):
 for op,a,b in gates:assert any(x and not y for x,y in zip(values[a],values[b])) and any(y and not x for x,y in zip(values[a],values[b]))
report={'n':n,'gates':gates,'size':k,'graph_edges':sorted(edges),'mode':meta['mode'],'full_truth_rows':1<<n,'topform':not violations,'tops':tops,'junk':junk,'nested_junk_pairs':nested,'star_edges':sorted(star),'Ustar':ustar,'ratio_Ustar_over_size_plus_one':len(ustar)/(k+1),'leastness':'not claimed by this decoder; requires a separate lower bound or exact exclusion'}
dest.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({a:b for a,b in report.items() if a!='gates'},indent=2))
