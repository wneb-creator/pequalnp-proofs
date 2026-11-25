import itertools,json
from pathlib import Path
root=Path('/tmp/oec/pequalnp-pilot-157/12179');prefix=root/'general13_control';d=json.loads(prefix.with_suffix('.json').read_text())
# Intermediate index7+j;6 is constant false sentinel.
gs=[('and',0,1),('and',4,5),('and',7,8),('or',0,1),('or',4,5),('and',7,11),('and',8,10),('or',12,13),('and',2,14),('or',9,15),('and',3,16)]
gs += [('not',17,17),('not',18,18)]
others=[0,1,2,4,5];best=None
for pp in itertools.permutations(others):
 mp=dict(enumerate(range(7)))
 for a,b in zip(others,pp):mp[a]=b
 remain=set(range(len(gs)));out=[]
 while remain:
  ready=[((d['opnames'].index(gs[j][0]),*sorted((mp[gs[j][1]],mp[gs[j][2]]))),j) for j in remain if gs[j][1] in mp and gs[j][2] in mp]
  key,j=min(ready);out.append(key);mp[7+j]=7+len(out)-1;remain.remove(j)
 out=tuple(out)
 if best is None or out<best:best=out
tr=set();vals=[sum(1<<x for x in range(64) if x>>i&1) for i in range(6)]+[0]
for j,(op,a,b) in enumerate(best):
 tr.add(d['ops'][j][op]);tr.add(d['sels'][j][0][a]);tr.add(d['sels'][j][1][b]);z=vals[a]&vals[b] if d['opnames'][op]=='and' else vals[a]|vals[b] if d['opnames'][op]=='or' else ((1<<64)-1)^vals[a];vals.append(z)
 for x,zid in enumerate(d['vals'][j]):
  if vals[a]>>x&1:tr.add(zid-2)
  if vals[b]>>x&1:tr.add(zid-1)
  if z>>x&1:tr.add(zid)
assert vals[-1]==d['T']
last=d['vals'][-1][-1]
for j in range(1,d['k']):
 if best[j-1][1]==best[j][1]:tr.add(last+j)
reps=[(0,0),(0,1),(0,3),(0,6),(3,3),(3,6),(6,6)]
assert best[0][1:] in reps;tr.add(last+d['k']+reps.index(best[0][1:]))
rows=prefix.with_suffix('.cnf').read_text().splitlines();nv,nc=map(int,rows[0].split()[2:]);bad=[]
for i,row in enumerate(rows[1:]):
 lits=list(map(int,row.split()))[:-1]
 if not any((lit in tr) if lit>0 else (-lit not in tr) for lit in lits):bad.append(i)
assert not bad,bad[:20]
log='s SATISFIABLE\n'+'v '+' '.join(str(i if i in tr else -i) for i in range(1,nv+1))+' 0\n'
(root/'general13_control.manual.model').write_text(log)
print('PASS canonical13 double-NOT control satisfies all',nc,'clauses and all64 assignments; no solver used.')
print(best)
