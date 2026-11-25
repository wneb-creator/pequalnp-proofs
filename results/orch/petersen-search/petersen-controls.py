from pathlib import Path
from itertools import combinations
import json
base=Path('/tmp/oec/pequalnp-pilot-152/gap-1884')
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def normalize(desc,output):
 mapping={i:i for i in range(11)};todo=set(range(len(desc)));ordered=[]
 while todo:
  ready=[]
  for i in todo:
   op,a,b=desc[i]
   if a in mapping and b in mapping:
    aa,bb=sorted([mapping[a],mapping[b]]);ready.append((({'or':0,'and':1,'not':2}[op],aa,bb),i,op,aa,bb))
  _,i,op,a,b=min(ready);mapping[11+i]=11+len(ordered);ordered.append([op,a,b]);todo.remove(i)
 assert mapping[output]==10+len(ordered)
 return ordered,mapping[output]
def verify(label,desc,out):
 desc,out=normalize(desc,out)
 fs=[sum(1<<x for x in range(1024) if x>>i&1) for i in range(10)]+[sum(1<<x for x in range(1024) if not x&1)]
 for op,a,b in desc:fs.append(fs[a]|fs[b] if op=='or' else fs[a]&fs[b] if op=='and' else fs[a]^((1<<1024)-1))
 target=sum(1<<x for x in range(1024) if any(x>>a&1 and x>>b&1 for a,b in edges))
 assert fs[out]==target
 raw=[(i,op) for i,(op,a,b) in enumerate(desc) if a==0 or b==0]
 neg=[(i,op) for i,(op,a,b) in enumerate(desc) if a==10 or b==10]
 print(label,'gates',len(desc),'raw_readers',raw,'aux_readers',neg,'FULL_TRUTH_TABLE_VERIFIED')
 data=dict(inputs=11,free_unary='not',gates=desc,output=out,edges=edges)
 (base/(label+'.json')).write_text(json.dumps(data,indent=2))
 return data
for order in ['rawfirst','negfirst']:
 desc=[]
 def add(op,a,b):desc.append([op,a,b]);return 10+len(desc)
 residual=[e for e in edges if 0 not in e]
 cover=next(S for S in combinations(range(1,10),5) if all(a in S or b in S for a,b in residual))
 pending=set(residual);terms=[]
 for v in cover:
  es=[e for e in sorted(pending) if v in e]
  if not es:continue
  ns=[b if a==v else a for a,b in es];pending.difference_update(es);z=ns[0]
  for w in ns[1:]:z=add('or',z,w)
  terms.append(add('and',v,z))
 A=terms[0]
 for w in terms[1:]:A=add('or',A,w)
 assert len(desc)==16
 N=add('or',add('or',1,4),5)
 B=add('or',N,A)
 if order=='rawfirst':
  raw=add('or',0,A);neg=add('and',10,A);H=add('or',raw,neg)
 else:
  neg=add('and',10,A);H=add('or',A,neg);H=add('or',0,H)
 out=add('and',H,B)
 verify('petersen-both010-'+order+'-control23',desc,out)
model=json.loads((base/'petersen-ao-size20-canonical-model.json').read_text())
desc=[['not',10,10]]
def shift(w):return 11 if w==0 else w+1 if w>=11 else w
for op,a,b in model['gates']:desc.append([op,shift(a),shift(b)])
verify('petersen-only10-control21',desc,model['output']+1)
