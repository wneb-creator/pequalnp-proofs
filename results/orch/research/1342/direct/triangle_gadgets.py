import itertools, json, sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'counterexample'))
from common1342 import EDGES, N, target, audit
OUT=Path(__file__).resolve().parent
edges={frozenset(e) for e in EDGES}
triangles=[T for T in itertools.combinations(range(N),3) if all(frozenset(e) in edges for e in itertools.combinations(T,2))]
truth=sum(int(target(x))<<x for x in range(1<<N))
inputs=[sum(((x>>i)&1)<<x for x in range(1<<N)) for i in range(N)]

def mincover(es):
 for k in range(N+1):
  for S in itertools.combinations(range(N),k):
   if all(a in S or b in S for a,b in es):return S

def join(gs,vars,op='or'):
 out=vars[0]
 for v in vars[1:]:
  gs.append((op,out,v));out=N+len(gs)-1
 return out

def build(clauses,residual,cover):
 gs=[];cs=[]
 for C in clauses:cs.append(join(gs,C))
 h=join(gs,cs,'and')
 stars=[]
 for a in cover:
  ls=[v if u==a else u for u,v in residual if a in (u,v) and (u==a if u in cover else v==a)]
  if ls:
   v=join(gs,ls);gs.append(('and',a,v));stars.append(N+len(gs)-1)
 return gs,join(gs,[h]+stars)

records=[];best=None
for T in triangles:
 pendants=[(v,next(i for i,t in enumerate(T) if frozenset((v,t)) in edges))
           for v in range(N) if v not in T and sum(frozenset((v,t)) in edges for t in T)==1]
 for mask in range(1<<len(pendants)):
  clauses=[[T[j] for j in range(3) if j!=i] for i in range(3)]
  chosen=[pendants[k] for k in range(len(pendants)) if mask>>k&1]
  for v,i in chosen:clauses[i].append(v)
  ht=(1<<(1<<N))-1
  for C in clauses:
   ct=0
   for v in C:ct|=inputs[v]
   ht&=ct
  bad=ht&~truth
  accepted=[e for e in EDGES if (ht>>((1<<e[0])|(1<<e[1])))&1]
  residual=[e for e in EDGES if e not in accepted]
  cover=mincover(residual)
  gs,o=build(clauses,residual,cover)
  rec={'triangle':T,'pendants':chosen,'clauses':clauses,'accepted_edges':accepted,
       'false_positive_count':bad.bit_count(),'first_false_input':None if not bad else (bad&-bad).bit_length()-1,
       'residual_cover':cover,'size':len(gs)}
  records.append(rec)
  if not bad and (best is None or len(gs)<best['size']):best={**rec,'gates':gs,'output':o}
assert best is not None
check=audit(best['gates'],best['output'])
assert not check['false_positives'] and not check['false_negatives']
(OUT/'triangle-gadgets.json').write_text(json.dumps({'triangles':triangles,'records':records,'best':best,'audit':check},indent=2))
print('triangles',triangles,'patterns',len(records),'sound',sum(not r['false_positive_count'] for r in records))
print('best',json.dumps({k:v for k,v in best.items() if k not in ['gates']}))
print('audit',json.dumps(check))
