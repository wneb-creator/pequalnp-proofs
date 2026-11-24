import importlib.util
import json
from pathlib import Path
import random
import time
HERE=Path('/tmp/oec/pequalnp-pilot-21/search')
spec=importlib.util.spec_from_file_location('graphstrong',HERE/'cegis-graph-five-strong.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
class CNF:
 def __init__(self):self.n=0;self.cs=[]
 def var(self):self.n+=1;return self.n
 def add(self,*xs):self.cs.append(tuple(xs))
def propagate(clauses, assumptions):
 values={abs(x):x>0 for x in assumptions};changed=True
 while changed:
  changed=False
  for clause in clauses:
   remaining=[];satisfied=False
   for x in clause:
    if abs(x) not in values:remaining.append(x)
    elif values[abs(x)]==(x>0):satisfied=True;break
   if satisfied:continue
   if not remaining:return None
   if len(remaining)==1:
    x=remaining[0];values[abs(x)]=x>0;changed=True
 return values
rng=random.Random(5331024);started=time.monotonic();cases=[]
meta=[None]*13+[(0,{0,1}),(0,{0,1,3})];goals=g.q.GOALS
for trial in range(40):
 gates=[]
 for j in range(14):
  a,b=sorted(rng.sample(range(len(meta)+j),2));gates.append((a,b,bool(rng.getrandbits(1)) if j<9 else False))
 if trial%2==0:
  points=sorted(g.q.s.LINES[goals[0]])
  gates[0]=(points[0],points[1],False);gates[1]=(points[2],points[3],False)
  gates[2]=(len(meta),len(meta)+1,False);gates[9]=(points[0],len(meta)+2,False)
 c=CNF();ops=[];aa=[];bb=[];assumptions=[]
 for j,(a,b,op) in enumerate(gates):
  flag=c.var();ops.append(flag);assumptions.append(flag if op else -flag)
  aa.append([c.var() for _ in range(len(meta)+j)]);bb.append([c.var() for _ in range(len(meta)+j)])
  assumptions += [v if k==a else -v for k,v in enumerate(aa[-1])]
  assumptions += [v if k==b else -v for k,v in enumerate(bb[-1])]
 g.all_five_nonordinary(c,ops,aa,bb,meta,goals)
 def eval_at(x):
  values=[bool(x>>p&1) for p in range(13)]
  values += [any(x>>p&1 for p in m[1]) for m in meta[13:]]
  for a,b,op in gates:values.append(values[a] and values[b] if op else values[a] or values[b])
  return values[-5:]
 exotic=[]
 for j,w in enumerate(goals):
  line=g.q.s.LINES[w];comp=8191^sum(1<<p for p in line)
  exotic.append(eval_at(comp)[j] or any(not eval_at(1<<p)[j] for p in line))
 model=propagate(c.cs,assumptions)
 assert (model is not None)==all(exotic)
 if model is not None:
  assert len(model)==c.n
  assert all(any(model[abs(x)]==(x>0) for x in clause) for clause in c.cs)
 cases.append({'trial':trial,'all_five_nonordinary':all(exotic),'rejected':model is None})
assert sum(x['rejected'] for x in cases)>=20
result={'status':'PASS','fixed_networks':len(cases),'rejected_networks':sum(x['rejected'] for x in cases),'accepted_networks':sum(not x['rejected'] for x in cases),'elapsed_seconds':time.monotonic()-started,'cases':cases}
(HERE/'graph-five-strong-test.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))
