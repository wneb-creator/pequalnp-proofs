import argparse,json
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('candidate')
p.add_argument('output')
a=p.parse_args()
lines=Path(a.candidate).read_text().splitlines()
assert lines[0].startswith('score ') and lines[1].startswith('output ')
claimed_score=int(lines[0].split()[1]);out=int(lines[1].split()[1])
gates=[tuple(map(int,line.split())) for line in lines[2:]]
assert len(gates)==17 and 0<=out<27
for i,(op,u,v) in enumerate(gates):
 assert op in range(5)
 if op<3:assert 0<=u<10+i
 if op<2:assert 0<=v<10+i
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def apply(w,op,u,v):
 if op==0:return w[u] and w[v]
 if op==1:return w[u] or w[v]
 if op==2:return not w[u]
 return op==4
care_errors=[];full_errors=[]
for x in range(1024):
 raw=[bool(x>>i&1) for i in range(10)]
 target=any(raw[u] and raw[v] for u,v in edges)
 w=raw[:]
 for op,u,v in gates:w.append(apply(w,op,u,v))
 if x&3!=3 and w[out]!=target:care_errors.append(x)
 result=w[out] or (raw[0] and raw[1])
 if result!=target:full_errors.append(x)
mp=lambda w:w if w<10 else w+1
lift=[]
for op,u,v in gates:
 if op<2:lift.append({'op':'and' if op==0 else 'or','inputs':[mp(u),mp(v)]})
 elif op==2:lift.append({'op':'not','inputs':[mp(u)]})
 else:lift.append({'op':'and' if op==4 else 'or','inputs':[]})
lift.append({'op':'or','inputs':[10,mp(out)]})
# Independently replay the lifted 11-input circuit, including zero-arity gates.
lift_errors=[]
for x in range(1024):
 w=[bool(x>>i&1) for i in range(10)]
 target=any(w[u] and w[v] for u,v in edges);w.append(w[0] and w[1])
 for g in lift:
  values=[w[i] for i in g['inputs']]
  w.append(all(values) if g['op']=='and' else any(values) if g['op']=='or' else not values[0])
 if w[-1]!=target:lift_errors.append(x)
assert full_errors==care_errors==lift_errors
result={'claimed_score':claimed_score,'care_rows':768,'all_rows':1024,'care_errors':care_errors,'full_errors':full_errors,'counterexample':not full_errors,'chooseAnd':True,'pinmap':list(range(10)),'size':18,'not_count':sum(g['op']=='not' for g in lift),'output':28,'gates':lift}
Path(a.output).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='gates'}))
raise SystemExit(0 if not full_errors else 1)
