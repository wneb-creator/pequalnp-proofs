import argparse, json, random, time
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('model');ap.add_argument('--seconds',type=int,default=30);ap.add_argument('--seed',type=int,default=1);ap.add_argument('--out',required=True);a=ap.parse_args()
data=json.loads(Path(a.model).read_text());args=data['args'];p,l=args['p'],args['l'];n=p+l
edges=[tuple(map(int,e.split(','))) for e in args['edges'].split(';')]
inputs=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
target=sum(1<<x for x in range(1<<n) if any(x>>u&1 and x>>(p+v)&1 for u,v in edges))
positive=sum(1<<((1<<u)|(1<<(p+v))) for u,v in edges)
def trim(gates,out):
 live=set();pending=[out]
 while pending:
  w=pending.pop()
  if w<n or w in live:continue
  live.add(w);pending.extend(gates[w-n][1:])
 mapping={i:i for i in range(n)};new=[]
 for j,(op,u,v) in enumerate(gates):
  if n+j not in live:continue
  mapping[n+j]=n+len(new);new.append((op,mapping[u],mapping[v]))
 return new,mapping[out]
def check(gates,out):
 values=inputs.copy();cols=[1 if i<p else 2 for i in range(n)];cones=[{i} for i in range(n)];ands=[]
 for j,(op,u,v) in enumerate(gates):
  if op=='or':
   value=values[u]|values[v];col=cols[u]|cols[v];cone=cones[u]|cones[v]
   if col==3:return False
  else:
   value=values[u]&values[v];col=0;cone={n+j};ands.append(n+j)
   if not value&positive or value in inputs:return False
  values.append(value);cols.append(col);cones.append(cone)
 if values[out]!=target:return False
 dirty={w for w in ands if values[w]&~target}
 if len(dirty)<2:return False
 first=min(dirty)
 if args.get('nonstar_first'):
  _,fu,fv=gates[first-n]
  if {cols[fu],cols[fv]}!={1,2}:return False
 if args.get('lost_nonstar'):
  forced=values[:first]+[0]
  for op,u,v in gates[first-n+1:]:forced.append((forced[u]|forced[v]) if op=='or' else (forced[u]&forced[v]))
  lost=[(u,v) for u,v in edges if not(forced[out]>>((1<<u)|(1<<(p+v)))&1)]
  if not any(u!=s and v!=t for u,v in lost for s,t in lost):return False
 for w in ands:
  _,u,v=gates[w-n];readers=(cones[u]|cones[v])&set(ands)
  if any(r not in dirty for r in readers):return False
  if first in readers and w not in dirty:return False
 return True
gates=[(g['op'],g['left'],g['right']) for g in data['binary_gates']];out=data['binary_output'];gates,out=trim(gates,out);assert check(gates,out)
best=(gates.copy(),out);rng=random.Random(a.seed);start=time.monotonic();trials=0;accepted=0
while time.monotonic()-start<a.seconds:
 trials+=1
 if trials%5000==0:gates,out=best[0].copy(),best[1]
 j=rng.randrange(len(gates));op,u,v=gates[j];side=rng.randrange(2);new=rng.randrange(n+j)
 trial=gates.copy();trial[j]=(op,new,v) if side==0 else (op,u,new)
 trial,tout=trim(trial,out)
 if check(trial,tout):
  accepted+=1;gates,out=trial,tout
  if len(gates)<len(best[0]):
   best=(gates.copy(),out);print('IMPROVED',len(gates),'trials',trials,'seconds',time.monotonic()-start,flush=True)
gates,out=best
result={'args':args,'binary_gates':[{'wire':n+j,'op':op,'left':u,'right':v} for j,(op,u,v) in enumerate(gates)],'binary_output':out,'shared_binary_count':len(gates),'validated_assignments':1<<n,'topform':True,'first_dirty_has_no_clean_reader':True,'nonstar_loss_preserved':args.get('lost_nonstar',False),'trials':trials,'accepted':accepted,'seconds':time.monotonic()-start}
Path(a.out).write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
