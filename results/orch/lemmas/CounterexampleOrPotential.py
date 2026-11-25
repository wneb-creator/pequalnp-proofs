import argparse,itertools,time,signal,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=4);p.add_argument('--max-or',type=int,default=2);p.add_argument('--seconds',type=int,default=60);p.add_argument('--relaxed',action='store_true');p.add_argument('--pair-signatures',action='store_true');a=p.parse_args()
n=a.n;pairs=list(itertools.combinations(range(n),2));edgeindex={frozenset(e):i for i,e in enumerate(pairs)}
samples=([0]+[1<<i for i in range(n)]+[(1<<u)|(1<<v) for u,v in pairs]) if a.pair_signatures else list(range(1<<n))
inputs=[sum(1<<j for j,x in enumerate(samples) if (x>>i)&1) for i in range(n)]
cycles=[]
for u,v,w,z in itertools.combinations(range(n),4):
 for es in [[(u,v),(v,w),(w,z),(z,u)],[(u,w),(w,v),(v,z),(z,u)],[(u,v),(v,z),(z,w),(w,u)]]:
  cycles.append(sum(1<<edgeindex[frozenset(e)] for e in es))

def rank4(mask):
 basis={}
 for c in cycles:
  if c&mask!=c:continue
  while c:
   j=c.bit_length()-1
   if j in basis:c^=basis[j]
   else:basis[j]=c;break
 return len(basis)

targets={};by_mask={}
for mask in range(1<<len(pairs)):
 f=0;edges=[]
 for i,(u,v) in enumerate(pairs):
  if (mask>>i)&1:f|=inputs[u]&inputs[v];edges.append((u,v))
 r=rank4(mask);targets[f]={'mask':mask,'edges':edges,'edge_count':len(edges),'four_cycle_rank':r,'bound':max(0,len(edges)-r-1)};by_mask[mask]=targets[f]
if a.relaxed and not a.pair_signatures:
 mono=[0,1]
 for arity in range(1,n+1):
  shift=1<<(arity-1)
  mono=[lo|(hi<<shift) for lo in mono for hi in mono if lo&hi==lo]
 proper=[f for f in mono if not (f&1) and all(not ((f>>(1<<i))&1) for i in range(n))]
 targets={}
 for f in proper:
  mask=sum(1<<i for i,(u,v) in enumerate(pairs) if (f>>((1<<u)|(1<<v)))&1)
  targets[f]=by_mask[mask]
allones=(1<<len(samples))-1
initial={0}
for mask in range(1<<n):
 f=allones
 for i,x in enumerate(inputs):
  if (mask>>i)&1:f&=x
 initial.add(f)
start=time.monotonic();states={tuple(sorted(initial)):()};checks=0;outcomes=[]
print(json.dumps({'n':n,'targets':len(targets),'relaxed':a.relaxed or a.pair_signatures,'pair_signatures':a.pair_signatures,'max_proposed_bound':max(t['bound'] for t in targets.values()),'initial_meet_functions':len(initial),'max_or':a.max_or}),flush=True)
def alarm(sig,frame):raise TimeoutError
signal.signal(signal.SIGALRM,alarm);signal.alarm(a.seconds)
try:
 for k in range(1,a.max_or+1):
  nxt={};seen_functions=set()
  for S,hist in states.items():
   SS=set(S);new={}
   for u,v in itertools.combinations(S,2):
    c=u|v
    if c not in SS:new.setdefault(c,(u,v))
   for c,uv in new.items():
    added={c&x for x in S}-SS;checks+=1
    seen_functions|=added
    for f in added:
     if f in targets and k<targets[f]['bound']:
      print('COUNTEREXAMPLE',json.dumps({'or_gates':k,'target':targets[f],'history':hist+(uv,),'truth_table':f}),flush=True)
      raise SystemExit(0)
    if k<a.max_or:
     SN=tuple(sorted(SS|added));nxt.setdefault(SN,hist+(uv,))
  row={'or_gates':k,'states_examined':len(states),'next_states':len(nxt),'new_functions':len(seen_functions),'transitions':checks,'seconds':time.monotonic()-start}
  outcomes.append(row);print(json.dumps(row),flush=True);states=nxt
 print('NO_COUNTEREXAMPLE_WITHIN_OR_BUDGET',a.max_or,flush=True)
except TimeoutError:
 print('TIMEOUT','seconds',time.monotonic()-start,'completed_levels',len(outcomes),'transitions',checks,flush=True)
finally:signal.alarm(0)
