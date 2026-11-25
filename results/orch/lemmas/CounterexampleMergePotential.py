import argparse,itertools,signal,time,json
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=4);p.add_argument('--max-or',type=int,default=3);p.add_argument('--seconds',type=int,default=10);a=p.parse_args();n=a.n
pairs=list(itertools.combinations(range(n),2));ei={frozenset(e):i for i,e in enumerate(pairs)}
samples=[0]+[1<<i for i in range(n)]+[(1<<u)|(1<<v) for u,v in pairs]
xs=[sum(1<<j for j,x in enumerate(samples) if (x>>i)&1) for i in range(n)]
cycles=[]
for u,v,w,z in itertools.combinations(range(n),4):
 for es in [[(u,v),(v,w),(w,z),(z,u)],[(u,w),(w,v),(v,z),(z,u)],[(u,v),(v,z),(z,w),(w,u)]]:cycles.append(sum(1<<ei[frozenset(e)] for e in es))
graphs=[g for g in range(1<<len(pairs)) if all(c&g!=c for c in cycles)]
low=(1<<(n+1))-1

def proper_masks(S):return [f>>(n+1) for f in S if not f&low and (f>>(n+1)).bit_count()>1]
def merge(parts,f):
 out=[];u=0
 for c in parts:
  if c&f:u|=c
  else:out.append(c)
 if u:out.append(u)
 return tuple(out)
def components(G,fs):
 ps=tuple(1<<j for j in range(len(pairs)) if (G>>j)&1)
 for f in fs:
  if f&G==f:ps=merge(ps,f)
 return ps

initial={0};one=(1<<len(samples))-1
for mask in range(1<<n):
 f=one
 for i,x in enumerate(xs):
  if (mask>>i)&1:f&=x
 initial.add(f)
states={tuple(sorted(initial)):()};transitions=0;start=time.monotonic()
def alarm(sig,frame):raise TimeoutError
signal.signal(signal.SIGALRM,alarm);signal.alarm(a.seconds)
print(json.dumps({'n':n,'c4free_graphs':len(graphs),'max_or':a.max_or}),flush=True)
try:
 for k in range(1,a.max_or+1):
  nxt={}
  for S,hist in states.items():
   SS=set(S);oldfs=proper_masks(S);old={G:components(G,oldfs) for G in graphs}
   new={}
   for u,v in itertools.combinations(S,2):
    c=u|v
    if c not in SS:new.setdefault(c,(u,v))
   for c,uv in new.items():
    added={c&s for s in S}-SS;newfs=proper_masks(added);transitions+=1
    for G,parts in old.items():
     q=parts
     for f in newfs:
      if f&G==f:q=merge(q,f)
     if len(parts)-len(q)>1:
      print('COUNTEREXAMPLE',json.dumps({'G':G,'edges':[e for i,e in enumerate(pairs) if (G>>i)&1],'old_state':S,'old_history':hist,'new_or':uv,'old_components':parts,'new_components':q,'new_proper_masks':newfs,'or_step':k}),flush=True);raise SystemExit(0)
    if k<a.max_or:nxt.setdefault(tuple(sorted(SS|added)),hist+(uv,))
  print(json.dumps({'or_step':k,'states':len(states),'next_states':len(nxt),'transitions':transitions,'seconds':time.monotonic()-start}),flush=True);states=nxt
 print('NO_COUNTEREXAMPLE_WITHIN_BUDGET',a.max_or,flush=True)
except TimeoutError:print('TIMEOUT','transitions',transitions,'seconds',time.monotonic()-start,flush=True)
finally:signal.alarm(0)
