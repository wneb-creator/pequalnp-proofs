from itertools import permutations
import random,json,time

def valid(E):
    adj={v:set() for e in E for v in e}
    for u,v in E: adj[u].add(v);adj[v].add(u)
    for u in adj:
      for v in adj:
        if u<v and len(adj[u]&adj[v])>1:return False
    color={}
    for r in adj:
      if r in color:continue
      color[r]=0;todo=[r]
      while todo:
        u=todo.pop()
        for v in adj[u]:
          if v in color:
            if color[u]==color[v]:return False
          else:color[v]=1-color[u];todo.append(v)
    return True

def cover(E):
    vs=sorted({v for e in E for v in e})
    for mask in sorted(range(1<<len(vs)),key=int.bit_count):
      S={v for i,v in enumerate(vs) if mask>>i&1}
      if all(u in S or v in S for u,v in E):return len(S)

def check(paths):
    nodes=set();outs=set();E=set()
    def gate(op,a,b):
      z=(op,)+tuple(sorted((a,b),key=repr));nodes.add(z);return z
    for x,y,z,w in paths:
      a=gate('A',x,y);b=gate('O',a,z);c=gate('O',y,w);d=gate('A',b,c);outs.add(d)
      E.update(tuple(sorted(e)) for e in [(x,y),(y,z),(z,w)])
    if not valid(E):return None
    tau=cover(E);score=len(nodes)+len(outs)-len(E)-tau
    return {'paths':paths,'edges':sorted(E),'U':len(nodes),'MC':len(outs),'tau':tau,'slack':score}

start=time.monotonic();best={};counts={}; examples=[]
for p in permutations(range(8),4):
    # New vertices have canonical first-appearance names 4,5,6,7.
    new=[x for x in p if x>=4]
    if new!=list(range(4,4+len(new))):continue
    out=check([(0,1,2,3),p])
    if out:
      counts[2]=counts.get(2,0)+1
      if out['slack']<best.get(2,10**9):best[2]=out['slack'];examples.append(out)
random.seed(2962)
for k in range(3,9):
  counts[k]=0
  for trial in range(20000):
    n=random.randint(4,10)
    paths=[tuple(random.sample(range(n),4)) for _ in range(k)]
    out=check(paths)
    if out:
      counts[k]+=1
      if out['slack']<best.get(k,10**9):best[k]=out['slack'];examples.append(out)
print(json.dumps({'counts':counts,'min_slack':best,'elapsed':time.monotonic()-start,'record_minima':examples},indent=2))
