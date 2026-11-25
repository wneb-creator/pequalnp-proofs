import random, json, time
from itertools import combinations
R=random.Random(2962)

def matching(edges):
 adj={}
 for a,b in edges: adj.setdefault(a,[]).append(b)
 matched={}
 def dfs(a,seen):
  for b in adj.get(a,[]):
   if b in seen: continue
   seen.add(b)
   if b not in matched or dfs(matched[b],seen):
    matched[b]=a; return True
  return False
 return sum(dfs(a,set()) for a in adj)

def graph(p,q):
 edges=[]
 possible=[(a,p+b) for a in range(p) for b in range(q)]
 R.shuffle(possible)
 for a,b in possible:
  if any((a,c) in edges and (d,b) in edges and (d,c) in edges for d in range(p) if d!=a for c in range(p,p+q) if c!=b):continue
  if R.random()<0.75: edges.append((a,b))
 return set(edges)

def gadgets(G):
 adj={}
 for a,b in G:
  adj.setdefault(a,set()).add(b);adj.setdefault(b,set()).add(a)
 gs=[]
 for b in adj:
  for d in adj[b]:
   for a in adj[b]-{d}:
    for c in adj[a]-{b}:
     gs.append((a,b,c,d))
 return gs

def calc(gs):
 terms=set(); D=set(); roots=set()
 def op(k,a,b):
  t=(k,*sorted((a,b),key=repr));terms.add(t);return t
 for a,b,c,d in gs:
  a,b,c,d=map(lambda x:("v",x),(a,b,c,d))
  e=op("and",d,b);s=op("or",b,c);t=op("or",a,e);k=op("and",t,s)
  roots.add(k)
  for x,y in ((a,b),(a,c),(b,d)): D.add(tuple(sorted((x[1],y[1]))))
 return len(terms)+len(roots)-len(D)-matching(D),len(terms),len(roots),len(D),matching(D)

best=999;count=0;start=time.time()
for trial in range(30000):
 p=R.randrange(2,9);q=R.randrange(2,9);G=graph(p,q); gs=gadgets(G)
 if not gs:continue
 R.shuffle(gs)
 selected=[]
 for g in gs:
  cand=selected+[g]
  score=calc(cand)
  if not selected or score[0]<=calc(selected)[0] or R.random()<.08: selected=cand
  count+=1
  if score[0]<best:
   best=score[0]
   print(json.dumps(dict(trial=trial,count=count,best=best,score=score,selected=cand,seconds=time.time()-start)),flush=True)
  if score[0]<0: raise SystemExit(0)
print(json.dumps(dict(done=True,count=count,best=best,seconds=time.time()-start)),flush=True)
