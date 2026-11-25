from random import Random
from itertools import combinations
import json,time

def tau(edges):
    vs=set(sum(([a,b] for a,b in edges),[]))
    for k in range(len(vs)+1):
        for s in combinations(vs,k):
            ss=set(s)
            if all(a in ss or b in ss for a,b in edges):return k

def analyze(n,edges,gates):
    f=0
    for x in range(1<<n):
        if any(x>>a&1 and x>>b&1 for a,b in edges):f|=1<<x
    vals=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
    singles=[1<<i for i in range(n)]
    pairs=[0]*n
    ancestors=[0]*n
    imp=[False]*n
    core=[];accept=[]
    for j,(op,a,b) in enumerate(gates):
        if op==0:
            v=vals[a]&vals[b]
            sin=0
            pair=sum(1<<k for k,(u,w) in enumerate(edges) if (singles[a]>>u&1 and singles[b]>>w&1) or (singles[a]>>w&1 and singles[b]>>u&1))
        else:v=vals[a]|vals[b];sin=singles[a]|singles[b];pair=pairs[a]|pairs[b]
        im=bool(v) and not(v & ~f)
        ac=sum(1<<k for k,(u,w) in enumerate(edges) if v>>((1<<u)|(1<<w))&1)
        co=im and not(imp[a] and imp[b]) and bool(ac&~pair)
        vals.append(v);singles.append(sin);pairs.append(pair);imp.append(im)
        ancestors.append(ancestors[a]|ancestors[b]|(1<<j))
        if co:core.append(j)
        accept.append(ac)
    maximal=[j for j in core if not any(i!=j and ancestors[n+i]>>j&1 for i in core)]
    D=0;U=0
    for j in maximal:D|=accept[j];U|=ancestors[n+j]
    de=[e for k,e in enumerate(edges) if D>>k&1]
    rem=[e for k,e in enumerate(edges) if not(D>>k&1)]
    stronger=U.bit_count()+len(maximal)-len(de)-tau(de)
    target=U.bit_count()+len(maximal)+tau(rem)-len(de)-tau(edges)
    return target,stronger,maximal,U,D

if __name__=='__main__':
 r=Random(2962);start=time.time();best=100;count=0
 graphs=[]
 for n in [4,5,6,7,8]:
  a=n//2
  potential=list((u,v) for u in range(a) for v in range(a,n))
  for z in range(10):
   e=[]
   for uv in r.sample(potential,len(potential)):
    if r.random()<.5 and not any(len(set(v for u,v in e if u==x)&set(v for u,v in e if u==y))>1 for x,y in combinations(range(a),2)):
     e.append(uv)
     if any(len(set(v for u,v in e if u==x)&set(v for u,v in e if u==y))>1 for x,y in combinations(range(a),2)):e.pop()
   graphs.append((n,e))
 while time.time()-start<240:
  n,edges=r.choice(graphs);g=[]
  for j in range(r.randint(8,35)):
   if r.random()<.3 and edges:
    a,b=r.choice(edges)
   else:
    a=r.randrange(n+j);b=r.randrange(n+j)
   op=0 if r.random()<.55 else 1
   g.append((op,a,b))
  ans=analyze(n,edges,g);count+=1
  if ans[2] and min(ans[:2])<best:
   best=min(ans[:2]);print(json.dumps(dict(count=count,n=n,edges=edges,gates=g,ans=ans,best=best)),flush=True)
  if min(ans[:2])<0:
   print('COUNTEREXAMPLE',flush=True);break
 print(json.dumps(dict(total=count,seconds=time.time()-start,best=best)),flush=True)
