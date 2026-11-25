from random import Random
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import json,time

class Model:
 def __init__(self,n,left,edges,name):
  self.n=n;self.left=left;self.edges=tuple(edges);self.name=name
  self.inputs=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
  self.f=0
  for a,b in edges:self.f|=self.inputs[a]&self.inputs[b]
  self.epos=[(1<<a)|(1<<b) for a,b in edges]
  self.all=(1<<len(edges))-1
  self.base=self.tau(self.all)
  self.adj={i:set() for i in range(n)}
  for a,b in edges:self.adj[a].add(b);self.adj[b].add(a)
  self.motifs=[(a,b,c,d) for a in range(n) for b,c in combinations(self.adj[a],2) for d in self.adj[b] if d!=a]+[(a,c,b,d) for a in range(n) for b,c in combinations(self.adj[a],2) for d in self.adj[c] if d!=a]
 @lru_cache(maxsize=200000)
 def tau(self,mask):
  adj={i:[] for i in range(self.left)}
  for k,(a,b) in enumerate(self.edges):
   if mask>>k&1:adj[a].append(b)
  matching={}
  def aug(a,seen):
   for b in adj[a]:
    if b in seen:continue
    seen.add(b)
    if b not in matching or aug(matching[b],seen):matching[b]=a;return True
   return False
  return sum(aug(a,set()) for a in adj)
 def analyze(self,g,compact=True):
  n=self.n;vals=list(self.inputs);singles=[1<<i for i in range(n)];pairs=[0]*n;anc=[0]*n;imp=[False]*n
  cores=[];accept=[]
  for j,(op,a,b) in enumerate(g):
   if op==0:
    v=vals[a]&vals[b];sin=0
    pair=0
    for k,(u,w) in enumerate(self.edges):
     if (singles[a]>>u&1 and singles[b]>>w&1) or (singles[a]>>w&1 and singles[b]>>u&1):pair|=1<<k
   else:v=vals[a]|vals[b];sin=singles[a]|singles[b];pair=pairs[a]|pairs[b]
   im=not(v&~self.f)
   ac=sum(1<<k for k,x in enumerate(self.epos) if v>>x&1)
   co=im and not(imp[a] and imp[b]) and bool(ac&~pair)
   vals.append(v);singles.append(sin);pairs.append(pair);imp.append(im);anc.append(anc[a]|anc[b]|(1<<j));accept.append(ac)
   if co:cores.append(j)
  maximal=[j for j in cores if not any(i!=j and anc[n+i]>>j&1 for i in cores)]
  D=0;U=0
  for j in maximal:D|=accept[j];U|=anc[n+j]
  if not maximal:return None
  target=U.bit_count()+len(maximal)+self.tau(self.all^D)-D.bit_count()-self.base
  stronger=U.bit_count()+len(maximal)-D.bit_count()-self.tau(D)
  if compact:
   mapping={i:i for i in range(n)};gg=[]
   for j,(op,a,b) in enumerate(g):
    if U>>j&1:mapping[n+j]=n+len(gg);gg.append((op,mapping[a],mapping[b]))
   g=gg
  return target,stronger,D,len(maximal),g

def canon(n,g):
 mapping={i:i for i in range(n)};h=[];cache={}
 for j,(op,a,b) in enumerate(g):
  a,b=sorted((mapping[a],mapping[b]));key=(op,a,b)
  if key not in cache:cache[key]=n+len(h);h.append(key)
  mapping[n+j]=cache[key]
 return h

def seeded(M,r):
 g=[];n=M.n
 for _ in range(r.randrange(1,7)):
  a,b,c,d=r.choice(M.motifs)
  k=n+len(g);g.extend([(0,d,b),(1,b,c),(1,a,k),(0,k+2,k+1)])
 return canon(n,g)

def mutate(M,g,r):
 g=list(g);n=M.n;typ=r.randrange(8)
 if typ<4 and g:
  j=r.randrange(len(g));op,a,b=g[j]
  if typ==0:op=1-op
  elif typ==1:a=r.randrange(n+j)
  elif typ==2:b=r.randrange(n+j)
  else:a,b=r.randrange(n+j),r.randrange(n+j)
  g[j]=(op,a,b)
 elif typ==4 and len(g)>1:
  j=r.randrange(len(g));old=n+j;replacement=r.choice(g[j][1:]);out=[]
  for k,(op,a,b) in enumerate(g):
   if k==j:continue
   def sub(i):return replacement if i==old else i-1 if i>old else i
   out.append((op,sub(a),sub(b)))
  g=out
 elif typ==5 and len(g)<60:
  j=r.randrange(len(g)+1);new=n+j;fresh=(r.randrange(2),r.randrange(new),r.randrange(new));out=[]
  for k,(op,a,b) in enumerate(g):
   if k==j:out.append(fresh)
   aa=a+1 if a>=new else a;bb=b+1 if b>=new else b
   if k>j and r.random()<.25:aa=new
   out.append((op,aa,bb))
  if j==len(g):out.append(fresh)
  g=out
 elif typ==6 and len(g)<55:
  for _ in range(r.randrange(1,4)):
   k=n+len(g);g.append((r.randrange(2),r.randrange(k),r.randrange(k)))
 else:
  a,b,c,d=r.choice(M.motifs);k=n+len(g);g.extend([(0,d,b),(1,b,c),(1,a,k),(0,k+2,k+1)])
 return canon(n,g)

r=Random(2962123);M=Model(14,7,[(p,7+l) for p in range(7) for l in range(7) if (p-l)%7 in (0,1,3)],'heawood')
start=time.time();count=0;minimum=100;examples={}
while time.time()-start<45:
 g=seeded(M,r)
 for _ in range(r.randrange(1,6)):g=mutate(M,g,r)
 ans=M.analyze(g);count+=1
 if ans is None:continue
 t,s,D,mc,g=ans
 leaves=set(a for op,a,b in g if a<M.n)|set(b for op,a,b in g if b<M.n)
 delta=len(g)-len(leaves)
 minimum=min(minimum,delta)
 if delta<0:
  print(json.dumps(dict(kind='FOUND',n=M.n,edges=M.edges,gates=g,leaves=sorted(leaves),ans=ans)),flush=True);break
print(json.dumps(dict(kind='done',count=count,seconds=time.time()-start,minimum=minimum)),flush=True)
