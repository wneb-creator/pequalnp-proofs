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

r=Random(2962007);models=[]
for k in [5,6,7]:models.append(Model(2*k,k,[(i,k+i) for i in range(k)]+[(i,k+(i+1)%k) for i in range(k)],'cycle'+str(2*k)))
models.append(Model(14,7,[(p,7+l) for p in range(7) for l in range(7) if (p-l)%7 in (0,1,3)],'heawood'))
for n in [10,12,14]:
 left=n//2;edges=[(0,left)]
 for x in range(1,left):edges.append((x,r.randrange(left,left+x)))
 for y in range(left+1,n):edges.append((r.randrange(y-left),y))
 models.append(Model(n,left,edges,'tree'+str(n)))
start=time.time();count=0;last=0;best={};archives={M.name:{} for M in models};active=0
while time.time()-start<900:
 M=models[active%len(models)];active+=1;archive=archives[M.name]
 for step in range(200):
  if not archive or r.random()<.12:g=seeded(M,r)
  else:g=mutate(M,r.choice(list(archive.values()))[-1],r)
  ans=M.analyze(g);count+=1
  if ans is None:continue
  t,s,D,mc,g=ans;key=(D,mc)
  score=(t,s,len(g))
  if key not in archive or score<(archive[key][0],archive[key][1],len(archive[key][-1])):archive[key]=ans
  if len(archive)>500:
   keys=sorted(archive,key=lambda k:(archive[k][0],archive[k][1],-archive[k][2].bit_count()+.2*len(archive[k][-1])))
   archive={k:archive[k] for k in keys[:300]};archives[M.name]=archive
  if M.name not in best or (t,s)<best[M.name]:
   best[M.name]=(t,s);out=dict(kind='best',seconds=time.time()-start,count=count,graph=M.name,n=M.n,edges=M.edges,target=t,stronger=s,D=D,mc=mc,gates=g);print(json.dumps(out),flush=True)
   Path('/tmp/oec/pequalnp-pilot-71/core-counterexample/guided-best-'+M.name+'.json').write_text(json.dumps(out,indent=2))
  if t<0 or s<0:
   print(json.dumps(dict(kind='FOUND',target=t,stronger=s)),flush=True)
   raise SystemExit
 now=time.time()-start
 if now-last>60:print(json.dumps(dict(kind='progress',seconds=now,count=count,best=best,archives={k:len(v) for k,v in archives.items()})),flush=True);last=now
print(json.dumps(dict(kind='done',seconds=time.time()-start,count=count,best=best)),flush=True)
