import random,time,json,sys
R=random.Random(296271)

def match(edges):
 adj={}
 for a,b in edges:adj.setdefault(a,[]).append(b)
 mt={}
 def go(a,seen):
  for b in adj.get(a,[]):
   if b in seen:continue
   seen.add(b)
   if b not in mt or go(mt[b],seen):mt[b]=a;return True
  return False
 return sum(go(a,set()) for a in adj)

def graph(p,q):
 es=set(); pairs=[(a,p+b) for a in range(p) for b in range(q)];R.shuffle(pairs)
 for a,b in pairs:
  if any((a,c) in es and (d,b) in es and (d,c) in es for d in range(p) if d!=a for c in range(p,p+q) if c!=b):continue
  if R.random()<.9:es.add((a,b))
 return sorted(es)

def paths(G):
 adj={}
 for a,b in G:adj.setdefault(a,set()).add(b);adj.setdefault(b,set()).add(a)
 return [(a,b,c,d) for b in adj for d in adj[b] for a in adj[b]-{d} for c in adj[a]-{b}]

def setup(n,G):
 tt=[sum(1<<m for m in range(1<<n) if m>>i&1) for i in range(n)]
 fg=0
 for a,b in G:fg |=tt[a]&tt[b]
 bad=((1<<(1<<n))-1)^fg
 ev=[sum(1<<j for j,e in enumerate(G) if i in e) for i in range(n)]
 tau=match(G)
 cache={}
 def eval(gs):
  ts=tt[:];vals=ev[:];si=[1<<i for i in range(n)];once=[0]*n;imp=[False]*n;cones=[0]*n;cores=0
  for j,(op,a,b) in enumerate(gs):
   t=(ts[a]|ts[b]) if op else (ts[a]&ts[b]);ts.append(t)
   v=(vals[a]|vals[b]) if op else (vals[a]&vals[b]);vals.append(v)
   s=si[a]|si[b] if op else 0;si.append(s)
   ro=once[a]|once[b] if op else sum(1<<k for k,(u,w) in enumerate(G) if ((si[a]>>u&1) and (si[b]>>w&1)) or ((si[a]>>w&1) and (si[b]>>u&1)))
   once.append(ro)
   ip=bool(t) and not(t&bad);imp.append(ip)
   cone=cones[a]|cones[b]|(1<<j);cones.append(cone)
   if ip and not(imp[a] and imp[b]) and v&~ro:cores|=1<<j
  maximal=cores
  for j in range(len(gs)):
   if cores>>j&1:maximal &=~(cones[n+j]^(1<<j))
  U=0;D=0
  for j in range(len(gs)):
   if maximal>>j&1:U|=cones[n+j];D|=vals[n+j]
  if not maximal:return (-999,0,0,0,0,0)
  if D not in cache:cache[D]=match([e for j,e in enumerate(G) if not(D>>j&1)])
  score=D.bit_count()+tau-U.bit_count()-maximal.bit_count()-cache[D]
  return score,D.bit_count(),U.bit_count(),maximal.bit_count(),D,maximal
 return eval

start=time.time();best=-999;steps=0
while time.time()-start<300:
 n=R.choice([6,7,8,9]);p=n//2;G=graph(p,n-p);pp=paths(G)
 if not pp:continue
 ev=setup(n,G)
 a,b,c,d=R.choice(pp)
 gs=[(0,d,b),(1,b,c),(1,a,n),(0,n+2,n+1)]
 base=ev(gs)
 for run in range(3):
  cur=gs[:];cs=base
  for k in range(3000):
   new=cur[:]
   typ=R.random()
   if typ<.08 and len(new)<24:
    j=len(new);new.append((R.randrange(2),R.randrange(n+j),R.randrange(n+j)))
   elif typ<.1 and len(new)>4:
    new.pop()
   else:
    j=R.randrange(len(new));op,x,y=new[j]
    which=R.randrange(3)
    if which==0:op^=1
    elif which==1:x=R.randrange(n+j)
    else:y=R.randrange(n+j)
    new[j]=(op,x,y)
   z=ev(new);steps+=1
   if z[0]>best:
    best=z[0];print(json.dumps(dict(best=best,score=z,n=n,G=G,gates=new,steps=steps,seconds=time.time()-start)),flush=True)
   if z[0]>0:sys.exit(0)
   if z[0]>cs[0] or (z[0]==cs[0] and (z[1]>=cs[1] or R.random()<.2)) or (z[0]>=cs[0]-2 and R.random()<.01):cur,cs=new,z
print(json.dumps(dict(done=True,best=best,steps=steps,seconds=time.time()-start)),flush=True)
