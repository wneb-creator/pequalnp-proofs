import argparse,ast,re,time,json,itertools
from functools import lru_cache
from pathlib import Path
P=argparse.ArgumentParser()
P.add_argument('--budget',type=int,default=18)
P.add_argument('--seconds',type=float,default=300)
P.add_argument('--first',choices=['all','andedge','oredge','subedge','andnonedge','ornonedge','subnonedge'],default='all')
P.add_argument('--output',type=Path,required=True)
P.add_argument('--symdepth',type=int,default=0)
P.add_argument('--source',type=Path,default=Path('/workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_8367.lean'))
a=P.parse_args()
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
AD=[set() for _ in range(10)]
for u,v in E:AD[u].add(v);AD[v].add(u)
def graph(mask):
 V=[i for i in range(10) if mask>>i&1 and any(mask>>j&1 for j in AD[i])]
 return tuple(sum(1<<k for k,j in enumerate(V) if j in AD[i]) for i in V)
def signature(G):return (len(G),tuple(sorted(x.bit_count() for x in G)))
def iso(G,H):
 if signature(G)!=signature(H):return False
 n=len(G);order=sorted(range(n),key=lambda i:-G[i].bit_count());mapped=[-1]*n
 def go(k,used):
  if k==n:return True
  x=order[k]
  for y in range(n):
   if used>>y&1 or G[x].bit_count()!=H[y].bit_count():continue
   if any(((G[x]>>order[j])&1)!=((H[y]>>mapped[j])&1) for j in range(k)):continue
   mapped[k]=y
   if go(k+1,used|1<<y):return True
  return False
 return go(0,0)
classes={}
for line in a.source.read_text().splitlines():
 match=re.match(r'def known(\d+) := extendKnown (?:\[\]|known\d+) (\d+) (\[.*\])$',line)
 if not match:continue
 name,bound,ls=match.groups();bound=int(bound)
 for mask,swaps in ast.literal_eval(ls):
  if mask>=512:continue
  G=graph(mask);key=signature(G)
  candidates=classes.setdefault(key,[])
  for item in candidates:
   if iso(G,item[0]):item[1]=max(item[1],bound);break
  else:candidates.append([G,bound])
 if name=='383':break
@lru_cache(None)
def lower(mask):
 G=graph(mask)
 if len(G)==9:return 15
 best=max(0,len(G)-1)
 for H,L in classes.get(signature(G),[]):
  if iso(G,H):best=max(best,L)
 return best
full=(1<<1024)-1
raw=[sum(((r>>i)&1)<<r for r in range(1024)) for i in range(10)]
def target(r):return any((r>>u)&(r>>v)&1 for u,v in E)
T=sum(target(r)<<r for r in range(1024))
pairs=[(r|(1<<i),r) for r in range(1024) if not target(r) for i in range(10) if not (r>>i)&1 and target(r|(1<<i))]
sepfull=(1<<len(pairs))-1
signal={w:(sum(((r>>i)&1)<<j for j,(r,s) in enumerate(pairs)),sum(((s>>i)&1)<<j for j,(r,s) in enumerate(pairs))) for i,w in enumerate(raw)}
signal[T]=(sepfull,0)
def automorphisms():
 out=[];image=[-1]*10
 def go(k,used):
  if k==10:out.append(tuple(image));return
  un=[x for x in range(10) if image[x]<0]
  x=max(un,key=lambda x:sum(image[z]>=0 for z in AD[x]))
  for y in range(10):
   if used>>y&1:continue
   if any((z in AD[x])!=(image[z] in AD[y]) for z in range(10) if image[z]>=0):continue
   image[x]=y;go(k+1,used|1<<y);image[x]=-1
 go(0,0)
 return out
swaps={}
for i in range(10):
 for j in range(i+1,10):
  swaps[i,j]=(sum(1<<r for r in range(1024) if (r>>i)&1 and not (r>>j)&1),(1<<j)-(1<<i))
autos=[]
for p in automorphisms():
 cur=list(range(10));steps=[]
 for i in range(10):
  j=cur.index(p[i])
  if i!=j:
   steps.append(swaps[min(i,j),max(i,j)]);cur[i],cur[j]=cur[j],cur[i]
 autos.append(steps)
def transform(w,steps):
 for mask,d in steps:
  t=(w^(w>>d))&mask;w^=t^(t<<d)
 return w
assert len(autos)==120 and all(transform(T,p)==T for p in autos)
@lru_cache(maxsize=3000)
def pivotimages(w):return tuple(transform(w,p) for p in autos)
def canonical(S):
 pivot=min(S,key=lambda w:(w.bit_count(),w));images=pivotimages(pivot);least=min(images)
 return min(tuple(sorted(transform(w,autos[i]) for w in S)) for i,z in enumerate(images) if z==least)
domains=[]
for zsize in [1,2]:
 for zs in itertools.combinations(range(10),zsize):
  z=sum(1<<i for i in zs);mask=full
  for i in zs:mask&=full^raw[i]
  domains.append((mask,lower(1023^z),'zero'+str(zs)))
for i in range(10):
 linear=sum(1<<j for j in AD[i]);remaining=1023^(1<<i)^linear
 domains.append((raw[i],lower(remaining)+len(AD[i]),'one'+str(i)))
domains.sort(key=lambda d:-d[1])
D=len(domains)
print(json.dumps({'domain_bounds':[(L,label) for _,L,label in domains]}),flush=True)
@lru_cache(maxsize=20000)
def restrict(w):
 out=[]
 for mask,L,label in domains:
  q=w&mask;out.append(min(q,mask^q))
 return tuple(out)
banks=[{q for w in raw if (q:=restrict(w)[i])} for i in range(D)]
paid=[0]*D
memo=set();nodes=0;cuts=0;covcuts=0;maxdepth=0;witness=None;bydepth=[0]*(a.budget+1);last_report=time.monotonic();start=last_report
class Limit(Exception):pass
def search(k,S,mass,path):
 global nodes,cuts,covcuts,maxdepth,witness,last_report
 nodes+=1;depth=a.budget-k;maxdepth=max(maxdepth,depth);bydepth[depth]+=1
 now=time.monotonic()
 if nodes%512==0:
  if now-start>a.seconds:raise Limit
  if now-last_report>30:
   print(json.dumps({'progress_seconds':now-start,'nodes':nodes,'cuts':cuts,'memo':len(memo),'depth':depth}),flush=True);last_report=now
 if T in S:witness=path;return True
 if not k or len(S)>k+1:return False
 key=(k,canonical(S) if depth<=a.symdepth else S)
 if key in memo:return False
 for i,(_,L,_) in enumerate(domains):
  if k+paid[i]<L+mass[i]:cuts+=1;return False
 cov=0
 for x in S:
  p,n=signal[x];cov|=p^n
 if cov!=sepfull:covcuts+=1;return False
 for ix,x in enumerate(S):
  px,nx=signal[x]
  for jx in range(ix+1,len(S)):
   y=S[jx];py,ny=signal[y];rest=S[:ix]+S[ix+1:jx]+S[jx+1:]
   candidates=[(x&y,px&py,nx&ny,'and'),(x|y,px|py,nx|ny,'or'),(x&~y,px&~py,nx&~ny,'sub'),(y&~x,py&~px,ny&~nx,'rsub')]
   for g,pg,ng,op in candidates:
    if g==0 or g in S:continue
    old_signal=signal.get(g)
    signal[g]=(pg,ng);qg=restrict(g);qx=restrict(x);qy=restrict(y)
    added=[]
    for d,q in enumerate(qg):
     if q and q not in banks[d]:banks[d].add(q);paid[d]+=1;added.append(d)
    for keepx,keepy in [(False,False),(True,False),(False,True),(True,True)]:
     if len(rest)+1+keepx+keepy>k:continue
     U=tuple(sorted(rest+(g,)+((x,) if keepx else ()) +((y,) if keepy else ())))
     nm=tuple(mass[d]-(not keepx and qx[d]==0)-(not keepy and qy[d]==0)+(qg[d]==0) for d in range(D))
     if search(k-1,U,nm,path+[(op,x,y,g,keepx,keepy)]):return True
    for d in added:banks[d].remove(qg[d]);paid[d]-=1
    if old_signal is None:signal.pop(g,None)
    else:signal[g]=old_signal
 if len(memo)<50000:memo.add(key)
 return False
S=tuple(sorted(raw));mass=tuple(sum(restrict(w)[d]==0 for w in S) for d in range(D));status='unknown'
try:
 if a.first=='all':status='sat' if search(a.budget,S,mass,[]) else 'unsat'
 else:
  i,j=(0,2) if 'nonedge' in a.first else (0,1);x,y=raw[i],raw[j]
  px,nx=signal[x];py,ny=signal[y]
  if a.first.startswith('and'):g,pg,ng=x&y,px&py,nx&ny
  elif a.first.startswith('or'):g,pg,ng=x|y,px|py,nx|ny
  else:g,pg,ng=x&~y,px&~py,nx&~ny
  signal[g]=(pg,ng);qg=restrict(g)
  for d,q in enumerate(qg):
   if q and q not in banks[d]:banks[d].add(q);paid[d]+=1
  status='unsat'
  for keepx,keepy in [(False,False),(True,False),(False,True),(True,True)]:
   rest=tuple(w for w in S if w not in (x,y));U=tuple(sorted(rest+(g,)+((x,) if keepx else ()) +((y,) if keepy else ())))
   nm=tuple(sum(restrict(w)[d]==0 for w in U) for d in range(D))
   if search(a.budget-1,U,nm,[(a.first,x,y,g,keepx,keepy)]):status='sat';break
except Limit:status='timeout'
r={'status':status,'budget':a.budget,'first':a.first,'seconds':time.monotonic()-start,'nodes':nodes,'memo':len(memo),'restriction_cuts':cuts,'coverage_cuts':covcuts,'maxdepth':maxdepth,'bydepth':bydepth,'domains':[(L,label) for _,L,label in domains],'restrict_cache':str(restrict.cache_info())}
if witness:r['witness']=witness
print(json.dumps({k:v for k,v in r.items() if k not in ('witness','domains')}),flush=True)
a.output.write_text(json.dumps(r))
