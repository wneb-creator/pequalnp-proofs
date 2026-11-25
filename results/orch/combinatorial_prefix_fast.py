from itertools import combinations
from functools import reduce
from operator import or_
from collections import Counter
import json,time
N=10; M=(1<<(1<<N))-1
X=[sum(1<<a for a in range(1<<N) if a>>i&1) for i in range(N)]
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
T=0
for a,b in E:T|=X[a]&X[b]
ZERO=[a for a in range(1<<N) if not (T>>a&1)]
CUTS=json.loads(open("/tmp/oec/pequalnp-pilot-104/certificates/zero-cuts.json").read())
D=[]
for cut in CUTS:
 d=M
 for i in cut["removed"]: d &= M^X[i]
 D.append(d)
LB=[c["lower"] for c in CUTS]
for cut in json.loads(open("/tmp/oec/pequalnp-pilot-104/certificates/cycle-mixed-cuts.json").read()):
 d=M
 for i in cut["zero"]:d &= M^X[i]
 for i in cut["one"]:d &= X[i]
 D.append(d);LB.append(cut["lower"])
BASE=[{x&d for x in X}|{(M^x)&d for x in X}|{0,d} for d in D]
def bins(a,b):return [a&b,a|b,a&(M^b),(M^a)&b]
def separates(ws):
 for r in ZERO:
  hit=T
  for w in ws:
   hit &= w if (w>>r)&1 else M^w
   if not hit:break
  if hit:return False
 return True
def prefix_banks(prefix):
 banks=[]
 for i,d in enumerate(D):
  bank={t:0 for t in BASE[i]}
  for j,(a,b,z) in enumerate(prefix):
   t=z&d
   deps=bank[a&d]|bank[b&d]|(1<<j)
   if t not in bank or deps.bit_count()<bank[t].bit_count():
    bank[t]=deps;bank[d^t]=deps
  banks.append(bank)
 return banks

def restricted_fast(info,a,b,z,j,k,ka,kb):
 for d,lb,bank,restUsed,restConst,da,db,ca,cb in info:
  t=z&d
  deps=bank.get(t)
  if deps is None:deps=da|db|(1<<j)
  used=restUsed|deps|(da if ka else 0)|(db if kb else 0)
  const=restConst+(t in (0,d))+ka*ca+kb*cb
  if k+used.bit_count()<lb+const:return True
 return False

def expand(ws,prefix,k):
 stats=Counter();out={};banks=prefix_banks(prefix)
 reads=Counter(w for a,b,z in prefix for w in {a,b} if w in X)
 projection=[[(bank[w&d],int((w&d) in (0,d))) for w in ws] for d,bank in zip(D,banks)]
 for ai,bi in combinations(range(len(ws)),2):
  a,b=ws[ai],ws[bi]
  if reads[a]>=2 or reads[b]>=2:continue
  info=[]
  for i,(d,bank,pj) in enumerate(zip(D,banks,projection)):
   restUsed=reduce(or_,(dep for q,(dep,_) in enumerate(pj) if q!=ai and q!=bi),0)
   restConst=sum(c for q,(_,c) in enumerate(pj) if q!=ai and q!=bi)
   info.append((d,LB[i],bank,restUsed,restConst,pj[ai][0],pj[bi][0],pj[ai][1],pj[bi][1]))
  for gateop,z in enumerate(bins(a,b)):
   if gateop==0 and (a in FIRST or b in FIRST):continue
   if gateop==2 and a in FIRST:continue
   if gateop==3 and b in FIRST:continue
   if z in ws or z in (0,M):continue
   rest=tuple(w for w in ws if w!=a and w!=b)
   for ka,kb in [(0,0),(0,1),(1,0),(1,1)]:
    state=tuple(sorted(rest+(a,)*ka+(b,)*kb+(z,)))
    stats['children']+=1
    if len(state)>k+1:stats['length']+=1;continue
    cut=restricted_fast(info,a,b,z,len(prefix),k,ka,kb)
    if cut:stats['restriction']+=1;continue
    if not separates(state):stats['separation']+=1;continue
    if state not in out:out[state]=prefix+((a,b,z),)
 stats['open_unique']=len(out)
 return stats,out

AUTOS=json.loads(open('/workspace/pequalnp-proofs/results/orch/few_nots_automorphisms.json').read())
def swaplist(p):
 cur=list(range(N));ops=[]
 for i in range(N):
  if cur[i]!=p[i]:
   a,b=sorted((cur[i],p[i]));d=(1<<b)-(1<<a)
   ma=X[a]&(M^X[b]);mb=X[b]&(M^X[a]);keep=M^(ma|mb)
   ops.append((d,ma,mb,keep))
   cur=[b if j==a else a if j==b else j for j in cur]
 return ops
def transformed(w,ops):
 for d,ma,mb,keep in ops:w=((w&ma)<<d)|((w&mb)>>d)|(w&keep)
 return w
start=time.time()
for pair in [(0,1),(0,2)]:
 FIRST={X[pair[0]],X[pair[1]]}
 auto=[p for p in AUTOS if {p[pair[0]],p[pair[1]]}==set(pair)]
 ops=[swaplist(p) for p in auto]
 for p,o in zip(auto,ops):
  assert transformed(T,o)==T
  assert all(transformed(x,o)==X[p[i]] for i,x in enumerate(X))
 trcache={}
 def canon(ws,prefix):
  for w in ws+tuple(t for gate in prefix for t in gate):
   if w not in trcache:trcache[w]=tuple(transformed(w,o) for o in ops)
  best=min(range(len(ops)),key=lambda j:tuple(sorted(trcache[w][j] for w in ws)))
  return tuple(sorted(trcache[w][best] for w in ws)),tuple(tuple(trcache[w][best] for w in gate) for gate in prefix)
 z=X[pair[0]]|X[pair[1]]
 current={tuple(sorted(X+[z])):((X[pair[0]],X[pair[1]],z),)}
 for depth in range(2,8):
  total=Counter();nxt={};processed=0
  for ws,prefix in current.items():
   st,out=expand(ws,prefix,17-depth);total+=st;processed+=1
   for w,p in out.items():
    key,pr=canon(w,p);nxt.setdefault(key,pr)
   if len(nxt)>100000 or time.time()-start>360:break
  open('/tmp/oec/pequalnp-pilot-104/certificates/fast-%s-%s-depth%s.json' % (*pair,depth),'w').write(json.dumps([[list(w),list(p)] for w,p in nxt.items()]))
  total.update({'states':len(nxt),'depth':depth,'cap':17,'parents_processed':processed,'parents_total':len(current),'stabilizer':len(auto)})
  print(json.dumps({'pair':pair,**dict(total)}),flush=True)
  current=nxt
  if len(current)>100000 or time.time()-start>360:break
print(json.dumps({'elapsed_seconds':time.time()-start}),flush=True)
