import argparse,time,json
from functools import lru_cache
from pathlib import Path
P=argparse.ArgumentParser()
P.add_argument('--budget',type=int,default=19)
P.add_argument('--nots',type=int,default=1)
P.add_argument('--seconds',type=float,default=30)
P.add_argument('--output',type=Path,required=True)
args=P.parse_args()
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x): return any((x>>a)&(x>>b)&1 for a,b in E)
pairs=[(x|(1<<i),x) for x in range(1024) if not target(x) for i in range(10) if not (x>>i)&1 and target(x|(1<<i))]
M=(1<<len(pairs))-1
raw=tuple(sorted((sum(((a>>i)&1)<<j for j,(a,b) in enumerate(pairs)),sum(((b>>i)&1)<<j for j,(a,b) in enumerate(pairs))) for i in range(10)))
T=(M,0)
start=time.monotonic(); count=0; maximum=0; misses=0; gates=[0]*20; memo=set(); witness=None
class TimeLimit(Exception): pass
def sep(a,t): return a[0]^a[1] if t else a[0]&~a[1]
def search(k,t,S,path):
 global count,maximum,misses,witness
 count+=1; maximum=max(maximum,args.budget-k);gates[args.budget-k]+=1
 if count%1024==0 and time.monotonic()-start>args.seconds:raise TimeLimit
 if T in S:witness=path;return True
 if not k or t>k or len(S)>k-t+1:return False
 key=(k,t,S)
 if key in memo:return False
 C=[sep(a,t) for a in S]
 pref=[0]
 for z in C:pref.append(pref[-1]|z)
 if pref[-1]!=M:return False
 def use(g,rem,keep,nt,label):
  if g in S or g in [(0,0),(M,M)]:return False
  U=tuple(sorted(rem+keep+(g,)))
  if len(U)>k-nt:return False
  cov=sep(g,nt)
  for a in rem+keep:cov|=sep(a,nt)
  if cov!=M:return False
  return search(k-1,nt,U,path+[label])
 if t:
  for i,a in enumerate(S):
   g=(M^a[0],M^a[1]);rem=S[:i]+S[i+1:]
   for keep in [(),(a,)]:
    if use(g,rem,keep,t-1,('not',a,g,bool(keep))):return True
 for i,a in enumerate(S):
  for j in range(i+1,len(S)):
   b=S[j];rem=S[:i]+S[i+1:j]+S[j+1:]
   for op,g in [('and',(a[0]&b[0],a[1]&b[1])),('or',(a[0]|b[0],a[1]|b[1]))]:
    for keep in [(),(a,),(b,),(a,b)]:
     if use(g,rem,keep,t,(op,a,b,g,len(keep))):return True
 if len(memo)<100000:memo.add(key)
 return False
status='unknown'
try: status='sat_samples' if search(args.budget,args.nots,raw,[]) else 'unsat_samples'
except TimeLimit:status='timeout'
r={'status':status,'budget':args.budget,'nots':args.nots,'seconds':time.monotonic()-start,'nodes':count,'memo':len(memo),'maxdepth':maximum,'bydepth':gates,'pair_count':len(pairs),'sample_row_count':len(set(x for a in pairs for x in a))}
if witness:r['witness']=witness
args.output.write_text(json.dumps(r))
print(json.dumps({k:v for k,v in r.items() if k!='witness'}),flush=True)
