"""Search ordered cones of shared gates with a fixed budget for excess fan-out occurrences."""
from pathlib import Path
import functools,itertools,ctypes,collections,time,sys,json,resource
import fresh_meta3773_k4_lowfan_fast as m
job=Path(__file__).resolve().parent;P=m.P;N=m.N;NP=m.NP;NT=m.NT;M=m.M;target=m.target;raw=m.raw;free=m.free;feasible=m.feasible;trees=m.trees
lib=m.shared;lib.splits.argtypes=[ctypes.c_int,ctypes.POINTER(ctypes.c_uint32),ctypes.c_int,ctypes.c_int,ctypes.POINTER(ctypes.c_uint64)];lib.splits.restype=ctypes.c_int
rowid={x:i for i,x in enumerate(m.rows)}; rpi=[]
for pi in m.perms:
 rpi.append(tuple(rowid[sum(1<<pi[i]for i in range(10) if row>>i&1)]for row in m.rows))
@functools.lru_cache(maxsize=15000)
def images(v):return tuple(sum(1<<pi[i]for i in range(NT)if v>>i&1)for pi in rpi)
@functools.lru_cache(maxsize=60000)
def canon(F):
 im=list(map(images,F));return min(tuple(sorted(y[j]for y in im))for j in range(24))
@functools.lru_cache(maxsize=4000)
def splits(F):
 n=len(F);a=(ctypes.c_uint32*n)(*F);o=(ctypes.c_uint64*(1<<n))();count=lib.splits(n,a,NP,NT-NP,o);assert count>=0;out=[];seen=set(); af=(1<<n)-1
 stab=[j for j in range(24)if sorted(images(x)[j]for x in F)==list(F)]
 for i in range(count):
  w=o[i];s=w&65535;t=af^s;si=tuple(x for j,x in enumerate(F)if s>>j&1);to=tuple(x for j,x in enumerate(F)if t>>j&1)
  if si in seen:continue
  for j in stab:seen.add(tuple(sorted(images(x)[j]for x in si)))
  out.append((si,to,(w>>16)&65535,(w>>32)<<NP))
 return tuple(out)
@functools.lru_cache(maxsize=240)
def forward(F,h):
 # Boolean functions of the given input tokens, with any unused occurrences of surplus budget.
 outs=set(trees(F));n=len(F)
 if h and n>=3:
  seen=set()
  for s in range(1,(1<<n)-1):
   if s.bit_count()<2:continue
   si=tuple(x for i,x in enumerate(F)if s>>i&1);to=tuple(x for i,x in enumerate(F)if not (s>>i&1));
   if si in seen:continue
   seen.add(si)
   for v in trees(si):
    for d in range(2,h+2):outs.update(forward(tuple(sorted((*to,*([v]*d)))),h-d+1))
 return frozenset(outs)
count=collections.Counter(); hits=[]
@functools.lru_cache(maxsize=48000)
def search(F,h):
 count['states']+=1
 if feasible(F,target,M^target):hits.append(('readonce',F,h));return True
 if h==0:return False
 for si,to,g1,g0 in splits(F):
  if len(si)<=len(to)+2 and len(si)<=6:
   for v in trees(si):
    if v&g0 or g1&~v:continue
    for d in range(2,h+2):
     if search(canon(tuple(sorted((*to,*([v]*d))))),h-d+1):hits.append(('forward-gate',F,h,si,to,v,d));return True
  else:
   # First try an over-approximation with an arbitrary monotone remainder on up to four features.
   sym=M<<NT;to2=tuple(x|(x<<NT)for x in to);keep=True
   if len(to)<=3:
    possibilities=set()
    for pair in m.monotone_outputs([*to2,sym]):
     l=pair&M;u=pair>>NT
     if not(target&~u or (M^target)&l):possibilities.add((target&~l,(M^target)&u))
    keep=any(feasible(si,a,b)for a,b in possibilities)
   if not keep:continue
   # If this relaxed test survives, enumerate the exact remainder with bounded sharing.
   for d in range(2,h+2):
    outer=tuple(sorted((*to2,*([sym]*d))))
    for pair in forward(outer,h-d+1):
     l=pair&M;u=pair>>NT
     if not(target&~u or (M^target)&l) and feasible(si,target&~l,(M^target)&u):hits.append(('reverse-cone',F,h,si,to,pair,d));return True
 return False

def run(k,dup):
 F=tuple((*raw,*free[:k]));ex=5-k;h=ex-dup;cases={canon(tuple(sorted((*F,*extra)))) for extra in itertools.combinations_with_replacement(F,dup)}; st=time.perf_counter();res=[]
 for t,f in enumerate(sorted(cases)):
  a=search(f,h);res.append(a);print('case',k,dup,t+1,'of',len(cases),'result',a,'states',count['states'],'seconds',round(time.perf_counter()-st,3),flush=True)
  if a:break
 return {'free_count':k,'repeated_primitive_count':dup,'internal_excess_budget':h,'cases':len(cases),'tested':len(res),'hits':hits,'states':count['states'],'seconds':time.perf_counter()-st}
if __name__=='__main__':
 k,dup=map(int,sys.argv[1:3]);result=run(k,dup);(job/f'fresh-meta3773-k4-rec-{k}-{dup}.json').write_text(json.dumps(result,indent=2)+'\n');print(result,flush=True)
