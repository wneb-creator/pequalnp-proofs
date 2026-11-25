"""Search ordered cones of shared gates with a fixed budget for excess fan-out occurrences."""
from pathlib import Path
import functools,itertools,ctypes,collections,time,sys,json,resource
import fresh_meta3773_extended_model as m
job=Path(__file__).resolve().parent;P=m.P;N=m.N;NP=m.NP;NT=m.NT;M=m.M;target=m.target;raw=m.raw;free=m.free;feasible=m.feasible;trees=m.trees
lib=m.shared;lib.splits.argtypes=[ctypes.c_int,ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.c_int,ctypes.POINTER(ctypes.c_uint32)];lib.splits.restype=ctypes.c_int
rowid={x:i for i,x in enumerate(m.rows)}; rpi=[]
for pi in m.perms:
 rpi.append(tuple(rowid[sum(1<<pi[i]for i in range(m.raw_count) if row>>i&1)]for row in m.rows))
@functools.lru_cache(maxsize=15000)
def images(v):return tuple(sum(1<<pi[i]for i in range(NT)if v>>i&1)for pi in rpi)
@functools.lru_cache(maxsize=60000)
def canon(F):
 im=list(map(images,F));return min(tuple(sorted(y[j]for y in im))for j in range(len(rpi)))
@functools.lru_cache(maxsize=4000)
def splits(F):
 n=len(F);a=(ctypes.c_uint64*n)(*F);o=(ctypes.c_uint32*(3<<n))();count=lib.splits(n,a,NP,NT-NP,o);assert count>=0;out=[];seen=set(); af=(1<<n)-1
 stab=[j for j in range(len(rpi))if sorted(images(x)[j]for x in F)==list(F)]
 for i in range(count):
  s=o[3*i];t=af^s;si=tuple(x for j,x in enumerate(F)if s>>j&1);to=tuple(x for j,x in enumerate(F)if t>>j&1)
  if si in seen:continue
  for j in stab:seen.add(tuple(sorted(images(x)[j]for x in si)))
  out.append((si,to,o[3*i+1],o[3*i+2]<<NP))
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
@functools.lru_cache(maxsize=4000)
def closure_table(F):
 pat=[sum(1<<i for i,x in enumerate(F)if x>>j&1) for j in range(NT)];full=(1<<len(F))-1
 up=tuple(sum(1<<b for b,q in enumerate(pat)if not(v&~q))for v in pat);dn=tuple(sum(1<<b for b,q in enumerate(pat)if not(q&~v))for v in pat)
 return up,dn,sum(1<<j for j,v in enumerate(pat)if v==full),sum(1<<j for j,v in enumerate(pat)if not v)
def cone_requirements(F,a,b):
 up,dn,ones,zeros=closure_table(F)
 for i in range(NT):
  if a>>i&1:ones|=up[i]
  if b>>i&1:zeros|=dn[i]
 return ones,zeros
count=collections.Counter(); hits=[]
root_state=None; root_progress=None; root_skip=0
covers=tuple(((1<<m.raw_count)-1)^x for x in N)
@functools.lru_cache(maxsize=10000)
def carrier(x):return sum(1<<i for i,v in enumerate(raw) if not(v&~x))
@functools.lru_cache(maxsize=30000)
def cover_ok(R,Cs,h):
 for u in covers:
  need=u&~R;sz=need.bit_count()
  if sz<=h:return True
  if sz>h+len(Cs):continue
  assign={0}
  for c in Cs:
   new=assign.copy()
   for done in assign:
    v=c&need&~done
    while v:
     bit=v&-v;new.add(done|bit);v-=bit
   assign=new
  if any(sz-a.bit_count()<=h for a in assign):return True
 return False
def vperm(mask,pi):return sum(1<<pi[i] for i in range(m.raw_count) if mask>>i&1)
@functools.lru_cache(maxsize=20000)
def context(F,R,Cs):
 std=canon(F);group=[j for j in range(len(rpi)) if tuple(sorted(images(v)[j]for v in F))==std]
 rr,cc=min((vperm(R,m.perms[j]),tuple(sorted(vperm(c,m.perms[j]) for c in Cs))) for j in group)
 return std,rr,cc
@functools.lru_cache(maxsize=48000)
def search(F,R,Cs,h):
 if not cover_ok(R,Cs,h):return False
 count['states']+=1
 if feasible(F,target,M^target):hits.append(('readonce',F,h));return True
 if h==0:return False
 for cone_no,(si,to,g1,g0) in enumerate(splits(F)):
  if (F,R,Cs,h)==root_state:
   if cone_no<root_skip:continue
   record={'state':root_state,'next_cone':cone_no};tmp=root_progress.with_suffix('.tmp');tmp.write_text(json.dumps(record)+'\n');tmp.replace(root_progress)
  g1,g0=cone_requirements(si,g1,g0)
  if g1&g0 or not feasible(si,g1,g0):continue
  unknown=M&~(g1|g0)
  if len(si)>=6 and unknown.bit_count()<=12:
   extra=unknown
   while True:
    v=g1|extra
    if feasible(si,v,M^v):
     for d in range(2,h+2):
      if search(*context(tuple(sorted((*to,*([v]*d)))),R,tuple(sorted((*Cs,carrier(v))))),h-d+1):hits.append(('defined-cone',F,h,si,to,v,d));return True
    if not extra:break
    extra=(extra-1)&unknown
  elif len(si)<=len(to)+2 and len(si)<=8:
   for v in trees(si):
    if v&g0 or g1&~v:continue
    for d in range(2,h+2):
     if search(*context(tuple(sorted((*to,*([v]*d)))),R,tuple(sorted((*Cs,carrier(v))))),h-d+1):hits.append(('forward-gate',F,h,si,to,v,d));return True
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
   # Any singleton carried by a monotone gate also occurs at one primitive of its cone.
   sup=0
   for v in si:sup|=carrier(v)
   # If this relaxed test survives, enumerate the exact remainder with bounded sharing.
   for d in range(2,h+2):
    if not cover_ok(R,tuple(sorted((*Cs,sup))),h-d+1):continue
    outer=tuple(sorted((*to2,*([sym]*d))))
    for pair in forward(outer,h-d+1):
     l=pair&M;u=pair>>NT
     if not(target&~u or (M^target)&l) and feasible(si,target&~l,(M^target)&u):hits.append(('reverse-cone',F,h,si,to,pair,d));return True
 return False

@functools.lru_cache(None)
def residual_cover(R):
 es=[(p,y) for p,y in m.E if not (R>>p&1 or R>>y&1)]
 return min(X.bit_count()+len({y for p,y in es if not X>>p&1})for X in range(1<<m.point_count))
def cofactor_reader_budget(F):
 if m.cfg!=0:return True
 # Removing the unique two-triple point leaves the >=15 K4 subdivision with diagonal ORs.
 # Removing another point leaves theta(3,3,3) and two private line literals, costing >=14.
 # With a line removed, deleting the central point retains K4-minus-one-line (>=12,
 # because the missing line can be added back with three gates), costing >=13 in total.
 for v,feature in enumerate(raw):
  if v<m.point_count:
   degree=sum(p==v for p,y in m.E); limit=2 if degree==2 else 3
  else:limit=4 if any(v in F for v in free)else 3
  # Without free ORs, L_meta_723 false_cofactor_bound strengthens K4 minus a line to 13.
  if F.count(feature)>limit:return False
 return True
def budget_context(F):
 R=sum(1<<i for i,v in enumerate(raw)if F.count(v)>1); extra=0
 for idx,v in enumerate(free):
  if v in F:
   for i in m.support[idx]:R|=1<<i
   extra+=F.count(v)>1
 Cs=tuple(sorted(carrier(v) for v in free if F.count(v)>1));return R,Cs

def run(used,dup):
 global root_state,root_skip,root_progress
 F=tuple((*raw,*(f for j,f in enumerate(free)if used>>j&1)));ex=m.data['excess_budget']-used.bit_count();h=ex-dup;cases={canon(tuple(sorted((*F,*extra)))) for extra in itertools.combinations_with_replacement(F,dup)};st=time.perf_counter();res=[]
 out=job/f'fresh-meta3773-five-{m.cfg}-{used}-{dup}-progress.json';previous=json.loads(out.read_text())if out.exists()else {'tested':0,'hits':[]}; start=previous['tested'];total=len(cases);end=start
 if previous.get('hits'):return {'cases':total,'tested':start,'solutions':previous['hits'],'already_found':True}
 for t,f in enumerate(sorted(cases)):
  if t<start:continue
  R,Cs=budget_context(f);root_state=(f,R,Cs,h);root_progress=job/f'fresh-meta3773-five-{m.cfg}-{used}-{dup}-cone.json';old=json.loads(root_progress.read_text())if root_progress.exists()else {};root_skip=(old.get('next_cone',0) if old.get('state')==[list(f),R,list(Cs),h] else 0);eligible=cofactor_reader_budget(f) and cover_ok(R,Cs,h);a=search(f,R,Cs,h) if eligible else False;res.append(a);end=t+1;state={'configuration':m.cfg,'used':used,'extra_primitive_occurrences':dup,'remaining_internal_excess':h,'total':total,'tested':end,'hits':hits,'seconds_this_chunk':time.perf_counter()-st};tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2)+'\n');tmp.replace(out);print('case',t+1,'of',total,'result',a,'branch-eligible',eligible,'states',count['states'],'seconds',round(time.perf_counter()-st,3),flush=True)
  if a:break
 return {'cases':total,'tested':end,'solutions':hits,'seconds':time.perf_counter()-st}
if __name__=='__main__':
 cfg,used,dup=map(int,sys.argv[1:4]);assert cfg==m.cfg;print('model',m.data['points'],'rows',NP,len(N),'group',len(rpi),flush=True);print(run(used,dup),flush=True)
