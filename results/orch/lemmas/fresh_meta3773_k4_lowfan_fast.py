"""Exact low-fanout subcases for K4 subdivision with three free disjoint-line matching ORs."""
from pathlib import Path
import functools,itertools,collections,time,json,resource
resource.setrlimit(resource.RLIMIT_AS,(800<<20,800<<20));job=Path(__file__).resolve().parent
pairs=list(itertools.combinations(range(4),2));E=[(i,4+j)for j,pair in enumerate(pairs)for i in pair];P=[(1<<i)|(1<<j)for i,j in E];N=[X|sum(1<<j for j in range(4,10)if not any(X>>i&1 and e==j for i,e in E))for X in range(16)];rows=P+N;NP=len(P);NT=len(rows);M=(1<<NT)-1;target=(1<<NP)-1
raw=[sum(1<<i for i,r in enumerate(rows) if r>>j&1)for j in range(10)];diags=[(4+i,4+j)for i,j in itertools.combinations(range(6),2)if set(pairs[i]).isdisjoint(pairs[j])];free=[raw[a]|raw[b]for a,b in diags];base=raw+free
def signature(features):return tuple(sum(1<<i for i,f in enumerate(features)if f>>r&1)for r in range(NT))
def factorizations(F):
 pat=signature(F); af=(1<<len(F))-1; diff=tuple(tuple(pat[p]&~pat[n]for n in range(NP,NT))for p in range(NP))
 for s in range(1,af):
  if s.bit_count()<2:continue
  t=af^s;g1=g0=0
  for p,ds in enumerate(diff):
   for j,d in enumerate(ds):
    if d&t==0:g1|=1<<p;g0|=1<<(NP+j)
  if any(g1>>p&1 and g0>>(NP+j)&1 and not(d&s)for p,ds in enumerate(diff)for j,d in enumerate(ds)):continue
  yield s,t,g1,g0
if False:
 for name,F in [('base',base),('dup-point',base+[raw[0]]),('dup-edge',base+[raw[4]]),('dup-diag',base+[free[0]])]:
  st=time.perf_counter();co=collections.Counter(s.bit_count()for s,t,p,n in factorizations(F));print(name,dict(co),time.perf_counter()-st,flush=True)

def feasible_python(F,Pneed,Nneed):
 # Position of each input in each separating pair. The target is monotone in every feature.
 pos=[i for i in range(NP) if Pneed>>i&1];neg=[j for j in range(NP,NT)if Nneed>>j&1]
 pat=signature(F); diff=tuple(tuple(pat[i]&~pat[j] for j in neg) for i in pos)
 @functools.lru_cache(None)
 def sep(S):return tuple(sum(1<<j for j,d in enumerate(ds)if d&S)for ds in diff)
 @functools.lru_cache(None)
 def rec(S,A,B):
  if not A or not B:return True
  active=[i for i in range(len(pos))if A>>i&1]; s=sep(S)
  if any(s[i]&B!=B for i in active):return False
  if S&(S-1)==0:return True
  T=(S-1)&S
  while T:
   U=S^T
   if T<U:
    t=sep(T);u=sep(U);ca=cb=B;ta=tb=0
    for i in active:
     ca&=t[i];cb&=u[i]
     if t[i]&B==B:ta|=1<<i
     if u[i]&B==B:tb|=1<<i
    if ca|cb==B:
     opt=ca&cb;ls=B&~cb;rs=B&~ca;sel=opt
     while True:
      if rec(T,A,ls|sel) and rec(U,A,rs|(opt^sel)):return True
      if not sel:break
      sel=(sel-1)&opt
    if ta|tb==A:
     opt=ta&tb;ls=A&~tb;rs=A&~ta;sel=opt
     while True:
      if rec(T,ls|sel,B) and rec(U,rs|(opt^sel),B):return True
      if not sel:break
      sel=(sel-1)&opt
   T=(T-1)&S
  return False
 return rec((1<<len(F))-1,(1<<len(pos))-1,(1<<len(neg))-1)
import ctypes
shared=ctypes.CDLL(str(job/'fresh-meta3773-readonce.so'));shared.feasible.argtypes=[ctypes.c_int,ctypes.POINTER(ctypes.c_uint32),ctypes.c_uint32,ctypes.c_uint32]; shared.feasible.restype=ctypes.c_int
@functools.lru_cache(maxsize=16384)
def feasible(F,Pneed,Nneed):
 a=(ctypes.c_uint32*len(F))(*F); out=shared.feasible(len(F),a,Pneed,Nneed);assert out in (0,1);return bool(out)
@functools.lru_cache(maxsize=1000)
def trees(F):
 if len(F)==1:return frozenset(F)
 vals=set(); k=len(F)
 for s in range(1,(1<<k)-1,2):
  l=tuple(f for i,f in enumerate(F)if s>>i&1); r=tuple(f for i,f in enumerate(F)if not s>>i&1)
  for a in trees(l):
   for b in trees(r):vals.add(a&b);vals.add(a|b)
 return frozenset(vals)

def one_shared(F, symmetry=()):
 count=0; explored=0
 for s,t,req1,req0 in factorizations(F):
  if symmetry and s!=min(permmask(s,pi) for pi in symmetry):continue
  si=tuple(F[i] for i in range(len(F))if s>>i&1); to=tuple(F[i]for i in range(len(F))if t>>i&1); count+=1
  if len(si)<=len(to)+2:
   for v in trees(tuple(sorted(si))):
    if req1&~v or req0&v:continue
    explored+=1
    if feasible(tuple(sorted((*to,v,v))),target,M^target):return (s,t,v),count,explored
  else:
   # Symbolic duplicated feature. Low bits evaluate g=0, high bits evaluate g=1.
   G=M<<NT; dbl=lambda v:v|(v<<NT)
   for pair in trees(tuple(sorted((*map(dbl,to),G,G)))):
    low=pair&M;high=pair>>NT
    if target&~high or (M^target)&low:continue
    need1=target&~low;need0=(M^target)&high;explored+=1
    if feasible(tuple(sorted(si)),need1,need0):return(s,t,pair),count,explored
 return None,count,explored

perms=[]
for p4 in itertools.permutations(range(4)):
 er=[4+pairs.index(tuple(sorted((p4[i],p4[j]))))for i,j in pairs];di=[10+diags.index(tuple(sorted((er[i-4],er[j-4]))))for i,j in diags];perms.append(tuple((*p4,*er,*di)))
def permmask(s,pi):return sum(1<<pi[i] for i in range(len(pi))if s>>i&1)

def small_gate_data():
 for si,ti,req1,req0 in factorizations(base):
  if si!=min(permmask(si,pi)for pi in perms):continue
  S=tuple(base[i] for i in range(len(base)) if si>>i&1);T=tuple(base[i] for i in range(len(base))if ti>>i&1)
  if len(S)<=5:
   viable=[g for g in trees(tuple(sorted(S)))if not(req1&~g or req0&g)];print('small cone',si,[i for i in range(13)if si>>i&1],'viable',len(viable),'aliases',sum(g in base for g in viable),flush=True)
  else:print('large cone',si,'outside', [i for i in range(13)if ti>>i&1],flush=True)

if False:small_gate_data()

def monotone_outputs(F):
 known={0,(1<<(2*NT))-1,*F};active=known.copy()
 while active:
  nxt={x for a in active for b in known for x in (a|b,a&b)}-known; known|=nxt;active=nxt
 return known

def main():
 results={};st=time.perf_counter();allpairs={min(tuple(sorted((pi[a],pi[b])))for pi in perms)for a,b in itertools.combinations_with_replacement(range(13),2)}
 yes=[]
 for a,b in sorted(allpairs):
  if feasible(tuple(sorted((*base,base[a],base[b]))),target,M^target):yes.append((a,b))
 results['no_shared_internal']={'repeat_leaf_pair_orbits':len(allpairs),'solutions':yes}; print('no shared',results['no_shared_internal'],time.perf_counter()-st,flush=True)
 for i in [None,0,4,10]:
  F=base if i is None else base+[base[i]];pis=perms if i is None else [(*pi,13)for pi in perms if pi[i]==i];out=one_shared(F,pis);results[str(i)]={'solution':out[0],'partitions':out[1],'candidates':out[2]};print('one shared',i,results[str(i)],time.perf_counter()-st,flush=True)
 results['two_shared']=[]
 for s,t,req1,req0 in factorizations(base):
  if s!=min(permmask(s,pi) for pi in perms):continue
  si=tuple(base[i]for i in range(13)if s>>i&1);to=tuple(base[i]for i in range(13)if t>>i&1);hit=[];checked=0
  if len(si)<=5:
   for v in trees(tuple(sorted(si))):
    if req1&~v or req0&v:continue
    # Permit the previously computed feature to occur twice as two labelled leaves.
    # One further shared internal node may read these leaves; any DAG of the required form is covered.
    F=(*to,v,v); checked+=1;ans=one_shared(F)[0]
    if ans is not None:hit.append((v,ans))
    if feasible(tuple(sorted((*to,v,v,v))),target,M^target):hit.append((v,'three occurrences'))
  else:
   # Relax the remainder to an arbitrary monotone function of <=3 outside literals and the cone bit.
   sym=M<<NT; possibilities=set()
   for pair in monotone_outputs([v|(v<<NT)for v in to]+[sym]):
    low=pair&M;high=pair>>NT
    if target&~high or (M^target)&low:continue
    possibilities.add((target&~low,(M^target)&high))
   for p,n in possibilities:
    checked+=1
    if feasible(tuple(sorted(si)),p,n):hit.append((p,n))
  result={'inside':s,'size':len(si),'checked':checked,'relaxed_solutions':hit};results['two_shared'].append(result);print('2 shared',result,time.perf_counter()-st,flush=True)
 results['seconds']=time.perf_counter()-st;(job/'fresh-meta3773-k4-lowfan-result.json').write_text(json.dumps(results,indent=2)+'\n');print('DONE',results['seconds'],flush=True)
if __name__=='__main__':main()
