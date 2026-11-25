from pathlib import Path
import itertools,functools,collections,sys,time,json,resource
resource.setrlimit(resource.RLIMIT_AS,(750<<20,750<<20));job=Path(__file__).resolve().parent
E=[(i,j) for i in range(4) for j in (4,5+i)];P=[(1<<i)|(1<<j)for i,j in E];N=[X|sum(1<<j for j in range(4,9)if not any(X>>i&1 and e==j for i,e in E)) for X in range(16)]; rows=P+N; target=(1<<8)-1; M=(1<<24)-1
raw=[sum(1<<r for r,m in enumerate(rows)if m>>i&1) for i in range(9)]
free=lambda F:sum(1<<r for r,m in enumerate(rows) if (m>>5)&F)
def signature(features):return tuple(sum(1<<i for i,f in enumerate(features) if f>>r&1) for r in range(24))
def factorizations(features):
 patterns=signature(features);Nf=len(features); allf=(1<<Nf)-1; diff=[[patterns[p]&~patterns[n] for n in range(8,24)]for p in range(8)]
 for S in range(1,allf):
  if S.bit_count()<2:continue
  T=allf^S; guards=[(p,n+8) for p,ds in enumerate(diff) for n,d in enumerate(ds) if d&T==0];gp=set(p for p,n in guards);gn=set(n for p,n in guards)
  if any(diff[p][n-8]&S==0 for p in gp for n in gn):continue
  yield S,T,sum(1<<p for p in gp),sum(1<<n for n in gn)
models={'no-extra-feature':raw,'dup-point':raw+[raw[0]],'dup-common':raw+[raw[4]],'dup-private':raw+[raw[5]],'free-pair':raw+[free(3)],'free-triple':raw+[free(7)],'free-quad':raw+[free(15)]}
if __name__=='__main__':
 for name,features in models.items():
  counted=collections.Counter((S.bit_count(),gp.bit_count(),gn.bit_count()) for S,T,gp,gn in factorizations(features)); print(name,'by_size',dict(sorted(collections.Counter({k:sum(v for (s,p,n),v in counted.items()if s==k)for k,p,n in counted}).items())),flush=True)

@functools.lru_cache(maxsize=8192)
def feasible(F,Pneed,Nneed):
 # Position of each input in each separating pair. The target is monotone in every feature.
 pos=[i for i in range(8) if Pneed>>i&1];neg=[j for j in range(8,24)if Nneed>>j&1]
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
@functools.lru_cache(maxsize=1000)
def trees(F):
 if len(F)==1:return frozenset(F)
 vals=set(); k=len(F)
 for s in range(1,(1<<k)-1,2):
  l=tuple(f for i,f in enumerate(F)if s>>i&1); r=tuple(f for i,f in enumerate(F)if not s>>i&1)
  for a in trees(l):
   for b in trees(r):vals.add(a&b);vals.add(a|b)
 return frozenset(vals)

def one_shared(F):
 count=0; explored=0
 for s,t,req1,req0 in factorizations(F):
  si=tuple(F[i] for i in range(len(F))if s>>i&1); to=tuple(F[i]for i in range(len(F))if t>>i&1); count+=1
  if len(si)<=len(to)+2:
   for v in trees(tuple(sorted(si))):
    if req1&~v or req0&v:continue
    explored+=1
    if feasible(tuple(sorted((*to,v,v))),target,M^target):return (s,t,v),count,explored
  else:
   # Symbolic duplicated feature. Low bits evaluate g=0, high bits evaluate g=1.
   G=M<<24; dbl=lambda v:v|(v<<24)
   for pair in trees(tuple(sorted((*map(dbl,to),G,G)))):
    low=pair&M;high=pair>>24
    if target&~high or (M^target)&low:continue
    need1=target&~low;need0=(M^target)&high;explored+=1
    if feasible(tuple(sorted(si)),need1,need0):return(s,t,pair),count,explored
 return None,count,explored

def main():
 # Zero internal fanout: at most two extra leaf occurrences, primitive repetitions or free ORs.
 labels=tuple(1<<i for i in range(9))+tuple(sum(1<<(5+i) for i in f)for k in range(2,5)for f in itertools.combinations(range(4),k)); allpi=list(itertools.permutations(range(4)))
 def perm(mask,pi):return (mask&(1<<4))|sum((1<<pi[i])for i in range(4)if mask>>i&1)|sum((1<<(5+pi[i])) for i in range(4) if mask>>(5+i)&1)
 reps={min(tuple(sorted(perm(i,p)for i in extra))for p in allpi)for extra in itertools.combinations_with_replacement(labels,2)}
 def val(label):return sum(1<<i for i,m in enumerate(rows)if m&label)
 results={};start=time.perf_counter();yes=[]
 for r in sorted(reps):
  if feasible(tuple(sorted((*raw,*map(val,r)))),target,M^target):yes.append(r)
 results['zero_shared']={'extra_leaf_orbits':len(reps),'solutions':yes};print(results,flush=True)
 for name,F in models.items():
  st=time.perf_counter();answer,n,c=one_shared(F);results[name]={'allowed_partitions':n,'tested_tables':c,'solution':answer,'seconds':time.perf_counter()-st};print(name,results[name],flush=True)
 results['two_shared_no_duplicate']={'possible_first_partitions':len(list(factorizations(raw)))}
 results['seconds']=time.perf_counter()-start; (job/'fresh-meta3773-claw4-fanout-result.json').write_text(json.dumps(results,indent=2)+'\n');print('done',results['seconds'],flush=True)
if __name__=='__main__':main()
