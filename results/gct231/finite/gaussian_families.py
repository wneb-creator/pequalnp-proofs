import sympy as s,numpy as np,itertools,json,time
from pathlib import Path
base=Path(__file__).parent
positions=list(itertools.combinations_with_replacement(range(4),2));lookup={p:i for i,p in enumerate(positions)}
t=s.symbols('t0:10');z=s.symbols('z');T=s.zeros(4)
for (i,j),v in zip(positions,t):T[i,j]=T[j,i]=v
f=s.expand(sum(s.prod(1+z*T[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24)
terms=[[(exp,int(coef)) for exp,coef in s.Poly(f.coeff(z,k),*t).terms()] for k in range(1,5)]
def evaluate(degree,R,I):
 R=np.asarray(R,dtype=np.int64).reshape(-1,10);I=np.asarray(I,dtype=np.int64).reshape(-1,10)
 outR=np.zeros(len(R),dtype=np.int64);outI=np.zeros(len(R),dtype=np.int64)
 for powers,coef in terms[degree-1]:
  a=np.full(len(R),coef,dtype=np.int64);b=np.zeros(len(R),dtype=np.int64)
  for j,power in enumerate(powers):
   for _ in range(power):a,b=a*R[:,j]-b*I[:,j],a*I[:,j]+b*R[:,j]
  outR+=a;outI+=b
 return outR,outI
def zeros(degree,R,I):
 a,b=evaluate(degree,R,I);return (a==0)&(b==0)
choicesR=np.array([0,1,-1,0,0],dtype=np.int64);choicesI=np.array([0,0,0,1,-1],dtype=np.int64)
weights=np.array([1 if i==j else 2 for i,j in positions[:9]],dtype=np.int64)
it=itertools.product(range(5),repeat=9);directions=set();processed=0;start=time.monotonic()
while True:
 batch=list(itertools.islice(it,20000))
 if not batch:break
 index=np.asarray(batch,dtype=np.int64);R=np.zeros((len(batch),10),dtype=np.int64);I=R.copy()
 R[:,:9]=choicesR[index];I[:,:9]=choicesI[index]
 R[:,9]=-R[:,:9]@weights;I[:,9]=-I[:,:9]@weights
 good=(np.abs(R[:,9])+np.abs(I[:,9]))<=1;R=R[good];I=I[good]
 for degree in (2,3,4):
  good=zeros(degree,R,I);R=R[good];I=I[good]
 for a,b in zip(R,I):
  nonzero=np.flatnonzero((a!=0)|(b!=0))
  if not len(nonzero):continue
  j=nonzero[0];u,v=int(a[j]),int(b[j])
  ar=a*u+b*v;ai=b*u-a*v
  directions.add(tuple(int(x) for x in ar)+tuple(int(x) for x in ai))
 processed+=len(batch)
D=np.array(sorted(directions),dtype=np.int64);R=D[:,:10];I=D[:,10:]
print('GAUSSIAN_DIRECTIONS_UP_TO_UNIT',len(D),'TRACE_INPUTS',processed,'SECONDS',time.monotonic()-start,flush=True)
adj=[set() for _ in D];pairs=[]
for i in range(len(D)-1):
 cand=np.arange(i+1,len(D))
 for mul in (1,-1,2):
  for degree in (2,3,4):
   good=zeros(degree,R[i]+mul*R[cand],I[i]+mul*I[cand]);cand=cand[good]
   if not len(cand):break
  if not len(cand):break
 for j in cand:
  j=int(j);pairs.append((i,j));adj[i].add(j);adj[j].add(i)
print('COMPATIBLE_PAIRS',len(pairs),'SECONDS',time.monotonic()-start,flush=True)
def mul(ar,ai,br,bi):return ar*br-ai*bi,ar*bi+ai*br
def independent(a,b,c):
 for i,j in itertools.combinations(range(10),2):
  u,v=mul(R[a,i],I[a,i],R[b,j],I[b,j]);w,x=mul(R[a,j],I[a,j],R[b,i],I[b,i]);dr,di=u-w,v-x
  if dr or di:
   u,v=mul(R[c,i],I[c,i],R[b,j],I[b,j]);w,x=mul(R[c,j],I[c,j],R[b,i],I[b,i]);ur,ui=u-w,v-x
   u,v=mul(R[a,i],I[a,i],R[c,j],I[c,j]);w,x=mul(R[a,j],I[a,j],R[c,i],I[c,i]);vr,vi=u-w,v-x
   lr,li=mul(dr,di,R[c],I[c]);ar,ai=mul(ur,ui,R[a],I[a]);br,bi=mul(vr,vi,R[b],I[b])
   return bool(np.any(lr!=ar+br) or np.any(li!=ai+bi))
 raise AssertionError('dependent pair')
triples=0;hits=[]
for a,b in pairs:
 for c in adj[a]&adj[b]:
  if c<=b or not independent(a,b,c):continue
  triples+=1
  sr=R[a]+R[b]+R[c];si=I[a]+I[b]+I[c]
  if not zeros(3,sr,si)[0]:continue
  if not all(zeros(4,rr,ii)[0] for rr,ii in ((sr,si),(-R[a]+R[b]+R[c],-I[a]+I[b]+I[c]),(R[a]-R[b]+R[c],I[a]-I[b]+I[c]))):continue
  hits.append([a,b,c])
print('INDEPENDENT_COMPATIBLE_TRIPLES',triples,'EXACT_HITS',len(hits),'SECONDS',time.monotonic()-start,flush=True)
result={'positions':positions,'entry_set':'0,1,-1,I,-I','trace_inputs':processed,'raw_entry_patterns':5**10,'directions_real_then_imag':D.tolist(),'compatible_pairs':pairs,'independent_pairwise_compatible_triples':triples,'three_dimensional_hits':hits,'arithmetic':'Exact Gaussian integer arithmetic using paired int64 arrays; all searched entries and degree≤4 expressions are far below integer overflow. No floating-point arithmetic.','scope':'Bounded finite enumeration only; no global nonexistence claim.'}
(base/'gaussian-families.json').write_text(json.dumps(result,indent=2)+'\n')
