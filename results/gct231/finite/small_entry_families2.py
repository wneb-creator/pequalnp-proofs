import sympy as s,numpy as np,itertools,json,time,math
from pathlib import Path
base=Path(__file__).parent
positions=list(itertools.combinations_with_replacement(range(4),2));lookup={p:i for i,p in enumerate(positions)}
t=s.symbols('t0:10');z=s.symbols('z');T=s.zeros(4)
for (i,j),v in zip(positions,t):T[i,j]=T[j,i]=v
f=s.expand(sum(s.prod(1+z*T[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24)
polys=[s.expand(f.coeff(z,k)) for k in range(1,5)]
functions=[s.lambdify(t,h,'numpy') for h in polys]
offdiag=np.array(list(itertools.product(range(-2,3),repeat=6)),dtype=np.int64)
diag=np.array(list(itertools.product(range(-2,3),repeat=3)),dtype=np.int64)
parts=[]
for start in range(0,len(offdiag),128):
 batch=offdiag[start:start+128]
 C=np.zeros((len(batch),len(diag),10),dtype=np.int64)
 C[:,:,[1,2,3,5,6,8]]=batch[:,None,:]
 C[:,:,[0,4,7]]=diag[None,:,:]
 C[:,:,9]=-np.sum(diag,axis=1)[None,:]-2*np.sum(batch,axis=1)[:,None]
 C=C.reshape(-1,10);C=C[np.abs(C[:,9])<=2]
 for fn in functions[1:]:C=C[np.asarray(fn(*C.T))==0]
 if len(C):parts.append(C)
A=np.vstack(parts);A=A[np.any(A!=0,axis=1)]
A=A[np.array([row[np.flatnonzero(row)[0]]>0 for row in A])]
primitive=[]
for row in A:
 g=0
 for value in row:g=math.gcd(g,abs(int(value)))
 if g==1:primitive.append(row)
A=np.array(primitive,dtype=np.int64)
print('CONSTANT_DIRECTIONS_UP_TO_SIGN',len(A),flush=True)
maps=[]
for perm in itertools.permutations(range(4)):
 maps.append([lookup[tuple(sorted((perm[i],perm[j])))] for i,j in positions])
def normalize(v):
 v=tuple(int(x) for x in v);g=0
 for x in v:g=math.gcd(g,abs(x))
 v=tuple(x//g for x in v)
 if next(x for x in v if x)!=abs(next(x for x in v if x)):v=tuple(-x for x in v)
 return v
orbits={}
for row in A:
 key=min(normalize(row[mapping]) for mapping in maps)
 orbits[key]=orbits.get(key,0)+1
print('DIRECTION_S4_ORBITS',len(orbits),flush=True)
adjacency=[set() for row in A];pairs=[];plane_orbits={};wedge_positions=list(itertools.combinations(range(10),2))
start=time.monotonic()
for i,a in enumerate(A):
 if i+1==len(A):break
 B=A[i+1:];good=np.ones(len(B),dtype=bool)
 for mult in (1,-1,2):
  C=a+mult*B
  for fn in functions[1:]:good &= np.asarray(fn(*C.T))==0
 for offset in np.flatnonzero(good):
  j=i+1+int(offset);b=A[j];adjacency[i].add(j);adjacency[j].add(i);pairs.append((i,j))
  def wedge(aa,bb):return normalize([aa[k]*bb[l]-aa[l]*bb[k] for k,l in wedge_positions])
  key=min(wedge(a[mapping],b[mapping]) for mapping in maps)
  if key not in plane_orbits:plane_orbits[key]={'a':a.tolist(),'b':b.tolist(),'count':0}
  plane_orbits[key]['count']+=1
print('COMPATIBLE_PAIRS',len(pairs),'PLANE_S4_ORBITS',len(plane_orbits),'SECONDS',time.monotonic()-start,flush=True)
def independent(a,b,c):
 for i,j in wedge_positions:
  det=int(a[i]*b[j]-a[j]*b[i])
  if det:
   u=int(c[i]*b[j]-c[j]*b[i]);v=int(a[i]*c[j]-a[j]*c[i])
   return any(det*int(c[k])!=u*int(a[k])+v*int(b[k]) for k in range(10))
 raise AssertionError('dependent pair')
triples=0;hits=[]
for i,j in pairs:
 for k in sorted(adjacency[i]&adjacency[j]):
  if k<=j:continue
  a,b,c=A[i],A[j],A[k]
  if not independent(a,b,c):continue
  triples+=1
  if functions[2](*(a+b+c))!=0:continue
  if any(functions[3](*v)!=0 for v in (a+b+c,-a+b+c,a-b+c)):continue
  hits.append([a.tolist(),b.tolist(),c.tolist()])
print('INDEPENDENT_COMPATIBLE_TRIPLES',triples,'EXACT_FAMILY_HITS',len(hits),flush=True)
result={'positions':positions,'entry_set':[-2,-1,0,1,2],'raw_direction_count':5**10,'directions_up_to_sign':A.tolist(),'direction_S4_orbits':[{'vector':list(k),'count':v} for k,v in orbits.items()],'compatible_pair_count':len(pairs),'plane_S4_orbits':list(plane_orbits.values()),'independent_pairwise_compatible_triples':triples,'three_dimensional_hits':hits,'scope':'Exact bounded small-entry enumeration; no global nonexistence claim.'}
(base/'small-entry-families2.json').write_text(json.dumps(result,indent=2)+'\n')
