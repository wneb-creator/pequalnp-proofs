from pathlib import Path
import itertools,json,collections,time
b=Path('/tmp/oec/pequalnp-pilot-78');ij=[(i,j) for i in range(4) for j in range(i,4)];idx={e:k for k,e in enumerate(ij)};idx.update({(j,i):k for k,(i,j) in enumerate(ij)});terms=[[idx[i,j] for i,j in enumerate(perm)] for perm in itertools.permutations(range(4))];basis=[]
for k in range(8):
 v=[int(i==k) for i in range(10)];v[8]=-sum(v[j] for j in [1,2,3,5,6]);v[9]=-sum(v[j] for j in [0,4,7]);basis.append(v)
def rank(M,p):
 a=[r[:] for r in M];n=0
 for j in range(len(a[0])):
  h=next((i for i in range(n,len(a)) if a[i][j]%p),None)
  if h is None:continue
  a[n],a[h]=a[h],a[n];u=pow(a[n][j],-1,p);a[n]=[x*u%p for x in a[n]]
  for i in range(n+1,len(a)):
   q=a[i][j];a[i]=[(x-q*y)%p for x,y in zip(a[i],a[n])]
  n+=1
  if n==len(a):break
 return n
def jacobian(plane,p):
 A,B=plane;pivots=[next(i for i,x in enumerate(v) if x) for v in plane];assert max(pivots)<8;free=[i for i in range(8) if i not in pivots];G=[collections.defaultdict(int) for _ in range(8)]
 for term in terms:
  for pos,entry in enumerate(term):
   poly={(0,0):1}
   for j,en in enumerate(term):
    if j==pos:continue
    nxt=collections.defaultdict(int)
    for (u,v),c in poly.items():nxt[u,v]+=c;nxt[u+1,v]+=c*A[en];nxt[u,v+1]+=c*B[en]
    poly=nxt
   for k in free:
    co=basis[k][entry]
    if co:
     for mon,v in poly.items():G[k][mon]+=co*v
 rows=[]
 for deg in [2,3,4]:
  for j in range(deg+1):rows.append([G[k].get((deg-j-1,j),0)%p for k in free]+[G[k].get((deg-j,j-1),0)%p for k in free])
 return rows
records=[];start=time.monotonic()
for p in [5,7,11,13,17,19,23]:
 path=b/f'construct_search/net_normal_form/tracezero-f{p}-2planes.json';planes=json.loads(path.read_text());counts=collections.Counter();details=[]
 for plane in planes:
  dr=rank([[v[j] for j in [0,4,7,9]] for v in plane],p);jr=rank(jacobian(plane,p),p);counts[dr,jr]+=1;details.append({'diagonal_rank':dr,'jacobian_rank':jr})
 record={'prime':p,'counts':[{'diagonal_rank':d,'jacobian_rank':r,'count':n} for (d,r),n in sorted(counts.items())],'planes':details};records.append(record);print(json.dumps({k:v for k,v in record.items() if k!='planes'}),flush=True)
(b/'construct_search/tracezero-jacobians.json').write_text(json.dumps({'scope':'Exact finite-field Jacobian ranks in full Gr(2,8) affine charts; no complex completeness claim','records':records},indent=2));print('SECONDS',time.monotonic()-start,flush=True)
