from pathlib import Path
import itertools,json,time
from fractions import Fraction
p=Path('/tmp/oec/pequalnp-pilot-78/construct_search/net_normal_form')
hollow=json.loads(Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero/hollow_planes.json').read_text())
slots=[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]
index={xy:k for k,xy in enumerate(slots)};index.update({(j,i):k for k,(i,j) in enumerate(slots)})
def rr(rows,p):
 rows=[r[:] for r in rows];r=0
 for c in range(10):
  j=next((j for j in range(r,len(rows)) if rows[j][c]%p),None)
  if j is None:continue
  rows[r],rows[j]=rows[j],rows[r];inv=pow(rows[r][c],-1,p);rows[r]=[x*inv%p for x in rows[r]]
  for j in range(len(rows)):
   if j!=r:
    z=rows[j][c];rows[j]=[(x-z*y)%p for x,y in zip(rows[j],rows[r])]
  r+=1
  if r==len(rows):break
 return tuple(tuple(v) for v in rows)
reports=[]
for prime in [5,7,11,13,17,19,23]:
 path=p/f'tracezero-f{prime}-2planes.json'
 if not path.exists():continue
 planes=json.loads(path.read_text());known=set()
 for item in hollow:
  rows=[]
  for h in item['rref']:
   v=[0]*10
   for j,x in zip([1,2,3,5,6,8],h):
    q=Fraction(x);v[j]=q.numerator*pow(q.denominator,-1,prime)%prime
   rows.append(v)
  known.add(rr(rows,prime))
 for A,B in planes:
  assert sum(A[i] for i in [0,4,7,9])%prime==0
  assert sum(B[i] for i in [0,4,7,9])%prime==0
  assert rr([A,B],prime)==tuple(map(tuple,[A,B]))
  result={}
  for perm in itertools.permutations(range(4)):
   term={(0,0):1}
   for i,j in enumerate(perm):
    k=index[i,j];out={}
    for (u,v),coef in term.items():
     for delta,factor in [((0,0),1),((1,0),A[k]),((0,1),B[k])]:
      uv=(u+delta[0],v+delta[1]);out[uv]=(out.get(uv,0)+coef*factor)%prime
    term=out
   for uv,coef in term.items():result[uv]=(result.get(uv,0)+coef)%prime
  assert result[(0,0)]==24%prime
  assert all(coef==0 for uv,coef in result.items() if uv!=(0,0))
 found_hollow={tuple(map(tuple,plane)) for plane in planes if all(v[i]==0 for v in plane for i in [0,4,7,9])}
 assert found_hollow==known
 report={'prime':prime,'planes':len(planes),'known_hollow_planes':len(known),'full_permanent_polynomials':'PASS'};reports.append(report);print(report,flush=True)
(p/'tracezero-direct-audit.json').write_text(json.dumps({'verdict':'PASS','primes':reports},indent=2)+'\n')
