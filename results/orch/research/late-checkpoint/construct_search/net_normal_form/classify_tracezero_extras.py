from pathlib import Path
import itertools,json,hashlib
p=Path('/tmp/oec/pequalnp-pilot-78/construct_search/net_normal_form')
slots=[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)];ix={xy:i for i,xy in enumerate(slots)};perms=list(itertools.permutations(range(4)))
def rr(rows,p,n=None):
 rows=[list(r) for r in rows];n=n or len(rows[0]);r=0;piv=[]
 for c in range(n):
  j=next((j for j in range(r,len(rows)) if rows[j][c]%p),None)
  if j is None:continue
  rows[r],rows[j]=rows[j],rows[r];rows[r]=[x*pow(rows[r][c],-1,p)%p for x in rows[r]]
  for j in range(len(rows)):
   if j!=r:
    z=rows[j][c];rows[j]=[(x-z*y)%p for x,y in zip(rows[j],rows[r])]
  piv.append(c);r+=1
  if r==len(rows):break
 return tuple(tuple(v) for v in rows[:r]),piv
def act(v,g):
 out=[0]*10
 for i,(j,k) in enumerate(slots):out[ix[tuple(sorted((g[j],g[k])))]]=v[i]
 return out
def norm(v,p):
 factor=pow(next(x for x in v if x),-1,p);return tuple(x*factor%p for x in v)
def kernel(rows,p,n):
 red,piv=rr(rows,p,n);out=[]
 for c in range(n):
  if c not in piv:
   v=[0]*n;v[c]=1
   for i,k in enumerate(piv):v[k]=-red[i][c]%p
   out.append(v)
 return out
def centered(v,p):return [x if x<=p//2 else x-p for x in v]
def matrix(v):
 return [[v[ix[tuple(sorted((i,j)))]] for j in range(4)] for i in range(4)]
reports={}
for prime in [19,23]:
 planes={tuple(map(tuple,plane)) for plane in json.loads((p/f'tracezero-f{prime}-2planes.json').read_text())}
 todo={plane for plane in planes if any(v[i] for v in plane for i in [0,4,7,9])};orbits=[]
 while todo:
  rep=min(todo);orbit={rr([act(v,g) for v in rep],prime)[0] for g in perms};assert orbit<=planes;todo-=orbit
  diag=[[v[i] for i in [0,4,7,9]] for v in rep];dr=len(rr(diag,prime)[0]);stabilizers=[]
  piv=rr(rep,prime)[1]
  for g in perms:
   acted=[act(v,g) for v in rep]
   if rr(acted,prime)[0]==rep:
    induced=[[v[j] for j in piv] for v in acted];stabilizers.append({'permutation':g,'induced_rows':induced})
  rows=matrix(rep[0])+matrix(rep[1]);report={'size':len(orbit),'diagonal_rank':dr,'representative':rep,'centered_representative':[centered(v,prime) for v in rep],'stabilizers':stabilizers,'common_kernel_basis':kernel(rows,prime,4)}
  if dr==1:
   coeff=kernel([[diag[0][i],diag[1][i]] for i in range(4)],prime,2)[0]
   h=norm([(coeff[0]*rep[0][i]+coeff[1]*rep[1][i])%prime for i in range(10)],prime)
   basic=[0]*10;basic[1]=1;basic[2]=prime-1
   report['hollow_kernel']=h;report['basic_star_kernel']=h in {norm(act(basic,g),prime) for g in perms}
  if dr==2:
   for stab in stabilizers:
    g=stab['permutation']
    if g==tuple(range(4)):continue
    rows=stab['induced_rows'];eigs=[]
    for lam in range(prime):
     coeffs=kernel([[(rows[j][i]-(lam if i==j else 0))%prime for j in range(2)] for i in range(2)],prime,2)
     for coeff in coeffs:
      v=norm([(coeff[0]*rep[0][i]+coeff[1]*rep[1][i])%prime for i in range(10)],prime)
      eigs.append({'eigenvalue':lam,'vector':v,'centered_vector':centered(v,prime),'matrix_rank':len(rr(matrix(v),prime)[0])})
    stab['eigenvectors']=eigs
  orbits.append(report)
 reports[str(prime)]={'total_planes':len(planes),'nonhollow_orbits':orbits}
print(json.dumps(reports,indent=2))
(p/'tracezero-extra-orbits.json').write_text(json.dumps(reports,indent=2)+'\n')
