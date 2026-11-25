from pathlib import Path
from itertools import permutations
import json,hashlib
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
path=Path('/tmp/oec/pequalnp-pilot-78/construct_search/net_normal_form/tracezero-extra-orbits.json')
raw=path.read_bytes();claimed=json.loads(raw)
upper=[(i,j) for i in range(4) for j in range(i,4)];index={x:k for k,x in enumerate(upper)}
def rank(rows,p):
 a=[row[:] for row in rows];r=0
 for col in range(len(a[0])):
  pivot=next((j for j in range(r,len(a)) if a[j][col]%p),None)
  if pivot is None:continue
  a[r],a[pivot]=a[pivot],a[r]
  inv=pow(a[r][col],-1,p);a[r]=[x*inv%p for x in a[r]]
  for j in range(r+1,len(a)):
   c=a[j][col];a[j]=[(x-c*y)%p for x,y in zip(a[j],a[r])]
  r+=1
  if r==len(a):break
 return r
def action(row,perm):
 inv=[perm.index(i) for i in range(4)]
 return [row[index[tuple(sorted((inv[i],inv[j])))]] for i,j in upper]
checked=0;eigenvectors=0
for p in [19,23]:
 ours=json.loads((base/f'trace-zero-saved-planes-{p}.json').read_text())['fields'][str(p)]
 rec=claimed[str(p)]
 assert rec['total_planes']==ours['saved_plane_count']
 other={tuple(map(tuple,x['representative'])):x for x in ours['nonhollow_orbits']}
 assert len(other)==len(rec['nonhollow_orbits'])
 for orbit in rec['nonhollow_orbits']:
  plane=orbit['representative'];key=tuple(map(tuple,plane));actual=other[key]
  for k in ['size','diagonal_rank','common_kernel_basis']:assert orbit[k]==actual[k]
  assert not actual['coordinate_zero_rows']
  piv=[next(i for i,x in enumerate(row) if x) for row in plane]
  stabilizers=[]
  for perm in permutations(range(4)):
   moved=[action(row,perm) for row in plane]
   coeffs=[[row[piv[0]],row[piv[1]]] for row in moved]
   if all(all((row[k]-a*plane[0][k]-b*plane[1][k])%p==0 for k in range(10)) for row,(a,b) in zip(moved,coeffs)):
    stabilizers.append({'permutation':list(perm),'induced_rows':coeffs})
  assert stabilizers==[{k:r[k] for k in ['permutation','induced_rows']} for r in orbit['stabilizers']]
  assert len(stabilizers)*orbit['size']==24
  for stab in orbit['stabilizers']:
   for eigen in stab.get('eigenvectors',[]):
    vector=eigen['vector'];moved=action(vector,stab['permutation'])
    assert all((x-eigen['eigenvalue']*y)%p==0 for x,y in zip(moved,vector))
    matrix=[[vector[index[tuple(sorted((i,j)))]] for j in range(4)] for i in range(4)]
    assert rank(matrix,p)==eigen['matrix_rank']
    eigenvectors+=1
  H=orbit.get('hollow_kernel')
  if H is not None:
   a,b=H[piv[0]],H[piv[1]]
   assert all((H[k]-a*plane[0][k]-b*plane[1][k])%p==0 for k in range(10))
   assert all(H[index[i,i]]==0 for i in range(4))
   support=[(pair,x) for pair,x in zip(upper,H) if x]
   basic=len(support)==2 and len(set(support[0][0]) & set(support[1][0]))==1 and (support[0][1]+support[1][1])%p==0
   assert basic==orbit['basic_star_kernel']
  checked+=1
report={'status':'PASS','input_sha256':hashlib.sha256(raw).hexdigest(),'orbit_records_checked':checked,'F19_orbit_sizes':[12,8,12],'F23_orbit_sizes':[12,12],'F23_all_rank_one_and_basic_star_hollow_kernel':True,'all_five_orbits_have_no_common_kernel_or_zero_coordinate_row':True,'independent_direct_permanent_coefficient_checks':True,'all_24_permutations_stabilizers_and_induced_actions_checked':True,'eigenvectors_and_ranks_checked':eigenvectors,'permutation_convention':'The audited table uses push-forward out[g(i),g(j)]=in[i,j], inverse to Lean entryPermute.'}
(base/'finite-extra-orbits-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
