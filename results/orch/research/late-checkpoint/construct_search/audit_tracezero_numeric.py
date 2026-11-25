from pathlib import Path
source=Path('/tmp/oec/pequalnp-pilot-78/construct_search/tracezero_numeric.py').read_text().split('rng=np.random.default_rng')[0]
exec(compile(source,'tracezero_numeric_prefix','exec'))
from collections import Counter
cs=json.loads((OUT/'tracezero-numeric-candidates.json').read_text());counts=Counter();ranks=Counter();kr=Counter();maxdirect=0.;details=[]
for ci,c in enumerate(cs):
 z=np.array(c['real'])+1j*np.array(c['imag']);A,B=matrices(z);poly=np.zeros((5,5),complex)
 for perm in perms:
  pr=np.zeros((5,5),complex);pr[0,0]=1
  for i,j in enumerate(perm):
   nex=pr.copy();nex[1:,:]+=A[i,j]*pr[:-1,:];nex[:,1:]+=B[i,j]*pr[:,:-1];pr=nex
  poly+=pr
 poly[0,0]-=24;direct=float(np.max(np.abs(poly)));maxdirect=max(maxdirect,direct);counts[len(c['stabilizer'])]+=1;ranks[sum(v>1e-7 for v in c['jacobian_singular_values'])]+=1;kr[sum(v<1e-7 for v in c['common_kernel_singular_values'])]+=1;details.append({'candidate':ci,'direct_permanent_residual':direct,'jacobian_min_singular':c['jacobian_singular_values'][-1]})
report={'count':len(cs),'stabilizer_sizes':dict(counts),'jacobian_ranks_at_1e_7':dict(ranks),'common_kernel_dimensions_at_1e_7':dict(kr),'max_direct_permanent_residual':maxdirect,'details':details,'scope':'Independent direct permanent expansion of numerical candidates; not exact certification'};(OUT/'tracezero-numeric-audit.json').write_text(json.dumps(report,indent=2));print(json.dumps({k:v for k,v in report.items() if k!='details'}))
