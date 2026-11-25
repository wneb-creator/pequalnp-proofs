from pathlib import Path
source=Path('/tmp/oec/pequalnp-pilot-78/construct_search/tracezero_numeric.py').read_text().split('rng=np.random.default_rng')[0]
exec(compile(source,'tracezero_numeric_prefix','exec'))
from collections import Counter
cs=json.loads((OUT/'tracezero-numeric-candidates.json').read_text());idx={e:k for k,e in enumerate(ij)};idx.update({(j,i):k for k,(i,j) in enumerate(ij)});counts=Counter();records=[]
for ci,c in enumerate(cs):
 z=np.array(c['real'])+1j*np.array(c['imag']);A,B=matrices(z);M=np.zeros((10,10),complex)
 for perm in perms:
  for pos in range(4):
   pr=np.zeros((4,4),complex);pr[0,0]=1
   for i,j in enumerate(perm):
    if i==pos:continue
    nex=pr.copy();nex[1:,:]+=A[i,j]*pr[:-1,:];nex[:,1:]+=B[i,j]*pr[:,:-1];pr=nex
   col=idx[pos,perm[pos]];row=0
   for degree in range(4):
    for it in range(degree+1):M[row,col]+=pr[degree-it,it];row+=1
 rownorm=np.linalg.norm(M,axis=1);N=M/np.maximum(rownorm,1e-30)[:,None];sv=np.linalg.svd(N,compute_uv=False);rank=int(sum(v>1e-6 for v in sv));counts[rank]+=1;vectors=np.array([[T[i,j] for T in [A,B]] for i,j in ij]);kerres=float(np.max(np.abs(N@vectors)));records.append({'candidate':ci,'first_variation_rank_at_1e_6':rank,'row_scaled_singular_values':sv.tolist(),'known_kernel_residual':kerres})
report={'count':len(records),'rank_counts':dict(counts),'minimum_eighth_singular_value':min(r['row_scaled_singular_values'][7] for r in records),'max_known_kernel_residual':max(r['known_kernel_residual'] for r in records),'records':records,'scope':'Numerical first-variation obstruction only, not an exact or exhaustive proof'};(OUT/'tracezero-numeric-extensions.json').write_text(json.dumps(report,indent=2));print(json.dumps({k:v for k,v in report.items() if k!='records'}))
