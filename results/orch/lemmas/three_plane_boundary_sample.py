from pathlib import Path
import json,time,numpy as np
source=Path('/tmp/oec/pequalnp-pilot-79/boundary_numeric.py').read_text();exec(source.split('for run in range(1000):')[0])
t0=time.time();rng=np.random.default_rng(2317909);found=[];near=[];best=1e100
for run in range(1000):
 start=rng.normal(size=24)*([.3,1,2][run%3]);sol=opt.least_squares(calc,start,jac=lambda v:calc(v,True),bounds=(-20,20),max_nfev=700,ftol=1e-11,gtol=1e-11,xtol=1e-11)
 err=np.linalg.norm(sol.fun);B,A=matrices(sol.x)
 if err<1e-9 and not any(np.linalg.norm(sol.x-r['parameters'])<1e-4 for r in found):
  rows=[]
  for k,df in zip([2,3,4],dfs):
   P=np.array([(j,k-1-j) for j in range(k)],dtype=float).T/(k-1);Z=B[:,None]*P[0]+A[:,None]*P[1];G=np.array([np.broadcast_to(v,(k,)) for v in df(*Z)]);rows.extend(G.T)
  E=np.array(rows);sv=np.linalg.svd(E,compute_uv=False)
  r={'run':run,'parameters':sol.x.tolist(),'error':float(err),'extension_singular_values':sv.tolist()};found.append(r)
  print('ROOT',len(found),'run',run,'residual',err,'thirdsmallest',sv[-3],flush=True)
  if sv[-3]<1e-6:
   near.append(r);print('POTENTIAL_EXTENSION',r,flush=True);break
 if time.time()-t0>110:print('TIME_LIMIT',flush=True);break
(job/'boundary-sampled-roots.json').write_text(json.dumps({'roots':found,'potential_extensions':near,'runs':run+1,'seconds':time.time()-t0},indent=2));print('DONE',len(found),'distinctroots',run+1,'starts',time.time()-t0,flush=True)
