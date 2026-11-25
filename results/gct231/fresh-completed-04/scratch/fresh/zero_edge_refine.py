from pathlib import Path
exec(Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh/zero_edge_numeric.py').read_text().split('rng=np.random')[0])
seed=json.loads((base/'zero-edge-numeric-roots.json').read_text())[0]
z=np.array(seed['real'])+1j*np.array(seed['imag'])
for stage in range(4):
 fit=least_squares(fun,np.r_[z.real,z.imag],jac=jac,max_nfev=2500,ftol=2.3e-16,xtol=2.3e-16,gtol=2.3e-16,method='lm')
 z=fit.x[:12]+1j*fit.x[12:]
 D=np.array([[z[0],z[1]],[z[2],z[3]],[z[4],z[5]],[-z[0]-z[2]-z[4]-2*(1+z[6]+z[8]+z[10]),-z[1]-z[3]-z[5]-2*(1+z[7]+z[9]+z[11])]])
 print('STAGE',stage,'ERROR',np.max(abs(fun(fit.x))),'DIAG_SINGULAR_VALUES',np.linalg.svd(D,compute_uv=False).tolist(),'JAC_SV',np.linalg.svd(jac(fit.x),compute_uv=False)[-4:].tolist(),'NFEV',fit.nfev,flush=True)
print('COEFFICIENTS',z.tolist(),flush=True)
