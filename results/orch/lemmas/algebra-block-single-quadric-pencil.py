import sympy as s,json,time
from pathlib import Path
start=time.time();data=json.loads(Path('/tmp/oec/pequalnp-pilot-79/rank2-block-single-extension.json').read_text());w=s.symbols('w:7');r=s.sqrt(2);z=s.symbols('z')
fs=[s.sympify(f) for f in data['polynomials']];qs=[f for f in fs if s.Poly(f,*w).total_degree()==2];Hs=[s.hessian(q,w) for q in qs]
print('ranks',[H.rank() for H in Hs],flush=True)
D=(Hs[0]+z*Hs[1]).det(method='domain-ge');print('det',s.factor(D,extension=r),'seconds',time.time()-start,flush=True)
