from pathlib import Path
import sympy as s,json,itertools,hashlib
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'geometry_search/rowzero'
manifest=json.loads((job/'Bzero-boundaries-manifest.json').read_text());certs=json.loads((job/'Bzero-boundary-certificates-verified.json').read_text())
a,b,c,d,u,v=s.symbols('a b c d s t');variables=(a,b,c,d);loc={str(x):x for x in variables+(u,v)};Q=s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2
R,*rv=ring('a,b,c,d',QQ);reports={}
for name,case in manifest.items():
 D=[s.sympify(x,locals=loc) for x in case['D_forms']];r=[s.sympify(x,locals=loc) for x in case['r_forms']]
 x=[(r[i]+D[i])/2 for i in range(3)];f=[(D[i]-r[i])/2 for i in range(3)]
 Tp=s.Matrix([[0,x[0],x[1],x[2]],[x[0],0,f[2],f[1]],[x[1],f[2],0,f[0]],[x[2],f[1],f[0],0]])
 M=s.ones(4)+Q*Tp*Q.T;actual=0
 for bits in range(1,16):
  cols=[j for j in range(4) if bits>>j&1];actual+=(-1)**(4-len(cols))*s.prod(sum(M[i,j] for j in cols) for i in range(4))
 actual=s.Poly(s.expand(actual-24),u,v)
 qa=-sum(r[i]**2+4*r[i]*D[i]+D[i]**2 for i in range(3));dot=sum(D[i]*r[i] for i in range(3));norm=sum(x*x for x in D)
 pm=(dot+norm/2)**2+sum(D[i]**2*r[i]**2 for i in range(3))/4-sum(D[i]**2*D[j]**2 for i in range(3) for j in range(i+1,3))/4
 pf=pm+qa*qa/16+qa*(dot/2+norm/4)
 expect=s.Poly(s.expand(qa+pf),u,v);assert actual==expect
 regenerated=[]
 for degree,expr in [(2,qa),(4,pm)]:
  p=s.Poly(s.expand(expr),u,v)
  for i in range(degree+1):
   g=p.coeff_monomial(u**(degree-i)*v**i)
   if g:regenerated.append(s.Poly(g,*variables).clear_denoms()[1].primitive()[1].as_expr())
 assert all(s.expand(s.sympify(g,locals=loc)-h)==0 for g,h in zip(case['generators'],regenerated)) and len(regenerated)==8
 cert=certs[name];assert cert['generators']==case['generators']
 parse=lambda x:R.from_expr(s.sympify(x.replace('^','**'),locals=loc))
 residual=sum(parse(g)*parse(m) for g,m in zip(cert['generators'],cert['multipliers']))-QQ(cert['target']);assert residual==0 and QQ(cert['target'])
 reports[name]={'status':'PASS','exact_Ryser_coefficients':12,'quartic_mod_quadratic_identity':True,'input_generators_regenerated':8,'certificate_residual':'0','nonzero_constant':cert['target']}
report={'status':'PASS','cases':reports,'coverage_review':'Zero product ofthreebinarylinearforms hasazero factor. Cubic productidentity gives both anr_i andanU_j zero. SimultaneousS3 reduces i=j tosamecase, whereD0=0 andD-rank2normalizes remainingpair. Fori!=j choose(r0,U1)zero, hence r1=-D1; someDcoordinatepair isindependent, givingthree listedcharts. All lower-rank additionalfactorzeros remaincovered. ScopeassumesD-image rank2.','manifest_sha256':hashlib.sha256((job/'Bzero-boundaries-manifest.json').read_bytes()).hexdigest()}
(base/'geometry_search/Bzero-boundaries-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
