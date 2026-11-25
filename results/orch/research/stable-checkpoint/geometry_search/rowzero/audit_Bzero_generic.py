from pathlib import Path
from itertools import permutations,combinations
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
import sympy as S
import json,hashlib,resource,time
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(60,65))
start=time.monotonic()
source=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/tracezero_Bzero_generic')
out=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
raw=(source/'systems.json').read_bytes();systems=json.loads(raw)
assert systems['variables']==['a','b','x','y','z']
a,b,x,y,z,s,t=S.symbols('a b x y z s t');lam=[x,y,z]
R,*gens=ring('a,b,x,y,z',QQ)
reports={}
for case in systems['cases']:
 name=case['name'];perm=case['permutation'];pair=case['independent_r_coordinate_pair']
 r=[None]*3;r[pair[0]]=s;r[pair[1]]=t;r[next(i for i in range(3) if i not in pair)]=a*s+b*t
 U=[lam[i]*r[perm[i]] for i in range(3)];D=[U[i]-r[i] for i in range(3)]
 for key,actual in [('r',r),('U',U),('D',D)]:
  assert all(S.expand(v-S.sympify(row[0])*s-S.sympify(row[1])*t)==0 for v,row in zip(actual,case[key]))
 q=-sum(r[i]**2+4*r[i]*D[i]+D[i]**2 for i in range(3))
 C=S.prod(U)-2*S.prod(r)
 assert S.expand(C-(x*y*z-2)*S.prod(r))==0
 normD=sum(v*v for v in D);dot=sum(D[i]*r[i] for i in range(3))
 Pm=(dot+normD/2)**2+sum(D[i]**2*r[i]**2 for i in range(3))/4-sum(D[i]**2*D[j]**2 for i in range(3) for j in range(i+1,3))/4
 Pf=Pm+q*q/16+q*(dot/2+normD/4)
 expected=[x*y*z-2]
 for degree,expr in [(2,q),(4,Pf)]:
  poly=S.Poly(S.expand(expr),s,t)
  expected.extend(poly.coeff_monomial(s**(degree-j)*t**j) for j in range(degree+1))
 assert len(expected)==len(case['generators'])==9
 for value,g,scale in zip(expected,case['generators'],case['scales_to_permanent_coefficients']):
  assert S.expand(value-S.sympify(scale)*S.sympify(g))==0
 certificate_path=source/f'{name}-certificate.json';cert_raw=certificate_path.read_bytes();cert=json.loads(cert_raw)
 generators=[R.from_expr(S.sympify(g)) for g in case['generators']]
 assert generators==[R.from_expr(S.sympify(g)) for g in cert['source_generators']]
 multipliers=[R.from_expr(S.sympify(m.replace('^','**'))) for m in cert['multipliers']]
 target=R.from_expr(S.sympify(cert['nonzero_constant']))
 assert target and not any(any(mon) for mon in target)
 assert sum((g*m for g,m in zip(generators,multipliers)),R.zero)==target
 reports[name]={'status':'PASS','certificate_sha256':hashlib.sha256(cert_raw).hexdigest(),'target':str(target.as_expr()),'multiplier_terms':sum(len(m) for m in multipliers),'all_nine_inputs_independently_reconstructed':True,'cubic_factor_identity_exact':True,'polynomial_certificate_independently_multiplied':True}
 print(name,json.dumps(reports[name]),flush=True)
covered=0
for perm in permutations(range(3)):
 for pair in combinations(range(3),2):
  found=False
  for relabel in permutations(range(3)):
   inverse=[relabel.index(i) for i in range(3)]
   transformed=[relabel[perm[inverse[i]]] for i in range(3)]
   transformed_pair=sorted(relabel[i] for i in pair)
   if any(transformed==case['permutation'] and transformed_pair==case['independent_r_coordinate_pair'] for case in systems['cases']):found=True
  assert found
  covered+=1
report={'status':'PASS','systems_sha256':hashlib.sha256(raw).hexdigest(),'cases':reports,'all_18_permutation_independent_pair_configurations_covered':covered,'coverage_argument':'Nonzero binary linear factors pair by unique factorization, giving U_i=lambda_i*r_perm(i) and product(lambda)=2. D=U-r has rank2, so r has rank2. Simultaneous coordinate permutations reduce all18 choices to these four cases; GL2 normalizes the selected independent forms. No D-rank or nonzero-third-form restriction is needed in the certified systems. Zero-factor boundary cases are separate.','scope':'Exact algebraic audit; no Lean proof of UFD coverage supplied here.','seconds':time.monotonic()-start}
(out/'Bzero-generic-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
