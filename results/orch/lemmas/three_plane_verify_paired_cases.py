from pathlib import Path
import json,itertools,resource,time,sympy as s
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
job=Path('/tmp/oec/pequalnp-pilot-79');start=time.monotonic();payload=json.loads((job/'four-frame-short-net.json').read_text());vv=s.symbols(' '.join(payload['variables']));u01,u02,u03,u12,u13,u23,a,b,g,h,k=vv;scope=dict(zip(payload['variables'],vv));x,y,z,r=s.symbols('x y z r');scope['r']=r
c=-g-h-2*(u12+u13+u23);d=-b+h+k-2*(u01-u03-u13);e=-a-k-2*(u02+u03-u23)
T=[[a*y+b*z,u01*z,u02*y,u03*(y-z)],[u01*z,g*x+d*z,u12*x,u13*(x-z)],[u02*y,u12*x,c*x+e*y,u23*(x-y)],[u03*(y-z),u13*(x-z),u23*(x-y),h*(x-z)+k*(y-z)]]
assert s.expand(sum(sum(row) for row in T))==0
# The second permanent coefficient is independently expanded from all24permutations.
physical_q=s.expand(sum(T[i][perm[i]]*T[j][perm[j]] for perm in itertools.permutations(range(4)) for i,j in itertools.combinations(range(4),2)))
physical=s.Poly(physical_q,x,y,z).coeffs();original=[s.sympify(q,locals=scope) for q in payload['equations'] if s.Poly(s.sympify(q,locals=scope),*vv).total_degree()==2]
assert len(physical)==len(original)==6
normalize=lambda f:s.Poly(f,*vv,domain=s.QQ).monic().as_expr()
assert {normalize(q) for q in physical}=={normalize(q) for q in original}
modroot=lambda f:s.rem(s.expand(f),r*r-2,r)
certificates=json.loads((job/'frame-paired-exact-certificates.json').read_text());results=[]
for item in certificates['cases']:
 case=item['case'];sign1,sign2,sign3=case['signs'];assert sign1==1 and sign2 in (-1,1) and sign3 in (-1,1)
 variables=s.symbols(' '.join(case['variables']));local=dict(scope);local.update(zip(case['variables'],variables));subs={scope[name]:s.sympify(value,locals=local) for name,value in case['substitutions'].items()};elimvar=scope[case['eliminated']];elimination=s.sympify(case['elimination'],locals=local);linear=s.sympify(case['linear'],locals=local)
 assert modroot(linear.subs(elimvar,elimination))==0
 allsubs={v:modroot(q.subs(elimvar,elimination)) for v,q in subs.items()};allsubs[elimvar]=elimination
 for value,wanted in [(a,(-4+2*r)*(u02+u03)),(g,(-4-2*r)*(u12+u13)),(b,(-4+2*sign2*r)*(1-u03)),(c,(-4-2*sign2*r)*(u12+u23)),(d,(-4+2*sign3*r)*(1-u13)),(e,(-4-2*sign3*r)*(u02-u23))]:
  assert modroot((value-wanted).subs(allsubs,simultaneous=True))==0
 qs=[s.sympify(q,locals=local) for q in case['quadratics']]
 for q,source in zip(qs,original):assert modroot(source.subs(allsubs,simultaneous=True)-q)==0
 # Independent dictionary convolution over QQ[r]/(r²−2), without using the certificate solver.
 qterms=[s.Poly(q,*variables,r,domain=s.QQ).terms() for q in qs];total={}
 for entry in item['certificate']:
  qi,mult,parity=entry['origin'];assert 0<=qi<6 and len(mult)==4 and all(isinstance(n,int) and n>=0 for n in mult) and parity in (0,1);weight=s.Rational(entry['numerator'],entry['denominator'])
  for mon,coefficient in qterms[qi]:
   rpow=mon[-1]+parity;key=tuple(i+j for i,j in zip(mon[:-1],mult))+(rpow%2,);total[key]=total.get(key,0)+weight*coefficient*2**(rpow//2)
 total={m:c for m,c in total.items() if c};assert total=={(0,0,0,0,0):s.Integer(1)}
 results.append({'signs':case['signs'],'physical_permanent_quadratic_source_verified':True,'all_six_root_substitutions_verified':True,'original_quadratics_after_substitution_verified':True,'exact_certificate_verified':True,'support':len(item['certificate'])})
assert {tuple(d['signs']) for d in results}=={(1,a,b) for a in (-1,1) for b in (-1,1)}
summary={'classification':'Independent exact algebra verification of conditional paired-root cases; does not establish the two base cubic implications','cases':results,'seconds':time.monotonic()-start};(job/'three-plane-paired-cases-independent-verification.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
