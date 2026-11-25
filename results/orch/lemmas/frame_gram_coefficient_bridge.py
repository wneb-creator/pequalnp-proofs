from pathlib import Path
import sympy as s,json,itertools,resource,hashlib
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
job=Path('/tmp/oec/pequalnp-pilot-79');f=job/'four-frame-short-net.json';digest=hashlib.sha256(f.read_bytes()).hexdigest();model=json.loads(f.read_text());vv=s.symbols(' '.join(model['variables']));u01,u02,u03,u12,u13,u23,a,b,g,h,k=vv;x,y,z=s.symbols('x y z');scope=dict(zip(model['variables'],vv));scope.update(x=x,y=y,z=z,Matrix=s.Matrix);M=s.sympify(model['matrix'],locals=scope);eqs=[s.sympify(q,locals=scope) for q in model['equations']];P={}
for degree in [2,3,4]:P[degree]=s.Poly(s.expand(sum(s.prod(M[i,p[i]] for i in chosen) for p in itertools.permutations(range(4)) for chosen in itertools.combinations(range(4),degree))),x,y,z)
targets={'qB':(2,(0,2,0)),'cBA':(3,(1,2,0)),'cBC':(3,(0,2,1)),'pBA':(4,(2,2,0)),'pBC':(4,(0,2,2)),'pBAC':(4,(1,2,1))};out={};physical={}
for name,(degree,mon) in targets.items():
 q=P[degree].coeff_monomial(mon);physical[name]=q;pm=s.Poly(q,*vv);matches=[]
 for i,e in enumerate(eqs):
  pe=s.Poly(e,*vv)
  if pe.total_degree()!=degree:continue
  c=pm.LC()/pe.LC()
  if s.expand(q-c*e)==0:matches.append([i,str(c)])
 if matches:out[name]={'indices_scales':matches}
 else:
  # Quartic coefficient relations may require a short linear combination.
  inds=[i for i,e in enumerate(eqs) if s.Poly(e,*vv).total_degree()==degree];cs=s.symbols('cc:'+str(len(inds)));poly=s.Poly(s.expand(q-sum(c*eqs[i] for c,i in zip(cs,inds))),*vv);sol=s.solve(poly.coeffs(),cs,dict=True);assert len(sol)==1;out[name]={'indices_scales':[[i,str(sol[0][c])] for c,i in zip(cs,inds) if sol[0][c]]}
 assert s.expand(q-sum(s.Rational(c)*eqs[i] for i,c in out[name]['indices_scales']))==0
 gram=json.loads((job/'frame-gram-localized-model.json').read_text())
ps=[s.sympify(q,locals=scope) for q in gram['gram_pairings']];d=-b+h+k-2*u01+2*u03+2*u13
combinations=[physical['pBA']-g*physical['cBA']+g*g*physical['qB'],physical['pBC']-d*physical['cBC']+d*d*physical['qB'],(physical['pBAC']-g*physical['cBC']-d*physical['cBA']+2*g*d*physical['qB'])/2,physical['qB']/2]
assert all(s.expand(a-b)==0 for a,b in zip(ps,combinations));assert hashlib.sha256(f.read_bytes()).hexdigest()==digest
out.update(source_sha256=digest,classification='Exact polynomial identities in original homogeneous frame coordinates; source indices are zero-based',gram_pairings_as_physical_coefficients=['pBA-g*cBA+g^2*qB','pBC-d*cBC+d^2*qB','(pBAC-g*cBC-d*cBA+2*g*d*qB)/2','qB/2']);(job/'frame-gram-coefficient-bridge.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
