"""Independent symbolic lineage review of reduced C4 cases2/3; no solver."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,itertools
import sympy as s

base=Path(__file__).resolve().parent
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
e,f,a,b,H,X,Y=s.symbols('e f a b H X Y')
coords=(e,f,a,b,H,X,Y);zs=coords[1:]
alpha,beta,gamma,u,v,tt=s.symbols('alpha beta gamma u v t')
P,BB,AA,U,V,sat=s.symbols('P B A U V sat')
local_symbols={str(z):z for z in [*coords,alpha,beta,gamma,u,v,tt,P,BB,AA,U,V,sat]}
parse=lambda value:s.sympify(value,locals=local_symbols)
q=6*e**2+2*f**2+a**2+b**2-H**2-X**2-Y**2-X*(a+b)+Y*(b-a)
c=2*f*a*b-2*H*X*Y+e*(-4*X**2-4*Y**2+4*X*(a+b)+4*Y*(a-b)-a*a-b*b+4*f*f)-4*e**3
G=s.hessian(q,zs)/2
assert G.det()!=0
perms=list(itertools.permutations((f,a,b)))
retained=(1,2,3,5,6)
for case in (2,3):
 original_path=base/f'c4-nonzero-square-{case}.json'
 reduced_path=base/f'c4-nonzero-reduced-{case}.json'
 original=json.loads(original_path.read_text());reduced=json.loads(reduced_path.read_text())
 perm=perms[case]
 assert original['permutation']==list(map(str,perm))
 assert original['variables']==['alpha','beta','gamma','u','v']
 assert original['equation_labels']==['product_scales','q_w','c_w','normal_q','square_cubic','normal_R','normal_L']
 n1=s.Matrix([s.diff(H-alpha*perm[0],z) for z in zs])
 n2=s.Matrix([s.diff(X-beta*perm[1],z) for z in zs])
 w=G.inv()*(u*n1+v*n2)
 assert all(s.expand(w[i]-parse(original['w'][str(z)]))==0 for i,z in enumerate(zs))
 assert parse(original['w']['e'])==1
 free=(f,a,b,Y)
 ksub={H:alpha*perm[0],X:beta*perm[1]}
 k=s.Matrix([ksub.get(z,z) for z in zs])
 basis=k.jacobian(free)
 GW=basis.T*G*basis
 assert (basis.T*G*w).applyfunc(s.expand)==s.zeros(4,1)
 assert (GW-s.Matrix([[parse(entry) for entry in row] for row in original['gram_W']])).applyfunc(s.expand)==s.zeros(4)
 detW=s.factor(GW.det())
 assert s.expand(detW-parse(original['det_W']))==0
 wsub={e:1,**dict(zip(zs,w))}
 qw=s.expand(q.subs(wsub,simultaneous=True));cw=s.expand(c.subs(wsub,simultaneous=True))
 # Recompute both mixed coefficients by direct substitution into the cubic.
 linear_family={e:tt,**{z:k[i]+tt*w[i] for i,z in enumerate(zs)}}
 pol=s.Poly(s.expand(c.subs(linear_family,simultaneous=True)),tt)
 R=pol.nth(1);L=pol.nth(2)
 GR=s.hessian(R,free)/2
 assert (GR-s.Matrix([[parse(entry) for entry in row] for row in original['gram_R']])).applyfunc(s.expand)==s.zeros(4)
 ell=Y-gamma*perm[2]
 normal=s.Matrix([s.diff(ell,z) for z in free])
 assert normal==s.Matrix([parse(entry) for entry in original['normal']])
 nv=GW.adjugate()*normal
 nq=s.expand((normal.T*nv)[0])
 nr=s.expand((nv.T*GR*nv)[0])
 nl=s.expand(L.subs(dict(zip(free,nv)),simultaneous=True))
 checks={1:qw,2:cw,3:nq,5:nr,6:nl}
 for index,expected in checks.items():
  assert s.expand(parse(original['equations'][index])-expected)==0,(case,index)
 assert s.expand(parse(original['equations'][0])-(alpha*beta*gamma-1))==0
 print('CASE',case,'original necessary equations independently reproduced',flush=True)

 if case==2:
  substitution={alpha:P/beta,gamma:1/P,u:U,v:V/beta}
  lift={BB:beta**2};expected_vars=['P','B','U','V','sat']
  saturation_factor=P*BB
  original_den_vars=(P,beta)
 else:
  substitution={gamma:1/(alpha*beta),u:U,v:V/alpha}
  lift={AA:alpha**2};expected_vars=['A','beta','U','V','sat']
  saturation_factor=AA*beta
  original_den_vars=(alpha,beta)
 assert reduced['variables']==expected_vars and len(reduced['equations'])==6
 assert reduced['original_case']==case
 assert all(parse(reduced['substitution'][str(k)])==val for k,val in substitution.items())
 assert s.cancel((alpha*beta*gamma-1).subs(substitution,simultaneous=True))==0
 for new_index,old_index in enumerate(retained):
  den=parse(reduced['discarded_denominators'][new_index])
  denpoly=s.Poly(den,*original_den_vars)
  assert len(denpoly.terms())==1 and denpoly.terms()[0][1]!=0
  assert int(denpoly.terms()[0][1])%1009!=0
  old=parse(original['equations'][old_index]).subs(substitution,simultaneous=True)
  new=parse(reduced['equations'][new_index]).subs(lift)
  assert s.cancel(old*den-new)==0,(case,new_index)
 detnum=parse(reduced['det_W_numerator'])
 detden=parse(reduced['det_W_denominator'])
 assert s.cancel(detW.subs(substitution,simultaneous=True)*detden-detnum.subs(lift))==0
 assert s.expand(parse(reduced['equations'][-1])-(sat*saturation_factor*detnum-1))==0
 variables=list(map(s.Symbol,expected_vars))
 terms=sum(len(s.Poly(parse(eq),*variables).terms()) for eq in reduced['equations'])
 assert terms==(134 if case==2 else 132)
 assert all(s.Poly(parse(eq),*variables).domain.is_ZZ for eq in reduced['equations'])
 print('CASE',case,'reduced substitutions, monomial denominators, variable/equation order, saturation, term count',terms,'PASS',flush=True)
 print('ORIGINAL_SHA256',case,hashlib.sha256(original_path.read_bytes()).hexdigest(),flush=True)
 print('REDUCED_SHA256',case,hashlib.sha256(reduced_path.read_bytes()).hexdigest(),flush=True)

symmetry={e:-e,f:-f,a:b,b:a,H:H,X:X,Y:-Y}
assert s.expand(q.subs(symmetry,simultaneous=True)-q)==0
assert s.expand(c.subs(symmetry,simultaneous=True)+c)==0
print('S:(e,f,a,b,H,X,Y)->(-e,-f,b,a,H,X,-Y) preserves q and negates c: PASS',flush=True)
print('Case2 maps to4 with scales(alpha,-beta,-gamma); case3 maps to5 with unchanged scales',flush=True)
print('Scope: necessary systems conditional on nonzero scales and nondegenerateW; no degenerateW coverage, no solver verdict',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
