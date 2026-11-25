from pathlib import Path
from itertools import permutations
import sympy as S
import json,random
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
a,b,c,d,s,t=S.symbols('a b c d s t');variables=[a,b,c,d]
cases={
 'same':([0,s,t],[0,a*s+b*t,c*s+d*t]),
 'different01':([s,t,c*s+d*t],[0,-t,a*s+b*t]),
 'different02':([s,c*s+d*t,t],[0,-c*s-d*t,a*s+b*t]),
 'different12':([c*s+d*t,s,t],[0,-s,a*s+b*t]),
}
Q=S.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2
rng=random.Random(78231);report={}
for name,(D,r) in cases.items():
 D=list(map(S.sympify,D));r=list(map(S.sympify,r))
 q=-sum(r[i]**2+4*r[i]*D[i]+D[i]**2 for i in range(3))
 C=S.prod(r[i]+D[i] for i in range(3))-2*S.prod(r)
 assert S.expand(C)==0
 normD=sum(x*x for x in D);dot=sum(D[i]*r[i] for i in range(3))
 Pm=(dot+normD/2)**2+sum(D[i]**2*r[i]**2 for i in range(3))/4-sum(D[i]**2*D[j]**2 for i in range(3) for j in range(i+1,3))/4
 Pf=Pm+q*q/16+q*(dot/2+normD/4)
 polys=[]
 for degree,expr in [(2,q),(4,Pm)]:
  binary=S.Poly(S.expand(expr),s,t)
  for j in range(degree+1):
   g=binary.coeff_monomial(s**(degree-j)*t**j)
   if g:polys.append(S.Poly(g,*variables).clear_denoms()[1].primitive()[1].as_expr())
 scales={2:set(),4:set()}
 for _ in range(3):
  point={x:rng.randrange(-2,3) for x in variables}
  DD=[x.subs(point) for x in D];rr=[x.subs(point) for x in r]
  v=[(rr[i]+DD[i])/2 for i in range(3)];o=[(DD[i]-rr[i])/2 for i in range(3)]
  Tp=S.Matrix([[0,v[0],v[1],v[2]],[v[0],0,o[2],o[1]],[v[1],o[2],0,o[0]],[v[2],o[1],o[0],0]])
  M=S.ones(4)+Q*Tp*Q.T
  actual=S.Poly(S.expand(sum(S.prod(M[i,j] for i,j in enumerate(perm)) for perm in permutations(range(4)))-24),s,t)
  for j in range(4):assert actual.coeff_monomial(s**(3-j)*t**j)==0
  for degree,expr in [(2,q),(4,Pf)]:
   expected=S.Poly(S.expand(expr.subs(point)),s,t)
   for j in range(degree+1):
    mon=s**(degree-j)*t**j;av=actual.coeff_monomial(mon);ev=expected.coeff_monomial(mon)
    if ev:scales[degree].add(av/ev)
    else:assert av==0
 assert all(x=={S.Integer(1)} for x in scales.values()),scales
 script='ring r=0,(a,b,c,d),dp;\noption(redSB);\nideal I='+','.join(str(x).replace('**','^') for x in polys)+';\nideal G=std(I);\nprint("BASIS_SIZE");size(G);print("DIMENSION");dim(G);print("BASIS");G;quit;\n'
 (base/f'Bzero-boundary-{name}.sing').write_text(script)
 report[name]={'variables':list(map(str,variables)),'D_forms':list(map(str,D)),'r_forms':list(map(str,r)),'generators':list(map(str,polys)),'generator_count':len(polys),'cubic_identically_zero':True,'direct_permanent_coefficients_checked':36,'actual_q_and_P_scales':{str(k):str(next(iter(v))) for k,v in scales.items()}}
(base/'Bzero-boundaries-manifest.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:{'generator_count':v['generator_count'],'D':v['D_forms'],'r':v['r_forms']} for k,v in report.items()}),flush=True)
