"""Necessary bivariate resultants for open nonzero-product C4 cases 0 and 1."""
from pathlib import Path
import json,time
import sympy as S
base=Path(__file__).parent
alpha,beta,gamma,u,v=S.symbols('alpha beta gamma u v');local={str(t):t for t in(alpha,beta,gamma,u,v)}
for case in (0,1):
 source=base/'fresh'/('c4-nonzero-square-'+str(case)+'.json');data=json.loads(source.read_text())
 polys=dict(zip(data['equation_labels'],[S.sympify(p,locals=local)for p in data['equations']]))
 det=S.together(S.sympify(data['det_W'],locals=local).subs(alpha,1/(beta*gamma))).as_numer_denom()[0]
 saturation=S.factor(beta*gamma*det)
 def primitive(p,variables=(beta,gamma,u,v)):
  p=S.Poly(S.together(p).as_numer_denom()[0],*variables,domain=S.QQ)
  if p.is_zero:return S.Integer(0)
  return p.clear_denoms()[1].primitive()[1].as_expr()
 def strip(p):
  p=primitive(p)
  if p==0:return p
  while True:
   common=S.gcd(p,saturation)
   if S.Poly(common,beta,gamma,u).total_degree()==0:return S.factor(p)
   p=S.cancel(p/common)
 eq={k:strip(p.subs(alpha,1/(beta*gamma))) for k,p in polys.items() if k!='square_cubic'}
 F=eq['normal_q'];R=eq['normal_R'];L=strip(eq['normal_L']/v)
 Q=S.Poly(eq['q_w'],v);C=S.Poly(eq['c_w'],v)
 assert set(k[0]for k,c in Q.terms())<={0,2};assert set(k[0]for k,c in C.terms())<={0,2}
 Q0=Q.coeff_monomial(1);Q2=Q.coeff_monomial(v*v);C0=C.coeff_monomial(1);C2=C.coeff_monomial(v*v)
 assert S.degree(R,u)<=1 and S.degree(L,u)<=1
 H=primitive(Q2*C0-C2*Q0)
 zero=[F,S.resultant(R,Q0,u),S.resultant(R,C0,u),S.resultant(Q0,C0,u)]
 nonzero=[F,S.resultant(R,L,u),S.resultant(R,H,u),S.resultant(L,H,u)]
 result={'source':str(source),'case':case,'variables':['beta','gamma'],'saturation_nonzero':str(saturation),'equations_before_resultants':{k:str(x)for k,x in dict(F=F,R=R,L=L,Q0=Q0,Q2=Q2,C0=C0,C2=C2,H=H).items()},'branches':{k:[str(strip(p))for p in eqs]for k,eqs in [('v_zero',zero),('v_nonzero',nonzero)]},'scope':'Only necessary equations on det_W != 0, beta*gamma != 0. Vanishing leading coefficients are not assumed away; resultants give an overapproximation.'}
 out=base/('c4-nonzero-bivariate-'+str(case)+'.json');out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'case':case,'saturation':str(saturation),'branches':result['branches']}),flush=True)
