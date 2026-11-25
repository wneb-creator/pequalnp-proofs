from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sympy as s
base=Path(__file__).resolve().parent
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
P,B,U,V,sat=s.symbols('P B U V sat'); loc={str(x):x for x in(P,B,U,V,sat)}
parse=lambda x:s.sympify(x,locals=loc)
d=json.loads((base/'c4-case2-resultants.json').read_text()); src=json.loads((base/'fresh/c4-nonzero-reduced-2.json').read_text()); assert d['source']==src
F=parse(d['scale_curve']); es=list(map(parse,src['equations'])); assert s.expand(F-es[2])==0
K=P**2+P-1;Q=P**4-2*P**3+4*P+2;W=parse(src['det_W_numerator'])
assert s.expand(F-(K*(-6*B**2+(5*P**2-P+10)*B-8*P**2)-3*P*B))==0
assert s.expand(es[5]-(P*B*W*sat-1))==0
rows={e['label']:e for e in d['reductions']};r=parse(rows['linear_r']['polynomial']);a=s.diff(r,U);b=s.diff(r,V);r0=r.subs({U:0,V:0})
assert s.expand(r-a*U-b*V-r0)==0
assert s.expand(parse(rows['linear_r']['denominator'])-8*K**3)==0
rem=s.Poly(es[3],B,domain=s.QQ.frac_field(P,U,V)).rem(s.Poly(F,B,domain=s.QQ.frac_field(P,U,V))).as_expr()
assert s.cancel(rem-r/(8*K**3))==0
print('Exact source, F/saturation/K identity and original-r reduction by8K^3: PASS',flush=True)
f2=s.expand(F).coeff(B,2);f1=s.expand(F).coeff(B,1);f0=F.subs(B,0)
ns=json.loads((base/'c4-case2-leading-norms.json').read_text()); norms={}; cert={}
for label,g in [('rU',a),('rV',b),('r0',r0)]:
 g1=s.expand(g).coeff(B,1);g0=g.subs(B,0);N=s.expand(f2*g0**2-f1*g1*g0+f0*g1**2)
 assert s.expand(N-parse(ns[label]))==0
 assert s.expand(g1**2*F-g*(f2*g1*B+f1*g1-f2*g0)-N)==0
 norms[label]=N;cert[label]={'slope':str(g),'norm':str(s.factor(N)),'multiplier_F':str(g1**2),'multiplier_g':str(-(f2*g1*B+f1*g1-f2*g0))}
 print('Independent quadratic/linear Sylvester norm identity',label,'PASS',flush=True)
R=s.cancel(norms['rU']/(256*P**4*K**3*Q**2));S=s.cancel(norms['rV']/(64*P**3*K**3*Q**2))
hR,hS,gcd=s.gcdex(R,S,P);assert gcd==1 and s.expand(hR*R+hS*S)==1
cert['norm_coprime']={'R':str(R),'S':str(S),'bezout_R':str(hR),'bezout_S':str(hS)}
print('R13/S13 explicit Bezout identity =1: PASS; common norm factors imply Q=0 under P*K nonzero.',flush=True)
ad=json.loads((base/'c4-case2-affine-quartic.json').read_text());aff=3*B+P**3-2*P**2
for name,g in [('a',a),('b',b)]:
 A=parse(ad[name]['multiplier']); qq,rr=s.div(s.Poly(g-A*aff,P,domain=s.QQ[B]),s.Poly(Q,P,domain=s.QQ[B]));assert rr.is_zero
 assert s.expand(s.rem(s.Poly(g,P,domain=s.QQ[B]),s.Poly(Q,P,domain=s.QQ[B])).as_expr()-parse(ad[name]['remainder']))==0
 ha,hq,gg=s.gcdex(A,Q,P);assert gg==1 and s.expand(ha*A+hq*Q)==1
 cert[name+'_affine']={'multiplier':str(A),'quotient_by_Q':str(qq.as_expr()),'bezout_multiplier':str(ha),'bezout_Q':str(hq)}
 print(name,'mod Q and explicit multiplier/Q Bezout =1: PASS',flush=True)
quot,rem=s.div(s.Poly(W-P**2*Q,B,domain=s.QQ[P]),s.Poly(aff,B,domain=s.QQ[P]));assert rem.is_zero
cert['det_affine']={'identity':'W - P^2*Q = quotient * (3*B+P^3-2*P^2)','quotient':str(quot.as_expr())}
print('W=P^2*Q modulo affine relation: PASS',flush=True)
cert['source_hashes']={name:hashlib.sha256((base/name).read_bytes()).hexdigest() for name in ['fresh/c4-nonzero-reduced-2.json','c4-case2-resultants.json','c4-case2-leading-norms.json','c4-case2-affine-quartic.json']}
cert['scope']='Over C, F=0 and P*B*W nonzero imply a!=0 or b!=0 for the stated reduced slopes. No r=0 premise is needed. All norm identities valid at vanishing slope-leading coefficients. K!=0 follows from F and P*B!=0. No chart classification or Lean compilation claimed.'
(base/'c4-case2-slope-review-certificates.json').write_text(json.dumps(cert,indent=2)+'\n')
print(cert['scope'],flush=True)
print('Certificate prospects: quadratic-linear norm ring identities; univariate R13/S13 Bezout degree12; multiplier/Q Bezout degree3; affine determinant factorization.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
