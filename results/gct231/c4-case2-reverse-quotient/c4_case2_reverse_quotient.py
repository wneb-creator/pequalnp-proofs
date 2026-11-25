from pathlib import Path
import json,time
import sympy as S
p=Path(__file__).parent;U,V,P,B=S.symbols('U V P B');loc={str(x):x for x in(U,V,P,B)}
d=json.loads((p/'c4-case2-resultants.json').read_text()); rows={x['label']:S.sympify(x['polynomial'],locals=loc) for x in d['reductions']};r=rows['linear_r']; q,c,l=[rows[x] for x in ['q','c','quadratic_l']]
vars3=(U,P,B);vars2=(P,B)
def poly3(x):return S.Poly(x,*vars3,domain=S.QQ)
def coeffU(f,k):return S.Poly.from_dict({(a,b):z for (u,a,b),z in f.terms() if u==k},*vars2,domain=S.QQ)
b=poly3(S.diff(r,V));d0=poly3(r.subs(V,0));b2=coeffU(b,0)
start=time.monotonic();first={}
for name,f in [('q',q),('c',c),('l',l)]:
 fV=S.Poly(f,V);degree=fV.degree();out=poly3(0)
 for (k,),coef in fV.terms():out += poly3(coef)*(-d0)**k*b**(degree-k)
 first[name]=out;print('first',name,'degree',out.degree(U),'terms',len(out.terms()),time.monotonic()-start,flush=True)
A,BB,C=[coeffU(first['q'],i) for i in[2,1,0]]
D,E,F=[coeffU(first['l'],i) for i in[2,1,0]]
ql=(A*F-C*D)**2-(A*E-BB*D)*(BB*F-C*E)
D,E,F,G=[coeffU(first['c'],i) for i in[3,2,1,0]]
qc=A**3*G**2-A**2*BB*F*G-2*A**2*C*E*G+A**2*C*F**2+A*BB**2*E*G+3*A*BB*C*D*G-A*BB*C*E*F-2*A*C**2*D*F+A*C**2*E**2-BB**3*D*G+BB**2*C*D*F-BB*C**2*D*E+C**3*D**2
for name,raw,power,source in [('ql',ql,4,'c4-case2-projective-resultants.json'),('qc',qc,6,'c4-case2-projective-resultants-qc.json')]:
 quotient=raw.exquo(b2**power);expected=S.Poly(S.sympify(json.loads((p/source).read_text())[0]['quotient'],locals=loc),*vars2,domain=S.QQ)
 sign=1 if quotient==expected else -1 if quotient==-expected else 0
 assert sign!=0
 row={'pair':name,'reverse_quotient':str(quotient.as_expr()),'reverse_slope':str(b2.as_expr()),'power':power,'forward_file':source,'sign_relative_to_forward':sign,'terms':len(quotient.terms())}
 (p/('c4-case2-reverse-quotient-'+name+'.json')).write_text(json.dumps(row,indent=2)+'\n')
 print('REVERSE_EQUALITY_PASS',name,sign,len(quotient.terms()),time.monotonic()-start,flush=True)
