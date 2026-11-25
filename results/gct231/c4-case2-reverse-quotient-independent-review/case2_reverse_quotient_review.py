from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,resource,time
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(90,90));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
import sympy as s
base=Path('/workspace/pequalnp-proofs/results/gct231/c4-case2-reverse-quotient');root=Path('/tmp/oec/pequalnp-pilot-75/gct231');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
man=base/'SHA256SUMS';assert sha(man)=='31b18334dcbc5406c680d9b663bc8dbfd06b8194771992c17bc9581a0d2729e5'
entries={line.split('  ',1)[1]:line.split('  ',1)[0] for line in man.read_text().splitlines()};files={p.name:p for p in base.iterdir() if p.is_file() and p!=man};assert entries.keys()==files.keys()
for name,h in entries.items():assert sha(base/name)==h
P,B,U,V=s.symbols('P B U V');loc={str(x):x for x in(P,B,U,V)}
d=json.loads((root/'c4-case2-resultants.json').read_text());ps={row['label']:s.sympify(row['polynomial'],locals=loc) for row in d['reductions']};r=ps['linear_r'];slope=s.diff(r,V);offset=r.subs(V,0)
# Verify the universal formula independently via a generic Sylvester resultant.
z=s.Symbol('z');a,b,c,d0,e,f,g=s.symbols('a b c d e f g');qc=s.resultant(a*z**2+b*z+c,d0*z**3+e*z**2+f*z+g,z);ql=s.resultant(a*z**2+b*z+c,d0*z**2+e*z+f,z)
cert=json.loads((base/'quadratic-cubic-resultant-certificate.json').read_text());big=s.symbols('A B C D E F G V');bigloc=dict(zip(['A','B','C','D','E','F','G','V'],big));a0,b0,c0,d1,e0,f0,g0,v=big
parse=lambda t:s.sympify(t,locals=bigloc)
assert s.expand(parse(cert['quadratic_multiplier'])*(a0*v**2+b0*v+c0)+parse(cert['cubic_multiplier'])*(d1*v**3+e0*v**2+f0*v+g0)-parse(cert['resultant']))==0
assert s.Poly(qc,a,b,c,d0,e,f,g).terms()==s.Poly(parse(cert['resultant']),a0,b0,c0,d1,e0,f0,g0).terms()
print('Generic quadratic/cubic Sylvester formula and complete polynomial Bezout identity: PASS',flush=True)
ring=lambda x:s.Poly(x,U,P,B,domain=s.QQ);slo=ring(slope);off=ring(offset);first={}
for name,key,degree in [('q','q',2),('l','quadratic_l',2),('c','c',3)]:
 fV=s.Poly(ps[key],V);assert fV.degree()==degree
 out=ring(0)
 for (k,),coef in fV.terms():out+=ring(coef)*(-off)**k*slo**(degree-k)
 first[name]=out
# Evaluate the independently computed generic determinant over QQ[P,B].
R=lambda x:s.Poly(x,P,B,domain=s.QQ)
def coeff(poly,k):return s.Poly.from_dict({(p,b):v for (u,p,b),v in poly.terms() if u==k},P,B,domain=s.QQ)
def evaluate(formula,variables,values):
 out=R(0)
 for mon,c in s.Poly(formula,*variables,domain=s.QQ).terms():
  term=R(c)
  for value,power in zip(values,mon):term*=value**power
  out+=term
 return out
slope2=R(slope)
for name,formula,varlist,other,degree,power,forwardname in [('ql',ql,[a,b,c,d0,e,f],'l',2,4,'c4-case2-projective-resultants.json'),('qc',qc,[a,b,c,d0,e,f,g],'c',3,6,'c4-case2-projective-resultants-qc.json')]:
 values=[coeff(first['q'],i) for i in [2,1,0]]+[coeff(first[other],i) for i in range(degree,-1,-1)]
 raw=evaluate(formula,varlist,values)
 row=json.loads((base/('c4-case2-reverse-quotient-'+name+'.json')).read_text());quot=R(s.sympify(row['reverse_quotient'],locals=loc));assert R(s.sympify(row['reverse_slope'],locals=loc))==slope2 and row['power']==power
 assert raw==slope2**power*quot
 forward=json.loads((base.parent/'c4-case2-projective-certificate'/forwardname).read_text())[0];assert quot==R(s.sympify(forward['quotient'],locals=loc)) and row['sign_relative_to_forward']==1
 print(name,'independent generic-determinant evaluation equals b^'+str(power)+' times saved quotient; forward quotient exactlyequal withsign+1: PASS',flush=True)
print('Scope: exact algebraic reverse quotient identities only. At b=0 they remain polynomial identities, but division/necessary normalized vanishing requires the separately established nonzero-slope chart. No Lean or complete gap result.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
