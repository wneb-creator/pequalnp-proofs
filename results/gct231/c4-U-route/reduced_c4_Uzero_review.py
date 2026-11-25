from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
import sympy as s
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
certpath=root/'reduced-c4-Uzero-classify.json'
cert=json.loads(certpath.read_text())
print('Classification source SHA256',sha(root/'reduced_c4_Uzero_classify.py'),flush=True)
print('Classification certificate SHA256',sha(certpath),flush=True)
for case in (2,3):
 path=root/'fresh'/f'c4-nonzero-reduced-{case}.json'
 print('CASE',case,'source SHA256',sha(path),flush=True)
 data=json.loads(path.read_text());vs=s.symbols(data['variables']);loc=dict(zip(data['variables'],vs))
 e=[s.sympify(t,locals=loc) for t in data['equations']]
 U=loc['U'];V=loc['V'];sat=loc['sat'];ez=[s.expand(x.subs(U,0)) for x in e]
 if case==2:
  P=loc['P'];B=loc['B']
  f,g=ez[:2]
  # Compute the 2x2 Sylvester determinant directly; both are linear in B.
  syl=s.expand(f.coeff(B)*g.subs(B,0)-f.subs(B,0)*g.coeff(B))
  target=-3*V**2*(V-6)**2*(V+2)
  assert s.expand(syl-target)==0
  assert s.expand(s.sympify(cert['case2_resultant'],locals=loc)-target)==0
  assert f.subs(V,0)==36*B
  assert s.expand(ez[5].subs(B,0)+1)==0
  print('CASE2 V=0 forces B=0 and contradicts saturation; remaining V=-2 or6',flush=True)
  assert s.expand(f.subs(V,-2)-48*(B-s.Rational(1,3)))==0
  assert s.expand(f.subs(V,6)-144*(B-1))==0
  for item in cert['case2_bezout']:
   sub={B:s.sympify(item['B']),V:s.sympify(item['V'])}
   polys=[ez[i].subs(sub).expand() for i in item['indices']]
   saved=[s.sympify(x,locals=loc) for x in item['polynomials']]
   assert all(s.expand(x-y)==0 for x,y in zip(polys,saved))
   mul=[s.sympify(x,locals=loc) for x in item['multipliers']]
   conclusion=s.sympify(item['conclusion'],locals=loc)
   assert s.expand(sum(x*y for x,y in zip(mul,polys))-conclusion)==0
   assert conclusion==(1 if sub[V]==-2 else P+2)
  point={P:-2,B:1,U:0,V:6,sat:s.Rational(-1,26)}
  assert s.expand(ez[5].subs({P:-2,B:1,V:6})-(-26*sat-1))==0
  print('CASE2 saved exact Bezout identities verified: V=-2 impossible; V=6 gives P=-2; sat=-1/26',flush=True)
 else:
  A=loc['A'];beta=loc['beta']
  assert ez[0].subs(V,0)==18*A
  assert s.expand(ez[5].subs(A,0)+1)==0
  assert s.expand(ez[1]+2*ez[0]+6*V**2*(2*beta-1)**2)==0
  print('CASE3 V=0 contradicts saturation; e1+2e0=-6V^2(2beta-1)^2 forces beta=1/2',flush=True)
  sub={beta:s.Rational(1,2)}
  assert s.expand(ez[2].subs(sub)+(A-4)*(4*A-3)/8)==0
  assert s.expand(ez[5].subs(sub)-(A*(4*A-3)*sat/4-1))==0
  assert s.expand(ez[5].subs({beta:s.Rational(1,2),A:s.Rational(3,4)})+1)==0
  line=s.expand(ez[3].subs({beta:s.Rational(1,2),A:4}))
  assert s.expand(line-s.Rational(169,8)*(V+12))==0
  assert s.expand(line-s.sympify(cert['case3_final_linear'],locals=loc))==0
  assert s.expand(ez[5].subs({beta:s.Rational(1,2),A:4})-(13*sat-1))==0
  point={A:4,beta:s.Rational(1,2),U:0,V:-12,sat:s.Rational(1,13)}
  print('CASE3 beta=1/2 gives (A-4)(4A-3)=0; saturation excludes A=3/4; final line gives V=-12 and sat=1/13',flush=True)
 assert all(s.expand(x.subs(point))==0 for x in e)
 print('CASE',case,'unique conditional point satisfies all six original equations: PASS',flush=True)
print('This classifies complex solutions only under U=0. No proof of U=0, no solver rerun.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
