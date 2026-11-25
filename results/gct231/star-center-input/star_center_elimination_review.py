from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction
import hashlib,json
import sympy as s
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
source=root/'star-full-grouped-equations.json';target=root/'star-full-center-eliminated-equations.json'
assert sha(source)=='a6a49ab3dab78f0c32da78838e91b0e1d3e722406d0607ee1bcc265d62790722'
assert sha(target)=='845a45f7e3374b691dc8ef76eacf59938118b7961360c99d09505559c2e39f17'
a=json.loads(source.read_text());d=json.loads(target.read_text())
assert d['source_sha256']==sha(source)
assert d['pivots']==a['pivots']==[[0,1],[0,2],[0,3]] and d['remaining']==a['remaining']==[[1,2],[1,3],[2,3]]
x,y,z=s.symbols('x y z');n=s.symbols('n0:3')
old={name:s.Symbol(name) for name in a['unknowns']};loc={**old,**{str(v):v for v in n},'x':x,'y':y,'z':z}
groups=[[f'd{i+3}',f'd{i+6}',f'n{i}',f'o{i}',f'o{i+3}',f'o{i+6}'] for i in range(3)]
assert d['basis_direction_groups']==groups and d['unknowns']==sum(groups,[])
variables=[loc[name] for name in d['unknowns']]
forward={old[f'd{i}']:-(n[i]+old[f'd{i+3}']+old[f'd{i+6}']+2*(1+old[f'o{i}']+old[f'o{i+3}']+old[f'o{i+6}'])) for i in range(3)}
inverse={n[i]:-(old[f'd{i}']+old[f'd{i+3}']+old[f'd{i+6}']+2*(1+old[f'o{i}']+old[f'o{i+3}']+old[f'o{i+6}'])) for i in range(3)}
for key,value in forward.items():
 assert s.expand(value-s.sympify(d['forward_substitution'][str(key)],locals=loc))==0
 assert s.expand(value.subs(inverse,simultaneous=True)-key)==0
for key,value in inverse.items():
 assert s.expand(value-s.sympify(d['inverse_substitution'][str(key)],locals=loc))==0
 assert s.expand(value.subs(forward,simultaneous=True)-key)==0
M=s.Matrix([[s.sympify(t,locals=loc) for t in row] for row in d['matrix']])
oldM=s.Matrix([[s.sympify(t,locals=loc) for t in row] for row in a['matrix']])
for i in range(4):
 for j in range(4):
  assert s.expand(oldM[i,j].subs(forward,simultaneous=True)-M[i,j])==0
  assert s.expand(M[i,j].subs(inverse,simultaneous=True)-oldM[i,j])==0
assert M==M.T and s.expand(sum(M))==0
assert s.expand(M[3,3]-(n[0]*x+n[1]*y+n[2]*z))==0
assert [M[0,j] for j in (1,2,3)]==[x,y,z]
print('Affine substitution and inverse, all 16 entries both directions, tangent, symmetry, three pivots, and free diagonal33: PASS',flush=True)
polys=[]
for oldentry,newentry in zip(a['equations'],d['equations']):
 assert oldentry['monomial']==newentry['monomial']
 before=s.sympify(oldentry['coefficient'],locals=loc);after=s.sympify(newentry['coefficient'],locals=loc)
 assert s.expand(before.subs(forward,simultaneous=True)-after)==0
 assert s.expand(after.subs(inverse,simultaneous=True)-before)==0
 polys.append(s.Poly(after,*variables,domain=s.QQ))
assert len(polys)==31 and sum(len(p.terms()) for p in polys)==3600
print('All 31 coefficient equations independently match forward and inverse substitutions: PASS; 3600 terms',flush=True)
# Independent permanent implementation: Ryser in the complete polynomial ring.
allvars=(x,y,z,*variables);zero=s.Poly(0,*allvars,domain=s.QQ);one=s.Poly(1,*allvars,domain=s.QQ)
rows=[[s.Poly(1+M[i,j],*allvars,domain=s.QQ) for j in range(4)] for i in range(4)]
per=zero
for mask in range(1,16):
 term=one
 for i in range(4):term*=sum((rows[i][j] for j in range(4) if mask>>j&1),zero)
 per+=(-1)**(4-mask.bit_count())*term
per-=24
coefs={}
for powers,coefficient in per.terms():
 abc=powers[:3];param=powers[3:]
 coefs.setdefault(abc,{})[param]=coefficient
assert all(2<=sum(m)<=4 for m in coefs) and len(coefs)==31
for entry,poly in zip(d['equations'],polys):
 mon=tuple(entry['monomial']);assert coefs.pop(mon)==dict(poly.terms())
assert not coefs
print('Independent Ryser permanent yields exactly all 31 exported coefficients, with zero constant/linear residues: PASS',flush=True)
for label,characteristic in [('qq',0),('p1009',1009)]:
 inp=root/f'neogb-star-full-center-{label}.in';prov=json.loads((root/f'neogb-star-full-center-{label}.provenance.json').read_text())
 assert prov['source_sha256']==sha(target) and prov['input_sha256']==sha(inp)
 assert prov['variables']==d['unknowns'] and prov['characteristic']==characteristic
 tokens=list(map(int,inp.read_text().split()));nv,m,p,total=tokens[:4]
 assert (nv,m,p,total)==(18,31,characteristic,3600)
 lengths=tokens[4:35];assert sum(lengths)==total;pos=35
 for i,(length,poly) in enumerate(zip(lengths,polys)):
  got={}
  for _ in range(length):
   num,den=tokens[pos:pos+2];mon=tuple(tokens[pos+2:pos+20]);pos+=20
   assert den>0 and all(e>=0 for e in mon) and mon not in got
   got[mon]=Fraction(num,den) if p==0 else num*pow(den,-1,p)%p
  denominator,integral=poly.clear_denoms();content,primitive=integral.primitive()
  scale=prov['equation_scalings'][i]
  assert s.Rational(scale['denominator'])/s.Rational(scale['content'])==denominator/content
  want={mon:Fraction(int(c.p),int(c.q)) for mon,c in primitive.terms()}
  if p:
   assert int(denominator)%p and int(content)%p
   want={mon:c.numerator*pow(c.denominator,-1,p)%p for mon,c in want.items()}
   want={mon:c for mon,c in want.items() if c}
  assert got==want,(label,i)
 assert pos==len(tokens)
 print(label,'actual sparse input independently reconstructed; SHA256',sha(inp),flush=True)
print('Scope: invertible affine reparameterization of the complete original full-star chart. No solver outcome or dimension reduction.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
