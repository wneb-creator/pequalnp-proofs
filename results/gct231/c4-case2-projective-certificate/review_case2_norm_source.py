from pathlib import Path
import re,json,hashlib
import sympy as S
p=Path(__file__).parent; source=p/'C4Case2ProjectiveNorm.lean';s=source.read_text();d=json.loads((p/'c4-case2-projective-cofactors.json').read_text());c=json.loads((p/'c4-case2-projective-bezout.integer-certificate.json').read_text());P=S.Symbol('P')
def horner(s):
 s=s.strip()
 if re.fullmatch(r'-?\d+',s):return[int(s)]
 m=re.fullmatch(r'\((.*) \* P\s+([+-])\s+(\d+)\)',s);assert m,s[:100]
 return[(1 if m[2]=='+' else -1)*int(m[3])]+horner(m[1])
ns=[s.split('(h'+str(i)+' : ',1)[1].split(' = 0)',1)[0] for i in[0,1]]
for actual,expected in zip(ns,d['norms']):
 poly=S.Poly(S.sympify(expected['norm'],locals={'P':P}),P,domain=S.QQ);assert all(x.q==1 for x in poly.all_coeffs());assert horner(actual)==[int(x) for x in reversed(poly.all_coeffs())]
a=s.split('linear_combination (',1)[1].split(') * h0 + (',1)[0];b=s.split(') * h0 + (',1)[1].split(') * h1',1)[0]
assert horner(a)==list(map(int,c['first_multiplier']));assert horner(b)==list(map(int,c['second_multiplier']))
scales=re.findall(r'\((\d+) : ℂ\)',s);assert scales==[c['scale'],c['scale']]
assert '((P+2)^2 * (P^4 - 2*P^3 + 4*P + 2)^14)' in s
assert '_root_' not in s and chr(34) not in s and '@[' not in s
print(json.dumps({'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'actual_Lean_norms_and_Bezout_coefficients':'PASS','scope':'only the two explicit norm equations imply a scalar disjunction'},indent=2))
