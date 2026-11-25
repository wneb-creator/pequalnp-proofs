from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sympy as s
b=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
f=b/'c4-case3-modular-coprime-p11.json';d=json.loads(f.read_text());P=s.Symbol('P');poly=lambda t:s.Poly(s.sympify(t,locals={'P':P,'beta':P}),P,domain=s.ZZ);source=b/'c4-case3-radical-bezout-inputs.json';assert d['source_sha256']==sha(source)=='875a0d1669ea37eae733201b563ad8296198f4445ee680f3c469f3f3218350d7';rows=json.loads(source.read_text())
ps={k:poly(d[k]) for k in ['original_f','original_g','mod_f','mod_g','mod_a','mod_b','integer_quotient']}
assert ps['original_f']==poly(rows[0]['radical_other']) and ps['original_g']==poly(rows[1]['radical_other'])
assert d['prime']==11 and s.isprime(11) and d['degrees']==[67,85,67,85]
for original,mod,degree in [('original_f','mod_f',67),('original_g','mod_g',85)]:
 assert ps[original].degree()==ps[mod].degree()==degree and ps[original].set_modulus(11)==ps[mod].set_modulus(11)
 assert all(0<=int(v)<11 for v in ps[mod].all_coeffs()) and int(ps[mod].LC())%11!=0
for name in ['mod_a','mod_b']:assert all(0<=int(v)<11 for v in ps[name].all_coeffs())
assert (ps['mod_a']*ps['mod_f']+ps['mod_b']*ps['mod_g']-s.Poly(1,P)-11*ps['integer_quotient']).is_zero
print('Frozen reviewed originalradicals exactlypreserved, leastresidue maps mod11 and exact67/85degrees, nonzero leading residues',int(ps['mod_f'].LC()),int(ps['mod_g'].LC()),': PASS',flush=True)
print('Independent exactinteger identity AbarFbar+BbarGbar-1=11H: PASS; data SHA256',sha(f),flush=True)
print('Scope: modular coefficient/degrees/coprimality data only, to be used with separately checked resultant-transfer theorem. No unreviewed geometric or original-equation necessity claim.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
