from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,sympy as s
base=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
old=base/'StarPencilClassification.first-corollary.lean';new=base/'StarPencilClassification.lean';assert sha(old)=='9cd27b8c23633b4efb7fa36f866a4f8b0633e43da64ba47b51f880928fef5fe9'
t=old.read_text()
for var in ['a','b']:
 before=f'  have h{var}1 : {var} + 1 = 0 := pow_eq_zero h{var}2'
 after=f'''  have h{var}1 : {var} + 1 = 0 := by
    have hh : ({var} + 1) * ({var} + 1) = 0 := by simpa only [pow_two] using h{var}2
    exact (mul_eq_zero.mp hh).elim id id'''
 assert t.count(before)==1;t=t.replace(before,after)
t=t.replace('zero_pow (by decide : 4 ≠ 0), zero_pow (by decide : 3 ≠ 0), ','').replace(', sub_zero, zero_add','')
assert t==new.read_text();print('Corrected star source differs only by exact pow_two/mul_eq_zero square-zero API proof and removal of unused simp arguments. All hypotheses, giant identity and theorem conclusions byte-preserved: PASS',flush=True)
p=base/'StandardStarTriangleExtension.lean';src=p.read_text();u,v,d,f=s.symbols('u v d f');loc={str(x):x for x in(u,v,d,f)}
rows={int(i):s.sympify(expr.replace('^','**'),locals=loc) for i,expr in re.findall(r'    \(h(\d+) : (.*?) = 0\)',src)};assert list(rows)==[5,10,13,16,19]
assert s.expand(-rows[13]-rows[19]-8*rows[5]-8*rows[16]+10*rows[10])==36
oldsrc=base.parent/'triangle_concept/triangle-twelve-equations.json';assert sha(oldsrc)=='03a8aa61b2a83e2918457d922059fb481128cc02b3d1532c2cfcc11677ed0ce7'
j=json.loads(oldsrc.read_text());vars=s.symbols(j['unknowns']);local=dict(zip(j['unknowns'],vars))
sub={local[n]:0 for n in ['d0','d1','d3','d7','o3','o7']};sub.update({local['o0']:-1,local['o1']:-1,local['d5']:u,local['d8']:v,local['o5']:d,local['o8']:f})
for i,got in rows.items():assert s.expand(s.sympify(j['equations'][i]['coefficient'],locals=local).subs(sub)-got)==0
print('All5 actual extension hypotheses exactly match reviewed triangle rows5/10/13/16/19 under standard-star substitution; independent combination gives36: PASS',flush=True)
print('Scope: scalar conditional extension contradiction for this normalized standard star. No general triangle or whole-gap assertion. No compiler run.',flush=True)
print('Hashes',json.dumps({p.name:sha(p) for p in [old,new,base/'StandardStarTriangleExtension.lean']}),flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
