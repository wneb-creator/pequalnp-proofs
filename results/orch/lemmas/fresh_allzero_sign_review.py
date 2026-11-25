from pathlib import Path
import json,hashlib,sympy as s,re
p=Path('AllZeroSignGluing.lean');src=p.read_text();st=json.loads(Path('root-AllZeroSignGluing-lean-3g-status.json').read_text());sha=hashlib.sha256(p.read_bytes()).hexdigest();assert st['sha256']==st['source_sha256_after']==sha and st['exit_code']==0
A,B,C,P,Q,h,x,y=s.symbols('A B C P Q h x y');eq=(A*x*x+B*x*y+C*y*y)**2-24*(P*x+Q*y)**4;proof=src.split('theorem binary_coefficients',1)[1].split('theorem binary_first',1)[0];ctx={}
for n,a,b in re.findall(r'have (h\w+) := H (\(?-?\d+\)?) (\(?-?\d+\)?)',proof):ctx[n]=eq.subs({x:int(a.strip('()')),y:int(b.strip('()'))})
forms=[A*A-24*P**4,2*A*B-96*P**3*Q,B*B+2*A*C-144*P*P*Q*Q,C*C-24*Q**4]
for goal,line in zip(forms,re.findall(r'linear_combination (.*)$',proof,re.M)):assert s.expand(goal-s.sympify(line.replace(': ℂ',''),locals=ctx))==0
assert 'anchored_glue C B A F E D r q p h hh hr Hzy Hzx Hyx' in src and 'anchored_glue B A C D F E q p r h hh hq Hyx Hyz Hxz' in src
assert all('have h'+n+' : '+n+' = 0 := by simpa' in src for n in 'ABC')
print('PASS. Four actual binary coefficient extractions agree identically. Nonzero-anchor sign, both incident pair coefficients, zero-endpoint mixed term, all-zero case and other-coordinate permutations independently reviewed. Final direct simpa at three zero-axis reductions. SHA',sha,'Lean exit0',st['seconds'],'s.')
