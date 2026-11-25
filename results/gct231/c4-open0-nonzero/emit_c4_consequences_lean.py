import argparse
import json
from fractions import Fraction
from pathlib import Path
from collections import defaultdict

p=argparse.ArgumentParser(description='Emit compact local polynomial consequences for a replayed exact certificate.')
p.add_argument('certificate');p.add_argument('output');p.add_argument('--case',type=int,choices=(0,1),required=True);p.add_argument('--theorem',default='rowzero_even_trace')
a=p.parse_args()
d=json.loads(Path(a.certificate).read_text())
names=d['variables'];assert len(names)==2
steps={s['index']:s for s in d['steps']}
sign=1 if a.case==0 else -1
target1={(2,0):Fraction(1),(1,1):Fraction(2*sign),(0,2):Fraction(1)}
target2={(0,4):Fraction(1),(0,3):Fraction(-2*sign),(0,2):Fraction(-1),(0,1):Fraction(2*sign),(0,0):Fraction(1)}
def find_target(wanted):
    matches=[idx for idx,step in steps.items() if {tuple(mon):Fraction(c) for mon,c in step['polynomial']}==wanted]
    assert matches,wanted
    return matches[0]
t1,t2=find_target(target1),find_target(target2)
needed=set()
def visit(idx):
    if idx in needed:return
    needed.add(idx)
    for parent,mon,c in steps[idx]['parents']:visit(parent)
visit(t1);visit(t2)

def rational(q):
 q=Fraction(q)
 if q.denominator==1:return str(q.numerator)
 return '('+str(q.numerator)+' / '+str(q.denominator)+' : ℂ)'
def monomial(exponents):
 pieces=[v if e==1 else v+' ^ '+str(e) for v,e in zip(names,exponents) if e]
 return ' * '.join(pieces) or '1'
def balanced_sum(pieces):
 if not pieces:return '0'
 if len(pieces)==1:return pieces[0]
 middle=len(pieces)//2
 return '('+balanced_sum(pieces[:middle])+' + '+balanced_sum(pieces[middle:])+')'
def polynomial(terms):
 pieces=[]
 for mon,q in terms:
  q=Fraction(q);m=monomial(mon)
  if m=='1':term=rational(q)
  elif q==1:term=m
  elif q==-1:term='-('+m+')'
  else:term=rational(q)+' * '+m
  pieces.append('('+term+')')
 return balanced_sum(pieces)

out=['import PEqualNP.Defs','', 'set_option maxHeartbeats 4000000',
     'set_option maxRecDepth 4096','', 'namespace PEqualNP.Outside.L_gct_231.trace', '',
     'theorem '+a.theorem+' ('+' '.join(names)+' : ℂ)']
for idx in sorted(needed):
 step=steps[idx]
 if 'generator' in step['kind']:
  out.append('    (h'+str(idx)+' : ('+polynomial(step['polynomial'])+' : ℂ) = 0)')
out.append('    (h_open : '+names[0]+' ^ 2 + '+names[0]+' - 1 ≠ 0) : False := by')
for idx in sorted(needed):
 step=steps[idx]
 if 'generator' in step['kind']:continue
 out.append('  have h'+str(idx)+' : ('+polynomial(step['polynomial'])+' : ℂ) = 0 := by')
 terms=[];groups=defaultdict(list)
 for parent,mon,coeff in step['parents']:
  groups[parent].append((mon,coeff))
 for parent,coefficients in groups.items():
  terms.append('('+polynomial(coefficients)+') * h'+str(parent))
 out.append('    linear_combination '+balanced_sum(terms))
left,right=names
sum_expr=left+(' + ' if a.case==0 else ' - ')+right
quad_expr=right+' ^ 2'+(' - ' if a.case==0 else ' + ')+right+' - 1'
out.extend(['  have hs : '+sum_expr+' = 0 := by',
    '    have hz : ('+sum_expr+') * ('+sum_expr+') = 0 := by',
    '      convert h'+str(t1)+' using 1 <;> ring',
    '    rcases mul_eq_zero.mp hz with h | h <;> exact h',
    '  have hq : '+quad_expr+' = 0 := by',
    '    have hz : ('+quad_expr+') * ('+quad_expr+') = 0 := by',
    '      convert h'+str(t2)+' using 1 <;> ring',
    '    rcases mul_eq_zero.mp hz with h | h <;> exact h',
    '  apply h_open',
    '  linear_combination hq + ('+left+(' - ' if a.case==0 else ' + ')+right+' + 1) * hs',
    '', 'end PEqualNP.Outside.L_gct_231.trace',''])
text='\n'.join(out)
assert len(text.encode())<=512*1024, ('Lean proof exceeds512KiB',len(text.encode()))
Path(a.output).write_text(text)
print(json.dumps({'lean_bytes':len(text.encode()),'lean_lines':len(out),'needed_steps':len(needed)}))
