import argparse
import json
from fractions import Fraction
from pathlib import Path
from collections import defaultdict

p=argparse.ArgumentParser(description='Emit compact local polynomial consequences for a replayed exact certificate.')
p.add_argument('certificate');p.add_argument('output');p.add_argument('--theorem',default='rowzero_even_trace')
a=p.parse_args()
d=json.loads(Path(a.certificate).read_text())
assert d['proved_nonzero_constant']
names=d['variables'];needed=set(d['needed_steps'])
steps={s['index']:s for s in d['steps']}

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
out.append('    : False := by')
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
out.extend(['  norm_num at h'+str(d['constant_step']),'','end PEqualNP.Outside.L_gct_231.trace',''])
text='\n'.join(out)
assert len(text.encode())<=512*1024, ('Lean proof exceeds512KiB',len(text.encode()))
Path(a.output).write_text(text)
print(json.dumps({'lean_bytes':len(text.encode()),'lean_lines':len(out),'needed_steps':len(needed)}))
