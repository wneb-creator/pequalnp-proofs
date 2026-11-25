"""Emit an exact polynomial zero-system contradiction goal for Lean grind."""
import argparse
from pathlib import Path
import re
import sympy as sp

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('input');p.add_argument('output');p.add_argument('theorem')
p.add_argument('--ring-steps',type=int,default=1000000)
a=p.parse_args()
rows=Path(a.input).read_text().splitlines()
char,n,m=map(int,rows[0].split());names=rows[1].split()
assert char==0 and len(names)==n and len(rows)==m+2
assert all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',name) and '_root_' not in name for name in names)
vs=sp.symbols(' '.join(names),seq=True);locals_=dict(zip(names,vs))
def polynomial(text):
    terms=[]
    for exponents,c in sp.Poly(sp.sympify(text.replace('^','**'),locals=locals_),*vs,domain=sp.QQ).terms():
        assert c.q==1
        mon=' * '.join(name if e==1 else name+' ^ '+str(e) for name,e in zip(names,exponents) if e)
        terms.append('('+str(c)+((' * '+mon) if mon else '')+')')
    return ' + '.join(terms) or '0'
out=['import PEqualNP.Defs','','set_option maxHeartbeats 10000000',
     'set_option maxRecDepth 4096','','namespace PEqualNP.Outside.L_gct_231.grindCalibration','',
     'theorem '+a.theorem+' ('+' '.join(names)+' : ℂ)']
for idx,line in enumerate(rows[2:]):
    out.append('    (h'+str(idx)+' : ('+polynomial(line)+' : ℂ) = 0)')
out += ['    : False := by',
        '  grind (ringSteps := '+str(a.ring_steps)+') (ringMaxDegree := 20) (ematch := 0) (splits := 0) -linarith -lia',
        '','end PEqualNP.Outside.L_gct_231.grindCalibration','']
source='\n'.join(out)
Path(a.output).write_text(source)
Path(a.output).with_name(Path(a.output).stem+'Audit.lean').write_text(source+'\n#print axioms PEqualNP.Outside.L_gct_231.grindCalibration.'+a.theorem+'\n')
print('bytes',len(source.encode()),'hypotheses',m,'variables',n)
