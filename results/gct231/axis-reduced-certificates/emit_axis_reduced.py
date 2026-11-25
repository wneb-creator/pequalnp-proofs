from pathlib import Path
from fractions import Fraction
import hashlib,json,math
out=Path(__file__).parent
def balanced(terms):
 if not terms:return '0'
 if len(terms)==1:return terms[0]
 k=len(terms)//2;return '('+balanced(terms[:k])+' + '+balanced(terms[k:])+')'
def polynomial(terms,names,scale=1):
 pieces=[]
 for mon,c in terms:
  coefficient=Fraction(c)*scale;assert coefficient.denominator==1;coefficient=int(coefficient)
  m=' * '.join(v if e==1 else v+' ^ '+str(e) for v,e in zip(names,mon) if e)
  if not m:piece=str(coefficient)
  elif coefficient==1:piece=m
  elif coefficient==-1:piece='-('+m+')'
  else:piece=str(coefficient)+' * '+m
  pieces.append('('+piece+')')
 return balanced(pieces)
ns='PEqualNP.Outside.L_gct_231_aux.AxisReduced'
lines=['import Mathlib.Basic.Complex.Basic','import Mathlib.Tactic.LinearCombination','import Mathlib.Tactic.NormNum','','namespace '+ns,'']
for case in ['equal','different']:
 data=json.loads((out/('axis-four-'+case+'-quotient-compressed-certificate.json')).read_text())
 names=data['variables'];D=int(data['integer_denominator']);indices=[i for i,p in enumerate(data['multipliers']) if p]
 lines+=['set_option maxRecDepth 4096 in','set_option maxHeartbeats 4000000 in','theorem '+case+'_chart_inconsistent ('+' '.join(names)+' : ℂ)']
 lines+=['    (h'+str(i)+' : ('+polynomial(data['generators'][i],names)+' : ℂ) = 0)' for i in indices]
 lines+=['    : False := by','  have h : ('+str(D)+' : ℂ) = 0 := by',
         '    linear_combination '+balanced(['('+polynomial(data['multipliers'][i],names,D)+') * h'+str(i) for i in indices]),
         '  norm_num at h','']
lines+=['end '+ns,''];text='\n'.join(lines)
source=out/'AxisReducedCertificates.lean';source.write_text(text)
(out/'AxisReducedAudit.lean').write_text(text+'\n#print axioms '+ns+'.equal_chart_inconsistent\n#print axioms '+ns+'.different_chart_inconsistent\n')
print('source_bytes',source.stat().st_size,'lines',len(text.splitlines()),'sha256',hashlib.sha256(source.read_bytes()).hexdigest())
