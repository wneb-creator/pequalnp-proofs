from pathlib import Path
import json,sympy as s,math
job=Path('/tmp/oec/pequalnp-pilot-79');data=json.loads((job/'frame-paired-exact-certificates.json').read_text());r=s.Symbol('r');text=['import Mathlib.Basic.Complex.Basic','import Mathlib.Tactic.LinearCombination','','namespace PEqualNP.Outside.L_gct_231_aux.FramePairedCases',''];checks=[]
def lean(expr):return str(s.expand(expr)).replace('**',' ^ ')
for number,entry in enumerate(data['cases']):
 case=entry['case'];variables=s.symbols(' '.join(case['variables']));scope=dict(zip(case['variables'],variables));scope['r']=r;qs=[s.sympify(q,locals=scope) for q in case['quadratics']];scales=[s.ilcm(*(s.denom(c) for c in s.Poly(q,*variables,r).coeffs())) for q in qs];scaled=[s.expand(q*d) for q,d in zip(qs,scales)];multipliers=[s.Integer(0)]*len(qs)
 for row in entry['certificate']:
  qi,m,power=row['origin'];c=s.Rational(row['numerator'],row['denominator'])/scales[qi];multipliers[qi]+=c*s.prod(v**e for v,e in zip(variables,m))*r**power
 denominator=s.ilcm(*(s.denom(c) for multiplier in multipliers for c in s.Poly(multiplier,*variables,r).coeffs()));multipliers=[s.expand(p*denominator) for p in multipliers];total=s.expand(sum(p*q for p,q in zip(multipliers,scaled))-denominator);quotient,remainder=s.div(total,r*r-2,r);assert remainder==0;assert all(c.q==1 for p in multipliers+[quotient] for c in s.Poly(p,*variables,r).coeffs());quotient=s.expand(quotient)
 checks.append({'case':number,'signs':case['signs'],'variables':case['variables'],'constant':str(denominator),'quadratics':[str(q) for q in scaled],'multipliers':[str(p) for p in multipliers],'root_multiplier':str(-quotient)})
 text.extend(['set_option maxRecDepth 2048 in','set_option maxHeartbeats 0 in',f'lemma case{number} (r '+ ' '.join(case['variables'])+' : ℂ)','    (hr : r ^ 2 = 2)'])
 for i,q in enumerate(scaled):text.append('    (h'+str(i)+' : '+lean(q)+' = 0)')
 text.extend(['    : False := by','  have hz : ('+str(denominator)+' : ℂ) = 0 := by','    linear_combination'])
 for i,p in enumerate(multipliers):text.append('      '+('' if i==0 else '+ ' )+'('+lean(p)+') * h'+str(i))
 text.extend(['      - ('+lean(quotient)+') * hr','  norm_num at hz',''])
text.extend(['end PEqualNP.Outside.L_gct_231_aux.FramePairedCases','']);path=Path('/workspace/pequalnp-proofs/results/orch/lemmas/FramePairedCases.lean');path.write_text('\n'.join(text));(job/'frame-paired-integer-certificates.json').write_text(json.dumps(checks,indent=2)+'\n');print(json.dumps({'source':str(path),'bytes':path.stat().st_size,'lines':len(text),'cases':[{'case':d['case'],'constant_digits':len(d['constant']),'multiplier_terms':[len(s.Poly(s.sympify(p),*variables,r).terms()) for p in d['multipliers']]} for d in checks]}))
