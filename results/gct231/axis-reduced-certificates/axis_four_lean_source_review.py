from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction
import json,hashlib,re,ast
base=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
p=base/'AxisReducedCertificates.lean';src=p.read_text();assert sha(p)=='8eeef2cb88b2869c59b72329d5b896b37f818f64b6e41c95d7ae4c10769c39cc' and len(src.encode())==44023 and len(src.splitlines())==35
allnames=['o7','o8','o1','u']+['h'+str(i) for i in range(8)];n=len(allnames);zero=(0,)*n
# Reuse the earlier independent sparse AST parser; do not run its surrounding checker.
prior=(base/'star_lean_source_review.py').read_text();helper=prior[prior.index('def add(a,b):'):prior.index('hyps=re.findall')];exec(helper)
for case in ['equal','different']:
 c=json.loads((base/('axis-four-'+case+'-quotient-compressed-certificate.json')).read_text());D=int(c['integer_denominator']);gens=[{tuple(m):Fraction(v) for m,v in row} for row in c['generators']];ms=[{tuple(m):Fraction(v) for m,v in row} for row in c['multipliers']]
 begin=src.index('theorem '+case+'_chart_inconsistent');end=src.index('  norm_num at h',begin)+len('  norm_num at h');body=src[begin:end]
 assert body.splitlines()[0]=='theorem '+case+'_chart_inconsistent (o7 o8 o1 u : ℂ)'
 used=[i for i,m in enumerate(ms) if m];assert used==[0,2,4,5,6,7]
 hyps=re.findall(r'    \(h(\d+) : \((.*?) : ℂ\) = 0\)',body);assert [int(i) for i,_ in hyps]==used
 for i,expr in hyps:assert parse(expr)=={mon+(0,)*8:int(v) for mon,v in gens[int(i)].items()}
 line=next(l for l in body.splitlines() if l.startswith('    linear_combination '));actual=parse(line.removeprefix('    linear_combination '));expected={}
 for i,m in enumerate(ms):
  for mon,c in m.items():
   hs=[0]*8;hs[i]=1;value=c*D;assert value.denominator==1;expected[mon+tuple(hs)]=int(value)
 assert actual==expected
 assert f'  have h : ({D} : ℂ) = 0 := by' in body and '    : False := by' in body
 assert len(body.splitlines())==11 and body.rstrip().endswith('norm_num at h')
 print(case,'actual6normalizedhypotheses,',sum(map(len,ms)),'multiplierterms and nonzero integerdenominator match exact reviewed identity; unusedgenerators1,3omitted: PASS',flush=True)
assert len(re.findall(r'^theorem ',src,re.M))==2 and not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',src)
assert all(l.endswith(' in') for l in src.splitlines() if l.startswith('set_option '))
assert sha(p)=='8eeef2cb88b2869c59b72329d5b896b37f818f64b6e41c95d7ae4c10769c39cc'
print('Scope: exactly two conditional polynomial contradiction lemmas over C, six explicit hypotheses each includingu^2-2. Geometric reduction/coverage not asserted. Source-only before authorcompile; no compiler or solver rerun.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
