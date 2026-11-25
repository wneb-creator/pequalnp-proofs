"""Match the literal Lean endpoint hypotheses to the exact scalar source rows."""
from pathlib import Path
import hashlib,json,re
import sympy as s
root=Path(__file__).parent
lean=root/'Case3ScalarEndpoints.lean';text=lean.read_text()
U,V,sat=s.symbols('U V sat');local={'U':U,'V':V,'sat':sat}
branches=json.loads((root/'c4-case3-scalar-branches.json').read_text())
rows=[]
for name,a,b,labels in [('case3_beta_neg2_A_three32_impossible','3/32','-2',{'hq':0,'hr':3,'hl':4}),
                       ('case3_beta_half_A_four_unique','4','1/2',{'hq':0,'hc':1,'hr':3})]:
    branch=next(row for row in branches if row['A']==a and row['beta']==b)
    block=text.split('theorem '+name,1)[1].split(':= by',1)[0]
    for label,index in labels.items():
        match=re.search(r'\('+label+r' : (.*?) = 0\)',block,re.S)
        assert match is not None
        expression=s.sympify(match.group(1).replace('^','**'),locals=local)
        original=s.sympify(branch['equations'][index],locals=local)
        ratio=s.cancel(original/expression)
        assert ratio.is_Rational and ratio!=0
        assert s.expand(original-ratio*expression)==0
        rows.append({'theorem':name,'hypothesis':label,'source_equation':index,
                     'source_equals_hypothesis_times':str(ratio)})
assert all(bad not in text for bad in ['_root_','"','sorry','native_decide','axiom '])
out={'source_sha256':hashlib.sha256(lean.read_bytes()).hexdigest(),
     'lines':len(text.splitlines()),'checked_hypotheses':rows,
     'scope':'Two conditional scalar endpoint lemmas; no claim of the preceding scale restriction.'}
(root/'case3-scalar-endpoints-mapping.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
