import json
from pathlib import Path
root=Path('/tmp/oec/pequalnp-pilot-73/fresh-count')
D={0,1,3,9}
def incident(p,l): return (p-l)%13 in D
positive=[(1<<p)|(1<<(13+l)) for p in range(13) for l in range(13) if incident(p,l)]
negative=[]
for a in range(8192):
    A=[p for p in range(13) if a>>p&1]
    B=[l for l in range(13) if all(not incident(p,l) for p in A)]
    closed=all(any(incident(p,l) for l in B) for p in range(13) if not a>>p&1)
    degenerate=any(all(incident(p,l) for p in A) for l in range(13)) or any(all(incident(p,l) for l in B) for p in range(13))
    if closed and degenerate:
        negative.append(a+sum(1<<(13+l) for l in B))
assert len(positive)==52 and len(negative)==236
rows=positive+negative
raw=[sum(1<<j for j,r in enumerate(rows) if r>>i&1) for i in range(26)]
allmask=(1<<len(rows))-1
posmask=(1<<52)-1
negmask=allmask^posmask
answers=[]
for name in (root/'without-flagrows-files.txt').read_text().splitlines():
    data=json.loads(Path(name).read_text())
    records=data if isinstance(data,list) else [data]
    for j,rec in enumerate(records):
        if not isinstance(rec,dict) or 'gates' not in rec: continue
        gates=rec['gates']
        shape=len(gates)==63 and gates[-1][0]==0 and gates[-1][1]!=gates[-1][2]
        shape=shape and all(len(g)==3 and g[0] in (0,1) and all(isinstance(w,int) and 0<=w<26+k for w in g[1:]) for k,g in enumerate(gates))
        assert shape
        values=raw.copy()
        for op,a,b in gates: values.append((values[a]|values[b]) if op else (values[a]&values[b]))
        missing=(posmask&~values[-1]).bit_count()
        falsepos=(negmask&values[-1]).bit_count()
        answers.append({'file':str(Path(name).relative_to(root)),'record':j,'shape_valid':True,'missing_positive':missing,'false_positive':falsepos,'valid_on_full_posted_domain':missing==falsepos==0})
answer={'status':'No valid witness' if not any(x['valid_on_full_posted_domain'] for x in answers) else 'VALID WITNESS REQUIRES LEAN CERTIFICATION','positive_count':52,'negative_count':236,'tested_candidates':len(answers),'results':answers}
(root/'without-flagrows-validation.json').write_text(json.dumps(answer,indent=2)+'\n')
print(json.dumps({k:v for k,v in answer.items() if k!='results'},indent=2))
