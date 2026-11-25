import json
import sys
from pathlib import Path

meta=json.loads(Path(sys.argv[1]).read_text())
rows=[json.loads(s) for s in Path(sys.argv[2]).read_text().splitlines() if s.startswith('{')]
best=min(rows,key=lambda r:r['score'])
n=meta['n'];edges=meta['edges'];gates=best['gates']
for j,(op,a,b) in enumerate(gates):
    assert op in (0,1) and 0<=a<n+j and 0<=b<n+j
def target(x):return any((x>>a)&(x>>b)&1 for a,b in edges)
def run(x):
    w=[(x>>i)&1 for i in range(n)]
    for op,a,b in gates:w.append((w[a]|w[b]) if op else(w[a]&w[b]))
    return w
bad=[x for x in range(1<<n) if bool(run(x)[-1])!=target(x)]
result={'candidate_score':best['score'],'size':len(gates),'all_inputs_checked':1<<n,
        'wrong_inputs':len(bad),'wrong_test_inputs':[x for x in meta['tests'] if bool(run(x)[-1])!=target(x)]}
if best['score']==0:
    assert not bad
    result['gates']=gates
    result['is_AO2']=True
    result['read1_pairs']=[];result['not_read1_pairs']=[]
    for p,l in edges:
        w=[{(1,0)} if i==p else({(0,1)} if i==l else set()) for i in range(n)]
        for op,a,b in gates:
            w.append(w[a]|w[b] if op else{(min(x+z,2),min(y+t,2)) for x,y in w[a] for z,t in w[b]})
        result['read1_pairs' if(1,1)in w[-1] else'not_read1_pairs'].append([p,l])
print(json.dumps(result))
