from pathlib import Path
import json
from itertools import combinations

pairs=list(combinations(range(4),2))
edges=[(v,4+j) for j,pair in enumerate(pairs) for v in pair]

def make(selected_edges):
    gates=[]
    def gate(op,a,b):
        assert a!=b
        gates.append([op,a,b])
        return 9+len(gates)
    def disj(xs):
        out=xs[0]
        for x in xs[1:]:out=gate('or',out,x)
        return out
    terms=[]
    for v in range(4):
        neighbors=[4+j for j,pair in enumerate(pairs) if v in pair and j not in selected_edges]
        if neighbors:terms.append(gate('and',v,disj(neighbors)))
    for j in selected_edges:terms.append(gate('and',4+j,disj(list(pairs[j]))))
    output=disj(terms)
    return {'inputs':10,'gates':gates,'output':output}

def audit(c):
    gates=c['gates']; fan=[0]*(10+len(gates))
    for j,(op,a,b) in enumerate(gates):
        assert 0<=a<10+j and 0<=b<10+j and a!=b
        fan[a]+=1;fan[b]+=1
    assert c['output']==9+len(gates)
    assert all(fan[w]>=1 for w in range(c['output']))
    def evaluate(mask):
        w=[bool(mask>>i&1) for i in range(10)]
        for op,a,b in gates:w.append((w[a] and w[b]) if op=='and' else (w[a] or w[b]))
        return w
    for mask in range(1024):
        assert evaluate(mask)[c['output']]==any(mask>>a&1 and mask>>b&1 for a,b in edges)
    singleton=[evaluate(1<<i) for i in range(10)]
    supports=[[i for i in range(10) if singleton[i][w]] for w in range(len(fan))]
    eligible=sorted({i for w,s in enumerate(supports) if fan[w]>=2 for i in s})
    plus=sum(max(0,fan[w]-1) for w,s in enumerate(supports) if s)
    zero=sum(max(0,fan[w]-1) for w,s in enumerate(supports) if not s)
    return {'gates':len(gates),'eligible':eligible,'eligible_originals':[i for i in eligible if i<4],
            'Bplus':plus,'Bzero':zero,'totalSurplus':plus+zero,'truth_rows':1024}

controls=[]
for selected in [[],[0],list(range(6))]:
    c=make(selected);v=audit(c);controls.append({'selected_edge_centers':selected,'circuit':c,'verification':v})
assert [(x['verification']['gates'],len(x['verification']['eligible_originals'])) for x in controls]==[(15,0),(16,2),(17,4)]
out={'scope':'Exact supported K4 controls only; no universal eligibility bound is inferred.',
     'accepted_labeling':'originals0..3; subdivision vertices4..9 for01,02,03,12,13,23', 'controls':controls}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([c['verification'] for c in controls],indent=2))
