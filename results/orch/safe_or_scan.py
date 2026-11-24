import itertools
import json
import sys
from pathlib import Path

from near_repair import antichain
from rectangle_search import bits,c4free,mincover


records = []
for name in Path(sys.argv[1]).read_text().splitlines():
    try:
        r = json.loads(Path(name).read_text())
    except (ValueError,OSError):
        continue
    if not isinstance(r,dict) or not all(k in r for k in ['n','gates','output']):
        continue
    n,gs,out = r['n'],r['gates'],r['output']
    if not isinstance(n,int) or not isinstance(out,int) or not isinstance(gs,list):
        continue
    if not all(isinstance(g,list) and len(g)==3 and g[0] in ['and','or']
               and isinstance(g[1],int) and isinstance(g[2],int) for g in gs):
        continue
    values = [frozenset({1<<i}) for i in range(n)]
    dependencies = [0]*n
    valid = True
    for i,(op,a,b) in enumerate(gs):
        if not (0<=a<n+i and 0<=b<n+i):
            valid = False
            break
        va,vb=values[a],values[b]
        if len(va)*len(vb)>10000:
            valid=False
            break
        values.append(antichain(va|vb) if op=='or' else antichain(x|y for x in va for y in vb))
        dependencies.append(dependencies[a]|dependencies[b]|(1<<i))
    if not valid or not 0<=out<len(values):
        continue
    es=values[out]
    if not es or any(e.bit_count()!=2 for e in es) or not c4free(n,es):
        continue
    hood=[0]*n
    for e in es:
        u,v=bits(e);hood[u]|=1<<v;hood[v]|=1<<u
    tau=mincover(n,es).bit_count()
    bound=len(es)+tau-1
    candidates=[]
    for w in range(n,len(values)):
        terms=values[w]
        if len(terms)<2 or any(t.bit_count()!=1 for t in terms):
            continue
        support=sum(terms)
        if all(not(hood[u]&hood[v]) for u,v in itertools.combinations(bits(support),2)):
            candidates.append((w,support,support.bit_count()-1,dependencies[w]))
    best=(dependencies[out].bit_count()-bound,[],dependencies[out])

    def visit(j,supports,selected,weight,needed):
        global best
        margin=needed.bit_count()-bound-weight
        if margin<best[0]:best=(margin,selected.copy(),needed)
        for i in range(j,len(candidates)):
            w,s,weight_i,deps=candidates[i]
            if all((s&t).bit_count()<=1 for t in supports):
                visit(i+1,supports+[s],selected+[w],weight+weight_i,needed|deps)

    visit(0,[],[],0,dependencies[out])
    result=dict(source=name,n=n,edges=[list(bits(e)) for e in es],tau=tau,bound=bound,
                original_gates=len(gs),base_live=dependencies[out].bit_count(),
                safe_or_wires=[dict(wire=w,support=list(bits(s)),weight=wt) for w,s,wt,_ in candidates],
                best_augmented_margin=best[0],selected=best[1],needed_mask=best[2])
    records.append(result)
    if best[0]<0:
        print(json.dumps(dict(candidate=result)),flush=True)
with open(sys.argv[2],'w') as f:json.dump(records,f,indent=2)
print(json.dumps(dict(pure_c4free_records=len(records),with_safe_or=sum(bool(r['safe_or_wires']) for r in records),
                     minimum_margin=min((r['best_augmented_margin'] for r in records),default=None))),flush=True)
