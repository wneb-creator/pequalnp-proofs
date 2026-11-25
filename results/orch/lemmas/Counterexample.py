from itertools import combinations
from datetime import datetime, timezone
from pathlib import Path
import json


def girth_ok(n, edges):
    E = {frozenset(e) for e in edges}
    if any(all(frozenset(e) in E for e in [(a,b),(b,c),(c,a)]) for a,b,c in combinations(range(n),3)):
        return False
    for a,b,c,d in combinations(range(n),4):
        if any(all(frozenset(e) in E for e in cycle) for cycle in [((a,b),(b,c),(c,d),(d,a)), ((a,c),(c,b),(b,d),(d,a)), ((a,b),(b,d),(d,c),(c,a))]):
            return False
    return True


def vertex_cover(n, edges):
    for k in range(n+1):
        for S in combinations(range(n),k):
            if all(a in S or b in S for a,b in edges): return k,S


def run(n, max_upper=None):
    bits=1 << n
    inputs=tuple(sum(1<<a for a in range(bits) if (a>>i)&1) for i in range(n))
    pairs=list(combinations(range(n),2))
    targets={}
    for graph_mask in range(1 << len(pairs)):
        edges=[e for i,e in enumerate(pairs) if (graph_mask>>i)&1]
        if not girth_ok(n,edges): continue
        f=0
        for a,b in edges: f |= inputs[a]&inputs[b]
        vc,S=vertex_cover(n,edges)
        upper=len(edges)+vc-1 if edges else 0
        if max_upper is not None and upper > max_upper: continue
        targets[f]={'edges':edges,'star_upper':upper,'cover':S,'min':0 if f==0 or f in inputs else None}
    maxg=max(t['star_upper'] for t in targets.values())
    states={tuple(sorted(inputs))}
    counts=[]
    for k in range(1,maxg+1):
        nexts=set()
        for state in states:
            # Constants and unary gates cannot occur in a minimum nonconstant positive circuit:
            # they simplify by substitution to an existing wire or constant false output.
            for a,b in combinations(state,2):
                for c in (a&b,a|b):
                    if c in state: continue
                    if c in targets and targets[c]['min'] is None: targets[c]['min']=k
                    if k < maxg: nexts.add(tuple(sorted(state+(c,))))
        counts.append((k,len(states),len(nexts)))
        print(n,counts[-1],flush=True)
        states=nexts
    return {'n':n,'counts':counts,'targets':list(targets.values()),'counterexamples':[v for v in targets.values() if v['min']!=v['star_upper']]}

if __name__ == '__main__':
    results=[run(n) for n in range(1,5)]
    print(json.dumps(results,indent=2))
    Path('/tmp/oec/pequalnp-pilot-54/counterexample-small-results.json').write_text(json.dumps(results,indent=2)+'\n')
