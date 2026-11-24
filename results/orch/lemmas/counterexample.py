from itertools import combinations
from collections import Counter
import json
from pathlib import Path


def truth_input(n, i):
    return sum(1 << a for a in range(1 << n) if a >> i & 1)


def graph_table(n, edges):
    xs = [truth_input(n, i) for i in range(n)]
    out = 0
    for u, v in edges:
        out |= xs[u] & xs[v]
    return out


def analyze(n, circuit, target):
    vals = [truth_input(n, i) for i in range(n)]
    ors = [{i} for i in range(n)]
    gates = [set() for _ in range(n)]
    cones = [set() for _ in range(n)]
    for j, (op, a, b) in enumerate(circuit):
        vals.append(vals[a] & vals[b] if op == 'and' else vals[a] | vals[b])
        ors.append(ors[a] | ors[b] if op == 'or' else set())
        gates.append({j} | gates[a] | gates[b] if op == 'or' else {j})
        cones.append(cones[a] | cones[b] | ({a-n} if a >= n else set()) | ({b-n} if b >= n else set()))
    tops = [j for j, (op, a, b) in enumerate(circuit) if op == 'and' and vals[n+j] & ~target == 0]
    junk = [j for j, (op, a, b) in enumerate(circuit) if op == 'and' and vals[n+j] & ~target]
    topform = not any(i in cones[n+j] for i in tops for j, (op, a, b) in enumerate(circuit) if op == 'and')
    edges = {(u,v) for u,v in combinations(range(n),2) if target >> ((1<<u)|(1<<v)) & 1}
    stars = {tuple(sorted((u,v))) for j in tops for u in ors[circuit[j][1]] for v in ors[circuit[j][2]]}
    ustar = edges - stars
    selected = set()
    for j in tops:
        for a,b in (circuit[j][1:],circuit[j][1:][::-1]):
            for u in ors[a]:
                for g in gates[b] & set(junk):
                    for v in range(n):
                        e = tuple(sorted((u,v)))
                        if e in ustar and vals[n+g] >> ((1<<u)|(1<<v)) & 1:
                            selected.add(e)
    return {'tops': tops, 'junk': junk, 'topform': topform, 'ustar': sorted(ustar), 'selected': sorted(selected)}


def search(n, targets, max_gates):
    xs = tuple(truth_input(n, i) for i in range(n))
    target_tts = {graph_table(n, e): name for name,e in targets.items()}
    pending = set(target_tts)
    states = {(): ()}
    result = {}
    counts = []
    for depth in range(1,max_gates+1):
        nxt = {}
        for state, circuit in states.items():
            vals = xs + tuple(state)
            wire = {v:i for i,v in enumerate(xs)}
            actualvals=list(xs)
            for op,a,b in circuit:
                actualvals.append(actualvals[a] & actualvals[b] if op=='and' else actualvals[a]|actualvals[b])
            wire={v:i for i,v in enumerate(actualvals)}
            for a,b in combinations(vals,2):
                for op,v in (('and',a&b),('or',a|b)):
                    if v in wire: continue
                    newstate=tuple(sorted((*state,v)))
                    if newstate in nxt: continue
                    newcircuit=(*circuit,(op,wire[a],wire[b]))
                    nxt[newstate]=newcircuit
                    if v in pending:
                        name=target_tts[v]
                        result[name]={'gates':depth,'circuit':newcircuit,**analyze(n,newcircuit,v)}
                        pending.remove(v)
        counts.append({'gates':depth,'states':len(nxt),'pending':[target_tts[v] for v in pending]})
        print(json.dumps(counts[-1]),flush=True)
        if not pending: break
        states=nxt
    return {'n':n,'counts':counts,'found':result,'pending':[target_tts[v] for v in pending]}

if __name__ == '__main__':
    targets={'edge':[(0,1)],'two_disjoint':[(0,1),(2,3)],'path2':[(0,1),(1,2)],'path3':[(0,1),(1,2),(2,3)],'star3':[(0,1),(0,2),(0,3)]}
    result=search(4,targets,4)
    Path('results/orch/lemmas/counterexample-data.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

    minima={graph_table(4,targets[name]):d['gates'] for name,d in result['found'].items()}
    names={graph_table(4,e):name for name,e in targets.items()}
    summary={name:{'circuits':0,'topform':0,'junk_circuits':0,'topform_junk':0,'max_selected':0} for name in targets}
    def dfs(vals,circuit):
        if len(circuit)==4: return
        for a,b in combinations(range(len(vals)),2):
            for op,v in (('and',vals[a]&vals[b]),('or',vals[a]|vals[b])):
                if v in vals: continue
                nc=(*circuit,(op,a,b))
                if minima.get(v)==len(nc):
                    row=summary[names[v]]
                    d=analyze(4,nc,v)
                    row['circuits']+=1
                    row['topform']+=int(d['topform'])
                    row['junk_circuits']+=int(bool(d['junk']))
                    row['topform_junk']+=int(d['topform'] and bool(d['junk']))
                    if d['topform']: row['max_selected']=max(row['max_selected'],len(d['selected']))
                dfs((*vals,v),nc)
    dfs(tuple(truth_input(4,i) for i in range(4)),())
    result['all_minimal_circuits']=summary
    Path('results/orch/lemmas/counterexample-data.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

    def peel(n,edges):
        remaining=set(edges)
        removed=[]
        while True:
            degrees=[sum(v in e for e in remaining) for v in range(n)]
            vertex=next((v for v,d in enumerate(degrees) if 0<d<=2),None)
            if vertex is None: break
            incident={e for e in remaining if vertex in e}
            removed.append((vertex,len(incident)))
            remaining-=incident
        support={v for e in edges for v in e}
        assert all(sum(v in e for e in remaining) in (0,) or sum(v in e for e in remaining)>=3 for v in range(n))
        assert len(edges)-len(remaining)==sum(d for v,d in removed)
        assert len(edges)<=len(remaining)+2*len(support)
        assert len({v for v,d in removed})==len(removed)
        return {'edges':len(edges),'support':len(support),'core_edges':len(remaining),'removed_vertices':len(removed),'removed_edges':sum(d for v,d in removed)}
    pairs=list(combinations(range(6),2))
    census=Counter()
    for mask in range(1<<len(pairs)):
        edges={pairs[i] for i in range(len(pairs)) if mask>>i&1}
        d=peel(6,edges)
        census['graphs']+=1
        census['nonempty_core']+=int(d['core_edges']>0)
    outer={(i,(i+1)%5) for i in range(5)}
    inner={(5+i,5+(i+2)%5) for i in range(5)}
    spokes={(i,5+i) for i in range(5)}
    petersen={tuple(sorted(e)) for e in outer|inner|spokes}
    result['peeling']={'six_vertex_census':dict(census),'petersen':peel(10,petersen),'petersen_one_edge_deleted':peel(10,petersen-{(0,1)})}
    Path('results/orch/lemmas/counterexample-data.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result['peeling'],indent=2))
