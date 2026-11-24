import itertools
import json
import sys
from pathlib import Path

from rectangle_search import Circuit,bits,edge,mincover


def case(k,cross):
    n=3*k+4
    a=lambda j,i:4+3*j+i
    edges={(3,i) for i in range(3)}
    for j in range(k):
        edges.update((a(j,i),a(j,l)) for i,l in itertools.combinations(range(3),2))
        edges.update((i,a(j,i)) for i in range(3))
    cross_spec=[]
    if cross and k==2:cross_spec=[(0,1,0)]
    if cross and k==3:cross_spec=[(0,1,0),(1,2,1),(0,2,2)]
    for p,q,i in cross_spec:edges.add((a(p,i),a(q,i)))
    edges=sorted(edges)
    adj=[[False]*n for _ in range(n)]
    for u,v in edges:adj[u][v]=adj[v][u]=True
    for q in itertools.combinations(range(n),4):
        for b,c,d in itertools.permutations(q[1:]):
            aa=q[0]
            assert not(adj[aa][b] and adj[b][c] and adj[c][d] and adj[d][aa])
    independent=[m for m in range(1<<n) if all(not(m>>u&1 and m>>v&1) for u,v in edges)]
    alpha=max(m.bit_count() for m in independent)
    tau=n-alpha
    maximal=[m for m in independent if all(any(adj[u][v] and m>>v&1 for v in range(n))
             for u in range(n) if not m>>u&1)]
    masks={edge(u,v) for u,v in edges}
    cover=mincover(n,masks)
    assert cover.bit_count()==tau
    c=Circuit(n)
    output=c.gate('and',3,c.any([0,1,2]))
    for j in range(k):
        aa,bb,cc=[a(j,i) for i in range(3)]
        r=c.gate('and',c.any([0,cc]),c.any([aa,2]))
        net=c.gate('and',c.any([aa,cc,1]),c.gate('or',r,bb))
        output=c.gate('or',output,net)
    for p,q,i in cross_spec:
        output=c.gate('or',output,c.gate('and',a(p,i),a(q,i)))
    c,output=c.compact(output)
    control=Circuit(n)
    stars={}
    for u,v in edges:
        center=u if cover>>u&1 else v
        other=v if center==u else u
        stars.setdefault(center,[]).append(other)
    terms=[control.gate('and',center,control.any(ns)) for center,ns in stars.items()]
    exact_output=control.any(terms)
    control,exact_output=control.compact(exact_output)
    wrong=[]
    for m in range(1<<n):
        wanted=any(m>>u&1 and m>>v&1 for u,v in edges)
        def evaluate(circuit,out):
            vals=[bool(m>>i&1) for i in range(n)]
            for op,u,v in circuit.gs:
                vals.append(vals[u] and vals[v] if op=='and' else vals[u] or vals[v])
            return vals[out]
        assert evaluate(control,exact_output)==wanted
        if evaluate(c,output)!=wanted:wrong.append([m,evaluate(c,output)])
    assert wrong==[[7,True]]
    bound=len(edges)+tau-1
    assert len(control.gs)==bound
    identifier=f'shared-net-k{k}'+('-cross' if cross else '')
    return dict(id=identifier,n=n,k=k,cross_spec=cross_spec,edges=edges,e=len(edges),
                alpha=alpha,tau=tau,bound=bound,target_gates=bound-1,
                maximal_independent_sets=[list(bits(m)) for m in maximal],
                maximal_independent_count=len(maximal),
                gates=control.gs,output=exact_output,control_size=len(control.gs),
                control_verified=True,near_gates=c.gs,near_output=output,
                near_size=len(c.gs),near_errors=wrong,
                validation='All assignments checked for both circuits; all independent subsets and all four-vertex cycles checked.')


directory=Path(sys.argv[1]);directory.mkdir(parents=True,exist_ok=True)
records=[]
for k in [2,3]:
    for cross in [False,True]:
        r=case(k,cross)
        (directory/(r['id']+'.json')).write_text(json.dumps(r,indent=2)+'\n')
        records.append({key:r[key] for key in ['id','n','e','tau','bound','target_gates','maximal_independent_count','near_size','near_errors']})
(directory/'manifest.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records))
