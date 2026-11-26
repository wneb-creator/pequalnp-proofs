"""Verify a family with unbounded singleton-positive AND count at fixed AND surplus.

For m >= 2, the graph has matching/cover number m and the circuit has m+1
AND gates, of which m accept a singleton. This is not a counterexample to
L-meta-4970 or to the matching-tight singleton-free conjecture. Full truth
tables are checked for m=2..5; the report also gives the general algebra.
Run with Python 3; only JSON is written to stdout.
"""

import json

def check(m):
    assert m>=2
    n=2*m;a=0
    E={(0,m+j)for j in range(m)}|{(j,m+j)for j in range(1,m)}
    inputs=[sum(1<<x for x in range(1<<n)if x>>i&1)for i in range(n)]
    gates=[];tables=list(inputs);raw=[{i}for i in range(n)]
    def add(op,u,v):
        gates.append((op,u,v));tables.append(tables[u]&tables[v]if op=='and'else tables[u]|tables[v])
        R=set()if op=='and'else raw[u]|raw[v]
        assert not(R&set(range(m))and R&set(range(m,n)))
        raw.append(R);return len(tables)-1
    g=add('and',a,a)
    for j in range(1,m):
        left=add('or',g,j);right=add('or',g,m+j);g=add('and',left,right)
    L=m
    for j in range(1,m):L=add('or',L,m+j)
    output=add('and',g,L)
    for j in range(1,m):add('or',a,j)
    target=0
    for u,v in E:target|=inputs[u]&inputs[v]
    assert tables[output]==target
    ss=[{i for i in range(n)if tt>>(1<<i)&1}for tt in tables]
    andw=[n+j for j,t in enumerate(gates)if t[0]=='and']
    assert len(andw)==m+1 and sum(bool(ss[w])for w in andw)==m
    assert all(ss[w]=={0}for w in andw[:-1])and ss[andw[-1]]==set()
    N=[{v if u==c else u for u,v in E if c in(u,v)}for c in range(n)]
    assert all(len(N[u]&N[v])<=1 for u in range(n)for v in range(u+1,n))
    served=set()
    for w,(op,_,_)in enumerate(gates,n):
        if op!='or'or len(ss[w])<2:continue
        tt=0
        for i in ss[w]:tt|=inputs[i]
        if tt!=tables[w]:continue
        for c,Q in enumerate(N):
            if ss[w]<=Q:served|={tuple(sorted((c,v)))for v in ss[w]}
    assert served==E
    matching={(j,m+j)for j in range(m)};assert matching<=E
    live={output}
    for w in range(output,n-1,-1):
        if w in live:live.update(gates[w-n][1:])
    assert set(andw)<=live
    es=sorted(E);parent=list(range(len(es)))
    def find(k):
        while parent[k]!=k:parent[k]=parent[parent[k]];k=parent[k]
        return k
    for w,tt in enumerate(tables):
        for c,Q in enumerate(N):
            if not raw[w]<=Q:continue
            outside=sum(1<<i for i in range(n)if i not in Q)
            B=ss[w]if not(tt>>outside&1)else raw[w]
            assert B<=Q
            ee=[es.index(tuple(sorted((c,i))))for i in B]
            for e in ee[1:]:parent[find(e)]=find(ee[0])
    k=len({find(i)for i in range(len(es))});assert k==1
    return dict(m=m,n=n,edges=es,gates=gates,output=output,AND_count=m+1,tau=m,
                nonempty_singleton_AND=m,empty_singleton_AND=1,defect=1,
                T0=True,C4_free=True,served=True,all_AND_live=True,augmented_components=k,
                assignments_checked=1<<n)

report=dict(family='g0=a AND a; gj=(gprev OR dj) AND (gprev OR cj); L=OR(all lines); output=gfinal AND L; add pure OR(a,dj) witnesses.',scope='Arbitrarily many nonempty-singleton AND gates at fixed defect AND-tau=1; does not refute tightness or augmented component count.',examples=[check(m)for m in range(2,6)],algebraic_proof=['For m>=2, points are a,d1,...,d(m-1); lines are b,c1,...,c(m-1).', 'Boolean identity (g OR d) AND (g OR c) = g OR (d AND c) gives gj = a OR the union of dt AND ct for 1<=t<=j.', 'Every dt AND ct implies L, so final output is (a AND L) OR the union of dt AND ct. Its graph is the a-star plus one private point dt adjacent to each ct.', 'Matching {a-b} union {dt-ct} has size m; all m points form a cover. Therefore tau=m. C4-freeness follows because every point other than a has degree one.', 'The m ANDs g0,...,g(m-1) each have singleton support {a}; the final AND has empty singleton support. AND=m+1, so defect=1.', 'Each intermediate OR containing gj has raw support equal to its other input singleton; L has only line inputs and appended witnesses OR(a,dt) have only point inputs. Thus T0 holds.', 'L serves all a-star edges and OR(a,dt) serves every dt-ct edge. Their edge cliques connect all graph edges, hence augmented k=1.', 'Every gj is an ancestor of the output, and each new pair dt-ct remains in the output function.'])
print(json.dumps(report, indent=2))
