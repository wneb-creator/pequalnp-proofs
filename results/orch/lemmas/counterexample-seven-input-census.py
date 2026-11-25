"""All bipartite C4-free graphs on seven labelled inputs, up to side exchange.

This is a finite graph census, not a circuit lower-bound proof. All circuit
claims in the supplement remain attached to their separately tested targets.
"""
import json
from itertools import permutations

reports=[]
for p in range(4):
    l=7-p;pairs=[(a,p+b) for a in range(p) for b in range(l)]
    masks=1<<(p*l);valid=0;forest=0;hist={};cyclic={}
    for mask in range(masks):
        c4=any(all(mask>>(u*l+v)&1 for u in (a,aa) for v in (b,bb))
               for a in range(p) for aa in range(a+1,p) for b in range(l) for bb in range(b+1,l))
        if c4:continue
        valid+=1;es=[edge for k,edge in enumerate(pairs) if mask>>k&1]
        tau=min(s.bit_count() for s in range(128) if all(s>>a&1 or s>>b&1 for a,b in es))
        key=(len(es),tau);hist[key]=hist.get(key,0)+1
        parent=list(range(7));cycle=False
        def find(a):
            while parent[a]!=a:a=parent[a]
            return a
        for a,b in es:
            aa,bb=find(a),find(b)
            if aa==bb:cycle=True
            parent[aa]=bb
        if not cycle:forest+=1;continue
        canonical=min(sum(1<<(aa[a]*l+bb[b]) for a in range(p) for b in range(l) if mask>>(a*l+b)&1)
                      for aa in permutations(range(p)) for bb in permutations(range(l)))
        cyclic[canonical]=cyclic.get(canonical,0)+1
    rows=[]
    for c,count in sorted(cyclic.items()):
        es=[edge for k,edge in enumerate(pairs) if c>>k&1]
        support=sorted({v for e in es for v in e})
        rows.append(dict(canonical=c,labelled_count=count,edges=es,active_inputs=len(support)))
    assert (p<3 and not cyclic) or (p==3 and set(cyclic)=={854,862})
    reports.append(dict(p=p,l=l,all_masks=masks,c4_free_masks=valid,forests=forest,cyclic_masks=valid-forest,
                        histogram=[dict(edges=e,tau=t,count=c) for (e,t),c in sorted(hist.items())],cyclic_classes=rows))
print(json.dumps(dict(inputs=7,partitions=reports,
    conclusion='Every bipartite C4-free graph on7 inputs is a forest, C6 plus an isolated input, or C6 plus a pendant edge, up to input renaming and side exchange.',
    limitation='Graph census only; this is not a circuit proof or a blanket seven-input solver result.'),indent=2))
