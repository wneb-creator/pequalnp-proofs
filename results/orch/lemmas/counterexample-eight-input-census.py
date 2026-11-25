"""Exact extremal C4-free graph census on3+5 and4+4 inputs."""
from itertools import permutations
import json

def analyse_split(p,l):
    pairs=[(a,p+b) for a in range(p) for b in range(l)]
    full=(1<<l)-1;valid=[];hist={};max_score=0;max_edges=0
    for mask in range(1<<(p*l)):
        rows=[(mask>>(a*l))&full for a in range(p)]
        if any((rows[a]&rows[b]).bit_count()>1 for a in range(p) for b in range(a+1,p)):continue
        # A cover's point subset determines the forced line vertices. Taking
        # exactly those forced vertices cannot increase its size.
        tau=p+l
        for selected in range(1<<p):
            forced=0
            for a in range(p):
                if not(selected>>a&1):forced|=rows[a]
            tau=min(tau,selected.bit_count()+forced.bit_count())
        e=mask.bit_count();valid.append((mask,e,tau));hist[(e,tau)]=hist.get((e,tau),0)+1
        max_score=max(max_score,e+tau);max_edges=max(max_edges,e)
    input_perms=[(a,b) for a in permutations(range(p)) for b in permutations(range(l))]
    def canonical(mask):
        es=[(a,b) for a in range(p) for b in range(l) if mask>>(a*l+b)&1]
        return min(sum(1<<(aa[a]*l+bb[b]) for a,b in es) for aa,bb in input_perms)
    classes={}
    for mask,e,tau in valid:
        if e+tau==max_score:
            c=canonical(mask);classes[c]=classes.get(c,0)+1
    records=[]
    for c,count in sorted(classes.items()):
        es=[edge for k,edge in enumerate(pairs) if c>>k&1];n=p+l
        tau=min(s.bit_count() for s in range(1<<n) if all(s>>a&1 or s>>b&1 for a,b in es))
        support=sorted({v for e in es for v in e})
        parent=list(range(n));cycle=False
        def find(a):
            while parent[a]!=a:a=parent[a]
            return a
        for a,b in es:
            aa,bb=find(a),find(b)
            if aa==bb:cycle=True
            parent[aa]=bb
        comp=len({find(a) for a in range(n)})
        assert len(es)+tau==max_score
        records.append(dict(p=p,l=l,mask=c,labelled_count=count,edges=es,edge_count=len(es),tau=tau,
                            active_inputs=len(support),support=support,forest=not cycle,components=comp,
                            cycle_rank=len(es)-n+comp,degrees=[sum(a in edge for edge in es) for a in range(n)],
                            reference_bound=len(es)+tau-1,violation_gate_budget=len(es)+tau-2))
    return dict(p=p,l=l,all_masks=1<<(p*l),c4_free_masks=len(valid),maximum_edges=max_edges,
                maximum_edges_plus_cover=max_score,highest_score_labelled=sum(classes.values()),
                highest_score_classes=len(classes),records=records,
                histogram=[dict(edges=e,tau=t,count=c) for (e,t),c in sorted(hist.items())])
reports=[analyse_split(3,5),analyse_split(4,4)]
print(json.dumps(dict(inputs=8,partitions=reports,
    scope='Exact finite graph census. Only maximum |E|+tau classes are canonized; no blanket eight-input circuit claim.'),indent=2))
