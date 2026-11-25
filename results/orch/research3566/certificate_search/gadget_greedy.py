"""Randomized, sharing-aware extraction from the finite gadget library."""
import argparse
import json
from pathlib import Path
import random
import time

p=argparse.ArgumentParser()
p.add_argument('library');p.add_argument('--seconds',type=int,default=120)
p.add_argument('--out',required=True);p.add_argument('--seed',type=int,default=1)
p.add_argument('--helper-objective',action='store_true')
args=p.parse_args();rng=random.Random(args.seed)
d=json.loads(Path(args.library).read_text())
n=d['graph']['n'];edges=d['graph']['edges'];nodes=d['nodes'];recipes=d['recipes']
clean=d['clean'];active=d['active'];m=len(edges);goal=(1<<m)-1
nonclean=[k for k in active if nodes[k]['kind'] not in ('clean','guarded')]
upper=d['graph']['star_cover_upper'];start=time.monotonic();attempt=0;best=None
auditor=None;proxy={}
if args.helper_objective:
    import importlib.util
    spec=importlib.util.spec_from_file_location('helper_audit',Path('../gate_elimination/reusable_helpers.py'))
    auditor=importlib.util.module_from_spec(spec);spec.loader.exec_module(auditor)
    (adj,colors,components),tau,F=auditor.graph_data(n,tuple(sorted(tuple(sorted(e)) for e in edges)))
    vals=list(auditor.inputs(n))+[0]*(len(nodes)-n)
    for k in nonclean:
        op,a,b=recipes[k][0]
        vals[k]=vals[a]&vals[b] if op=='and' else vals[a]|vals[b]
        S=tuple(i for i in range(n) if vals[k]>>(1<<i)&1)
        if len(S)<2 or len({colors[i] for i in S})>1:continue
        if any(len(set(S)&a)>1 for a in adj):continue
        ors=0
        for i in S:ors|=vals[i]
        if not vals[k]&~(ors|F):proxy[k]=S
    print('PROXY_HELPER_NODES',len(proxy),flush=True)

def plans(known):
    pp=[{} for _ in nodes]
    for k in nonclean+clean:
        if k in known:
            continue
        opt=None
        for op,a,b in recipes[k]:
            v=pp[a]|pp[b]|{k:(op,a,b)}
            if opt is None or len(v)<len(opt):
                opt=v
        pp[k]=opt if opt is not None else {}
    return pp

def extract(chosen,terms):
    wire={i:i for i in range(n)};gates=[];visiting=set()
    def emit(k):
        if k in wire:return
        assert k not in visiting
        visiting.add(k)
        op,a,b=chosen[k];emit(a);emit(b)
        gates.append((op,wire[a],wire[b]));wire[k]=n+len(gates)-1
        visiting.remove(k)
    for k in terms:emit(k)
    out=wire[terms[0]]
    for k in terms[1:]:
        gates.append(('or',out,wire[k]));out=n+len(gates)-1
    return gates,out

while time.monotonic()-start<args.seconds:
    attempt+=1;known={};terms=[];covered=0
    exponent=rng.choice([0.85,1.0,1.0,1.1,1.25,1.5,1.8])
    reward_weight=rng.choice([.5,.8,1.,1.,1.25,1.5]) if args.helper_objective else 0
    forced=rng.randrange(3) if attempt>1 else 0
    while covered!=goal:
        pp=plans(known)
        have_helpers={proxy[k] for k in known if k in proxy}
        opts=[]
        for k in clean:
            new=(nodes[k]['value']&~covered).bit_count()
            if not new:continue
            cost=len(pp[k])+1
            if reward_weight:
                new_helpers={proxy[j] for j in pp[k] if j in proxy}-have_helpers
                cost=max(.05,cost-reward_weight*sum(len(S)-1 for S in new_helpers))
            weight=cost/(new**exponent)
            if attempt>1:weight*=rng.uniform(0.8,1.2)
            if forced and nodes[k]['kind']=='guarded':weight*=.35
            opts.append((weight,k))
        _,k=min(opts)
        known.update(pp[k]);terms.append(k);covered|=nodes[k]['value']
        forced=max(0,forced-1)
    rng.shuffle(terms)
    j=0
    while j<len(terms):
        cov=0
        for i,k in enumerate(terms):
            if i!=j:cov|=nodes[k]['value']
        if cov==goal:terms.pop(j)
        else:j+=1
    gates,out=extract(known,terms)
    audit=auditor.audit_case(n,edges,gates,out,subset_budget_s=.05,build_extension=False) if auditor else None
    profit=audit['best_extension_profit'] if audit else upper-len(gates)
    if best is None or profit>best['profit'] or (profit==best['profit'] and len(gates)<best['size']):
        best={'size':len(gates),'gates':gates,'output':out,'terms':terms,
              'profit':profit,'helper_audit':audit,'attempt':attempt,'seconds':time.monotonic()-start}
        print(json.dumps({'new_best':best['size'],'profit':profit,'attempt':attempt,'seconds':best['seconds']}),flush=True)
        Path(args.out).write_text(json.dumps({'graph':d['graph'],'best':best},indent=2))
    if auditor and profit>0:
        if n+2*len(audit['best_helpers'])<=22:
            best['helper_audit']=auditor.audit_case(n,edges,gates,out,subset_budget_s=.5,build_extension=True)
        Path(args.out).write_text(json.dumps({'graph':d['graph'],'best':best},indent=2))
        print('FOUND_POSITIVE_EXTENSION_PROFIT',profit,flush=True)
        break
    if len(gates)<upper:
        wrong=[]
        for s in range(1<<n):
            w=[bool(s>>i&1) for i in range(n)]
            for op,a,b in gates:w.append((w[a] and w[b]) if op=='and' else (w[a] or w[b]))
            want=any(s>>a&1 and s>>b&1 for a,b in edges)
            if w[out]!=want:wrong.append(s)
        best['wrong_rows']=wrong
        Path(args.out).write_text(json.dumps({'graph':d['graph'],'best':best},indent=2))
        assert not wrong
        print('FOUND_FULLY_VERIFIED_IMPROVEMENT',flush=True)
        break
print(json.dumps({'attempts':attempt,'seconds':time.monotonic()-start,'best':best['size']}),flush=True)
