import argparse
import json
import random
import time
from pathlib import Path
import counterexample_q3_incremental as inc
import counterexample_q3_repair as plane

CENTERS=[0,1,2,3,4,6,7]
LINE_LABELS=[l for l,ps in enumerate(plane.LINES) if ps & set(CENTERS)]
B=len(LINE_LABELS);K=len(CENTERS)
NEIGHBORS=[{i for i,l in enumerate(LINE_LABELS) if p in plane.LINES[l]} for p in CENTERS]
NV=B+K
EDGES=[(i,B+k) for k,ns in enumerate(NEIGHBORS) for i in sorted(ns)]
POS=[(1<<a)|(1<<b) for a,b in EDGES]
NEG=[];closures=[]
for selected in range(1<<K):
    first=sum(1<<i for i in range(B) if not any(selected>>k&1 and i in ns for k,ns in enumerate(NEIGHBORS)))
    closure=sum(1<<k for k,ns in enumerate(NEIGHBORS) if not any(first>>i&1 for i in ns))
    if closure==selected:NEG.append(first|(selected<<B))
    closures.append((first|(selected<<B),first|(closure<<B)))
assert len(EDGES)==28 and len(NEG)==89
assert all(s&~t==0 and t in set(NEG) for s,t in closures)
base=inc.base
base.NINPUT=NV;base.EDGES=EDGES;base.POSITIVE=POS;base.NEGATIVE=NEG
TARGET=(1<<len(EDGES))-1
HIDDEN=min(NEIGHBORS[0])
BaseEncoding=inc.m.Encoding.__bases__[0]
assert BaseEncoding.__module__==base.__name__

def seed(rng,remove):
    pivot=rng.choice(sorted(NEIGHBORS[0]-{HIDDEN}))
    gates=[]
    def add(op,a,b):gates.append((op,a,b));return NV+len(gates)-1
    g=add(False,pivot,add(True,HIDDEN,B))
    order=list(range(K));rng.shuffle(order)
    stars=[];candidates=[]
    for k in order:
        terms=[g if i==pivot else i for i in sorted(NEIGHBORS[k]) if not(k==0 and i==HIDDEN)]
        rng.shuffle(terms);value=terms[0]
        for term in terms[1:]:
            candidates.append(len(gates));value=add(False,value,term)
        stars.append(add(True,B+k,value))
    output=stars[0]
    for w in stars[1:]:output=add(False,output,w)
    assert len(gates)==5*K and base.evaluate(gates,POS+NEG)==TARGET
    removed=sorted(rng.sample(candidates,remove));sides={i:rng.randrange(2) for i in removed}
    mapping={i:i for i in range(NV)};result=[]
    for i,(op,a,b) in enumerate(gates):
        if i in sides:mapping[NV+i]=mapping[(a,b)[sides[i]]]
        else:
            mapping[NV+i]=NV+len(result);result.append((op,mapping[a],mapping[b]))
    assert len(result)==5*K-remove
    return result,dict(pivot=pivot,hidden_edge=(HIDDEN,B),center_order=order,removed=removed,sides=sides)

def encoding(circuit):
    patterns=POS+NEG+[1<<i for i in range(NV)]
    e=BaseEncoding(circuit,list(range(len(circuit))),patterns)
    e.least_or_strict();e.least_singleton()
    return e

def embed(circuit):
    rec={i:13+l for i,l in enumerate(LINE_LABELS)}
    rec.update({B+k:p for k,p in enumerate(CENTERS)})
    full=[]
    for i,(op,a,b) in enumerate(circuit):
        rec[NV+i]=26+len(full);full.append((op,rec[a],rec[b]))
    output=26+len(full)-1
    for p in sorted(set(range(13))-set(CENTERS)):
        lines=[13+l for l,ps in enumerate(plane.LINES) if p in ps]
        v=lines[0]
        for u in lines[1:]:full.append((False,v,u));v=26+len(full)-1
        full.append((True,p,v));w=26+len(full)-1
        full.append((False,output,w));output=26+len(full)-1
    assert len(full)==len(circuit)+5*(13-K)
    assert plane.evaluate(full,plane.POSITIVE+plane.NEGATIVE)==(1<<52)-1
    return dict(n=26,circuit=full,output=output,gates=len(full),all_boundary_patterns=756,
                module_gate_count=len(circuit),subset_points=CENTERS,subset_lines=LINE_LABELS)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--solver',required=True);ap.add_argument('--out',required=True)
    ap.add_argument('--seconds',type=int,default=600);ap.add_argument('--query-seconds',type=int,default=30)
    ap.add_argument('--seed',type=int,default=76);ap.add_argument('--control',action='store_true');args=ap.parse_args()
    root=Path(args.out);root.mkdir(parents=True,exist_ok=True)
    rng=random.Random(args.seed);circuit,details=seed(rng,0 if args.control else 2)
    e=encoding(circuit);server=inc.Server(args.solver,e,root,0);start=time.monotonic();query=0
    try:
        while time.monotonic()-start<args.seconds:
            limit=max(1,min(args.query_seconds,int(args.seconds-(time.monotonic()-start))))
            status,model,span=server.solve(limit,500000)
            record=dict(query=query,status=status,seconds=time.monotonic()-start,log_span=span,
                        variables=e.count,clauses=server.total_clauses,seed_circuit=e.seed,seed_details=details,
                        positive=len(EDGES),maximal_negative=len(NEG),singletons=NV,target_gates=len(circuit))
            if status==10:
                candidate=e.decode(model)
                assert base.evaluate(candidate,POS+NEG)==TARGET
                record['circuit']=candidate;record['full_boundary_errors']=0
            (root/f'query-{query:04d}.json').write_text(json.dumps(record)+'\n')
            print(json.dumps({k:v for k,v in record.items() if k not in ('seed_circuit','circuit')}),flush=True)
            if status==10:
                full=embed(candidate)
                if args.control:
                    assert len(candidate)==5*K and full['gates']==65
                    server.add([[-e.truth]])
                    contradiction,_,check_span=server.solve(30,500000)
                    assert contradiction==20
                    report=dict(module_gates=5*K,full_plane_gates=65,full_plane_errors=0,
                                module_errors=0,positive=len(EDGES),negative=len(NEG),contradiction_status=contradiction,
                                contradiction_log_span=check_span,seconds=time.monotonic()-start,
                                circuit=candidate,full_plane=full)
                    (root/'control.json').write_text(json.dumps(report,indent=2)+'\n')
                    print('SUBSET POSITIVE CONTROL PASSED',flush=True)
                else:
                    assert len(candidate)==5*K-2 and full['gates']==63
                    (root/'module-witness.json').write_text(json.dumps(record,indent=2)+'\n')
                    (root/'full-plane-witness.json').write_text(json.dumps(full,indent=2)+'\n')
                    print('FOUND COUNTEREXAMPLE CANDIDATE: module33, fullplane63',flush=True)
                return
            if status==20:
                print('UNSAT for the encoded exact-size class; not a Lean proof',flush=True);return
            query+=1
            if args.control:continue
            if query%3==0:
                circuit,details=seed(rng,2);e.seed=circuit;server.phases(e)
        print(json.dumps(dict(event='finished',queries=query,seconds=time.monotonic()-start)),flush=True)
    finally:server.close()

if __name__=='__main__':main()
