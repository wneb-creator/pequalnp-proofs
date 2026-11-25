import argparse,json,random,sys,time
from pathlib import Path
import counterexample_subset_roots as r
s=r.s


def coreseed(rng,roots=7,control=False):
    assert roots in (7,8)
    ca,cd=rng.sample(range(s.K),2)
    b=next(iter(s.NEIGHBORS[ca]&s.NEIGHBORS[cd]))
    a,d=s.B+ca,s.B+cd;dirty=[];rootargs=[];candidates=[]
    def add(op,x,y):dirty.append((op,x,y));return s.NV+len(dirty)-1
    mixed=add(False,a,b);shared=add(False,a,d);g=add(True,mixed,shared)
    order=list(range(s.K));rng.shuffle(order)
    for k in order:
        neighbors=sorted(s.NEIGHBORS[k]-({b} if k==cd or (roots==8 and k==ca) else set()));rng.shuffle(neighbors)
        right=neighbors[0]
        for neighbor in neighbors[1:]:
            candidates.append(len(dirty));right=add(False,right,neighbor)
        rootargs.append((g if k==ca else s.B+k,right))
    if roots==8:rootargs.append((shared,b))
    assert len(dirty)==30-roots
    control_size=29+roots
    deleted=rng.sample(candidates,0 if control else control_size-33)
    sides={i:(0 if dirty[i][1]>=s.NV else rng.randrange(2)) for i in deleted}
    mapping={v:v for v in range(s.NV)};pruned=[]
    for i,(op,x,y) in enumerate(dirty):
        if i in sides:mapping[s.NV+i]=mapping[(x,y)[sides[i]]]
        else:
            mapping[s.NV+i]=s.NV+len(pruned);pruned.append((op,mapping[x],mapping[y]))
    args=[(mapping[x],mapping[y]) for x,y in rootargs]
    mapping={v:v for v in range(s.NV)};ordered=[];pending=set(range(len(pruned)))
    while pending:
        ready=[i for i in pending if all(w in mapping for w in pruned[i][1:])]
        i=min(ready,key=lambda i:(max(mapping[w] for w in pruned[i][1:]),min(mapping[w] for w in pruned[i][1:]),i))
        op,x,y=pruned[i];x,y=sorted((mapping[x],mapping[y]))
        mapping[s.NV+i]=s.NV+len(ordered);ordered.append((op,x,y));pending.remove(i)
    args=[tuple(sorted((mapping[x],mapping[y]))) for x,y in args];args.sort(key=lambda p:(p[1],p[0]))
    circuit=ordered+[(True,x,y) for x,y in args];dirty_count=len(ordered);output=s.NV+dirty_count
    for k in range(1,roots):
        circuit.append((False,output,s.NV+dirty_count+k));output=s.NV+len(circuit)-1
    assert len(circuit)==(control_size if control else 33)
    assert sum(op for op,_,_ in circuit[:dirty_count])==1
    if control:r.verify(circuit,roots)
    return circuit,dict(centers=[ca,cd],shared_line=b,center_order=order,deleted=deleted,sides=sides,
                        dirty=dirty_count,roots=roots,phase_family=f'strongnormal{control_size}_minus{control_size-33}')


def main():
    if '--control' not in sys.argv:
        r.seed=coreseed;r.main();return
    ap=argparse.ArgumentParser();ap.add_argument('--solver',required=True);ap.add_argument('--out',required=True)
    ap.add_argument('--seed',type=int,default=76);ap.add_argument('--roots',type=int,choices=[7,8],default=7)
    ap.add_argument('--control',action='store_true');args=ap.parse_args()
    root=Path(args.out);root.mkdir(parents=True,exist_ok=True)
    circuit,details=coreseed(random.Random(args.seed),args.roots,True);e=r.Encoding(circuit,args.roots,True)
    server=s.inc.Server(args.solver,e,root,0);start=time.monotonic()
    try:
        status,model,span=server.solve(60,1000000);assert status==10
        candidate=e.decode(model);r.verify(candidate,args.roots);full=s.embed(candidate);assert full['gates']==len(circuit)+30
        assert any(op for op,_,_ in candidate[:30-args.roots])
        server.add([[-e.truth]]);contradiction,_,last_span=server.solve(30,500000);assert contradiction==20
        record=dict(status=status,seconds=time.monotonic()-start,variables=e.count,clauses=server.total_clauses,
                    module_gates=len(circuit),full_plane_gates=len(circuit)+30,circuit=candidate,full_plane=full,seed_details=details,
                    seed_circuit=circuit,positive=28,negative=89,full_boundary_errors=0,require_dirty_and=True,
                    distinct_operands=True,log_span=span,contradiction_status=contradiction,contradiction_log_span=last_span)
        (root/'control.json').write_text(json.dumps(record,indent=2)+'\n')
        print(json.dumps({k:v for k,v in record.items() if k not in ('circuit','full_plane','seed_circuit')}),flush=True)
        print('STRONGNORMAL DIRTY-AND POSITIVE CONTROL PASSED',flush=True)
    finally:server.close()

if __name__=='__main__':main()
