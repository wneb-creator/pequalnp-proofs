import argparse,json,random,time
from pathlib import Path
import counterexample_subset_full as s


def seed(rng,roots,control=False):
    assert roots in (6,7,8)
    groups=[([k],sorted(s.NEIGHBORS[k])) for k in range(s.K)]
    if roots==6:
        a,b=rng.sample(range(s.K),2)
        groups=[g for k,g in enumerate(groups) if k not in (a,b)]
        groups.append(([a,b],sorted(s.NEIGHBORS[a]|s.NEIGHBORS[b])))
    elif roots==8:
        a=rng.randrange(s.K);terms=groups[a][1];rng.shuffle(terms)
        groups[a:a+1]=[([a],terms[:2]),([a],terms[2:])]
    rng.shuffle(groups);dirty=[];rootargs=[];candidates=[]
    def add(a,b):dirty.append((False,a,b));return s.NV+len(dirty)-1
    for centers,neighbors in groups:
        rng.shuffle(centers);rng.shuffle(neighbors)
        left=s.B+centers[0]
        for center in centers[1:]:left=add(left,s.B+center)
        right=neighbors[0]
        for neighbor in neighbors[1:]:
            candidates.append(len(dirty));right=add(right,neighbor)
        rootargs.append((left,right))
    target=34 if control else 33;wanted=target-(2*roots-1)
    assert wanted<=len(dirty)
    deleted=rng.sample(candidates,len(dirty)-wanted)
    sides={i:(0 if dirty[i][1]>=s.NV else rng.randrange(2)) for i in deleted}
    mapping={v:v for v in range(s.NV)};pruned=[]
    for i,(op,a,b) in enumerate(dirty):
        if i in sides:mapping[s.NV+i]=mapping[(a,b)[sides[i]]]
        else:
            mapping[s.NV+i]=s.NV+len(pruned);pruned.append((op,mapping[a],mapping[b]))
    args=[(mapping[a],mapping[b]) for a,b in rootargs]
    mapping={v:v for v in range(s.NV)};ordered=[];pending=set(range(len(pruned)))
    while pending:
        ready=[i for i in pending if all(w in mapping for w in pruned[i][1:])]
        i=min(ready,key=lambda i:(max(mapping[w] for w in pruned[i][1:]),min(mapping[w] for w in pruned[i][1:]),i))
        op,a,b=pruned[i];a,b=sorted((mapping[a],mapping[b]))
        mapping[s.NV+i]=s.NV+len(ordered);ordered.append((op,a,b));pending.remove(i)
    args=[tuple(sorted((mapping[a],mapping[b]))) for a,b in args]
    args.sort(key=lambda p:(p[1],p[0]))
    circuit=ordered+[(True,a,b) for a,b in args];d=len(ordered)
    output=s.NV+d
    for k in range(1,roots):
        circuit.append((False,output,s.NV+d+k));output=s.NV+len(circuit)-1
    assert len(circuit)==target and d==wanted
    if control:assert s.base.evaluate(circuit,s.POS+s.NEG)==s.TARGET
    return circuit,dict(groups=groups,deleted=deleted,sides=sides,dirty=d,roots=roots)


class Encoding(s.BaseEncoding):
    def __init__(self,circuit,roots,require_dirty_and=False):
        self.dirty_count=len(circuit)-(2*roots-1);d=self.dirty_count
        super().__init__(circuit,list(range(d+roots)),s.POS+s.NEG+[1<<i for i in range(s.NV)])
        self.least_or_strict();self.least_singleton()
        for i in self.free:
            for left,right in zip(self.lhs[i],self.rhs[i]):self.add(-left,-right)
        neg=range(len(s.POS),len(s.POS)+len(s.NEG))
        for i in range(d):self.add(*[self.values[i][t] for t in neg])
        for i in range(d,d+roots):
            self.add(self.ops[i])
            for selections in (self.lhs[i],self.rhs[i]):
                for sel in selections[s.NV+d:]:self.add(-sel)
            for t in neg:self.add(-self.values[i][t])
        for block in (range(d),range(d,d+roots)):
            for i in list(block)[1:]:
                for a,previous in enumerate(self.rhs[i-1]):
                    for current in self.rhs[i][:a]:self.add(-previous,-current)
        # Each clean root in a least circuit has a positive edge not accepted by any other root.
        for i in range(d,d+roots):
            witnesses=[]
            for t in range(len(s.POS)):
                w=self.var();witnesses.append(w)
                terms=[self.values[i][t]]+[-self.values[j][t] for j in range(d,d+roots) if j!=i]
                for term in terms:self.add(-w,term)
                self.add(w,*[-term for term in terms])
            self.add(*witnesses)
        if require_dirty_and:self.add(*[self.ops[i] for i in range(d)])


def verify(circuit,roots):
    assert s.base.evaluate(circuit,s.POS+s.NEG)==s.TARGET
    d=len(circuit)-(2*roots-1)
    words=[sum(1<<t for t,p in enumerate(s.POS+s.NEG) if p>>i&1) for i in range(s.NV)]
    for i,(op,a,b) in enumerate(circuit):
        v=words[a]&words[b] if op else words[a]|words[b];words.append(v)
        if i<d:assert v>>len(s.POS)!=0
        elif i<d+roots:assert op and a<s.NV+d and b<s.NV+d and v>>len(s.POS)==0
        else:assert not op
    for i in range(d,d+roots):
        others=0
        for j in range(d,d+roots):
            if j!=i:others|=words[s.NV+j]
        assert words[s.NV+i]&~others&s.TARGET


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--solver',required=True);ap.add_argument('--out',required=True)
    ap.add_argument('--seconds',type=int,default=600);ap.add_argument('--query-seconds',type=int,default=30)
    ap.add_argument('--seed',type=int,default=76);ap.add_argument('--roots',type=int,choices=[6,7,8],default=7)
    ap.add_argument('--control',action='store_true');ap.add_argument('--require-dirty-and',action='store_true')
    args=ap.parse_args();assert not args.control or args.roots==7
    root=Path(args.out);root.mkdir(parents=True,exist_ok=True);rng=random.Random(args.seed)
    circuit,details=seed(rng,args.roots,args.control);e=Encoding(circuit,args.roots,args.require_dirty_and)
    server=s.inc.Server(args.solver,e,root,0);start=time.monotonic();query=0
    try:
        while time.monotonic()-start<args.seconds:
            limit=max(1,min(args.query_seconds,int(args.seconds-(time.monotonic()-start))))
            status,model,span=server.solve(limit,500000)
            record=dict(query=query,status=status,seconds=time.monotonic()-start,log_span=span,
                        variables=e.count,clauses=server.total_clauses,seed_circuit=e.seed,seed_details=details,
                        positive=len(s.POS),maximal_negative=len(s.NEG),singletons=s.NV,target_gates=len(circuit),
                        root_count=args.roots,dirty_count=e.dirty_count,require_dirty_and=args.require_dirty_and,distinct_operands=True)
            if status==10:
                candidate=e.decode(model);verify(candidate,args.roots);full=s.embed(candidate)
                record.update(circuit=candidate,full_boundary_errors=0,full_plane=full)
            (root/f'query-{query:04d}.json').write_text(json.dumps(record)+'\n')
            print(json.dumps({k:v for k,v in record.items() if k not in ('seed_circuit','circuit','full_plane')}),flush=True)
            if status==10:
                if args.control:
                    assert len(candidate)==34 and full['gates']==64
                    server.add([[-e.truth]]);contradiction,_,span=server.solve(30,500000);assert contradiction==20
                    record.update(contradiction_status=contradiction,contradiction_log_span=span)
                    (root/'control.json').write_text(json.dumps(record,indent=2)+'\n')
                    print('ROOT-SHAPE CANONICAL34 POSITIVE CONTROL PASSED',flush=True)
                else:
                    assert len(candidate)==33 and full['gates']==63
                    (root/'module-witness.json').write_text(json.dumps(record,indent=2)+'\n')
                    (root/'full-plane-witness.json').write_text(json.dumps(full,indent=2)+'\n')
                    print('FOUND COUNTEREXAMPLE CANDIDATE: root-shape module33, fullplane63',flush=True)
                return
            if status==20:
                print('UNSAT for encoded exact-size root-shape class; not a Lean proof',flush=True);return
            query+=1
            if not args.control and query%3==0:
                circuit,details=seed(rng,args.roots);e.seed=circuit;server.phases(e)
        print(json.dumps(dict(event='finished',queries=query,seconds=time.monotonic()-start)),flush=True)
    finally:server.close()

if __name__=='__main__':main()
