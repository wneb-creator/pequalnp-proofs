import argparse,json,random,time
from pathlib import Path
import counterexample_subset_full as s


def canonical(circuit):
    required=set();todo=[len(circuit)-1]
    while todo:
        i=todo.pop()
        if i in required:continue
        required.add(i)
        for w in circuit[i][1:]:
            if w>=s.NV:todo.append(w-s.NV)
    assert len(required)==len(circuit)
    mapping={v:v for v in range(s.NV)};result=[];pending=set(required)
    while pending:
        ready=[i for i in pending if all(w in mapping for w in circuit[i][1:])]
        i=min(ready,key=lambda i:(max(mapping[w] for w in circuit[i][1:]),min(mapping[w] for w in circuit[i][1:]),i))
        op,a,b=circuit[i];a,b=sorted((mapping[a],mapping[b]))
        mapping[s.NV+i]=s.NV+len(result);result.append((op,a,b));pending.remove(i)
    assert mapping[s.NV+len(circuit)-1]==s.NV+len(circuit)-1
    assert all(result[i-1][2]<=result[i][2] for i in range(1,len(result)))
    assert s.base.evaluate(circuit,s.POS+s.NEG)==s.base.evaluate(result,s.POS+s.NEG)
    return result


def seed(rng,remove):
    gates=[];stars=[];candidates=[]
    def add(op,a,b):gates.append((op,a,b));return s.NV+len(gates)-1
    order=list(range(s.K));rng.shuffle(order)
    for k in order:
        terms=sorted(s.NEIGHBORS[k]);rng.shuffle(terms);value=terms[0]
        for term in terms[1:]:
            candidates.append(len(gates));value=add(False,value,term)
        stars.append(add(True,s.B+k,value))
    rng.shuffle(stars);output=stars[0]
    for w in stars[1:]:output=add(False,output,w)
    assert len(gates)==34 and s.base.evaluate(gates,s.POS+s.NEG)==s.TARGET
    removed=rng.sample(candidates,remove);sides={i:(0 if gates[i][1]>=s.NV else rng.randrange(2)) for i in removed}
    mapping={v:v for v in range(s.NV)};new=[]
    for i,(op,a,b) in enumerate(gates):
        if i in sides:mapping[s.NV+i]=mapping[(a,b)[sides[i]]]
        else:
            mapping[s.NV+i]=s.NV+len(new);new.append((op,mapping[a],mapping[b]))
    return canonical(new),dict(center_order=order,removed=removed,sides=sides)


class Encoding(s.BaseEncoding):
    def __init__(self,circuit,ordered=True):
        super().__init__(circuit,list(range(len(circuit))),s.POS+s.NEG+[1<<i for i in range(s.NV)])
        self.least_or_strict();self.least_singleton()
        self.below=[-self.truth]*s.NV+[self.var() for _ in circuit]
        for i in range(len(circuit)):
            b=self.below[s.NV+i];negative=self.values[i][len(s.POS):len(s.POS)+len(s.NEG)]
            for v in negative:self.add(-b,-v)
            self.add(b,*negative)
            flags=[]
            for selections in (self.lhs[i],self.rhs[i]):
                flag=self.var();flags.append(flag)
                for j,sel in enumerate(selections):
                    w=self.below[j];self.add(-sel,-flag,w);self.add(-sel,flag,-w)
            left,right=flags;o=self.ops[i]
            self.add(-o,-left);self.add(-o,-right)
            self.add(o,-left,right);self.add(o,left,-right)
        if ordered:
            for i in range(1,len(circuit)):
                for a,previous in enumerate(self.rhs[i-1]):
                    for b,current in enumerate(self.rhs[i][:a]):self.add(-previous,-current)


def verify(circuit):
    assert s.base.evaluate(circuit,s.POS+s.NEG)==s.TARGET
    bits=[sum(1<<t for t,p in enumerate(s.NEG) if p>>i&1) for i in range(s.NV)]
    for op,a,b in circuit:
        if op:assert bits[a]!=0 and bits[b]!=0
        else:assert (bits[a]==0)==(bits[b]==0)
        bits.append(bits[a]&bits[b] if op else bits[a]|bits[b])


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--solver',required=True);ap.add_argument('--out',required=True)
    ap.add_argument('--seconds',type=int,default=600);ap.add_argument('--query-seconds',type=int,default=30)
    ap.add_argument('--seed',type=int,default=76);ap.add_argument('--control',action='store_true')
    ap.add_argument('--unordered',action='store_true');args=ap.parse_args()
    root=Path(args.out);root.mkdir(parents=True,exist_ok=True);rng=random.Random(args.seed)
    circuit,details=seed(rng,0 if args.control else 1);e=Encoding(circuit,not args.unordered)
    server=s.inc.Server(args.solver,e,root,0);start=time.monotonic();query=0
    try:
        while time.monotonic()-start<args.seconds:
            limit=max(1,min(args.query_seconds,int(args.seconds-(time.monotonic()-start))))
            status,model,span=server.solve(limit,500000)
            record=dict(query=query,status=status,seconds=time.monotonic()-start,log_span=span,
                        variables=e.count,clauses=server.total_clauses,seed_circuit=e.seed,seed_details=details,
                        positive=len(s.POS),maximal_negative=len(s.NEG),singletons=s.NV,target_gates=len(circuit),
                        strong_normality=True,rhs_ordered=not args.unordered)
            if status==10:
                candidate=e.decode(model);verify(candidate);full=s.embed(candidate)
                record.update(circuit=candidate,full_boundary_errors=0,full_plane=full)
            (root/f'query-{query:04d}.json').write_text(json.dumps(record)+'\n')
            print(json.dumps({k:v for k,v in record.items() if k not in ('seed_circuit','circuit','full_plane')}),flush=True)
            if status==10:
                if args.control:
                    assert len(candidate)==34 and full['gates']==64
                    server.add([[-e.truth]]);contradiction,_,span=server.solve(30,500000);assert contradiction==20
                    record.update(contradiction_status=contradiction,contradiction_log_span=span)
                    (root/'control.json').write_text(json.dumps(record,indent=2)+'\n')
                    print('NORMAL CANONICAL34 POSITIVE CONTROL PASSED',flush=True)
                else:
                    assert len(candidate)==33 and full['gates']==63
                    (root/'module-witness.json').write_text(json.dumps(record,indent=2)+'\n')
                    (root/'full-plane-witness.json').write_text(json.dumps(full,indent=2)+'\n')
                    print('FOUND COUNTEREXAMPLE CANDIDATE: normal module33, fullplane63',flush=True)
                return
            if status==20:
                print('UNSAT for encoded exact-size normal class; not a Lean proof',flush=True);return
            query+=1
            if not args.control and query%3==0:
                circuit,details=seed(rng,1);e.seed=circuit;server.phases(e)
        print(json.dumps(dict(event='finished',queries=query,seconds=time.monotonic()-start)),flush=True)
    finally:server.close()

if __name__=='__main__':main()
