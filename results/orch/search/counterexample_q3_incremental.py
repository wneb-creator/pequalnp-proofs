import argparse
import json
import random
import subprocess
import time
from pathlib import Path
import counterexample_q3_concurrent_mixed as geometry

m=geometry.m
base=geometry.base

class Encoding(m.Encoding):
    def add_pattern(self,mask):
        assert mask not in self.patterns
        assert not any(mask>>a&1 and mask>>b&1 for a,b in base.EDGES)
        t=len(self.patterns);self.patterns.append(mask)
        for i in range(len(self.seed)):self.values[i].append(self.var())
        for i in self.free:
            self.lv[i].append(self.var());self.rv[i].append(self.var())
        for i,(op,a,b) in enumerate(self.seed):
            v=self.values[i][t]
            if i not in self.free:
                l,r=self.wire(a,t),self.wire(b,t)
                if op:self.add(-v,l);self.add(-v,r);self.add(v,-l,-r)
                else:self.add(v,-l);self.add(v,-r);self.add(-v,l,r)
            else:
                l,r,o=self.lv[i][t],self.rv[i][t],self.ops[i]
                for selections,bit in ((self.lhs[i],l),(self.rhs[i],r)):
                    for j,sel in enumerate(selections):
                        w=self.wire(j,t);self.add(-sel,-bit,w);self.add(-sel,bit,-w)
                self.add(-o,-v,l);self.add(-o,-v,r);self.add(-o,v,-l,-r)
                self.add(o,v,-l);self.add(o,v,-r);self.add(o,-v,l,r)
        self.add(-self.values[-1][t])

class Server:
    def __init__(self,solver,e,root,trial):
        cnf=root/'current.cnf';phase=root/'current.phases';frozen=root/'current.frozen'
        e.write(cnf);e.write_phases(phase)
        frozen_vars=[e.truth]
        for i in e.free:frozen_vars += [e.ops[i]]+e.lhs[i]+e.rhs[i]
        frozen.write_text(' '.join(map(str,frozen_vars))+'\n')
        self.log=(root/f'trial-{trial:04d}-server.log').open('w')
        self.process=subprocess.Popen([solver,str(cnf),str(phase),str(frozen)],stdin=subprocess.PIPE,
                                      stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        self.total_clauses=len(e.clauses)
        e.clauses=[]

    def solve(self,seconds,conflicts):
        begin=self.log.tell()
        self.process.stdin.write(f'solve {seconds} {conflicts}\n');self.process.stdin.flush()
        result=None;model=''
        while True:
            line=self.process.stdout.readline()
            if not line:raise RuntimeError('incremental solver exited before OEC_DONE')
            self.log.write(line)
            if line.startswith('c OEC_RESULT '):result=int(line.split()[2])
            elif line.startswith('v '):model+=line
            elif line.strip()=='c OEC_DONE':break
        self.log.flush()
        assert result in (0,10,20)
        return result,model,(begin,self.log.tell())

    def add(self,clauses):
        self.process.stdin.write(f'add {len(clauses)}\n')
        for clause in clauses:self.process.stdin.write(' '.join(map(str,clause))+' 0\n')
        self.process.stdin.flush();self.total_clauses+=len(clauses)

    def phases(self,e):
        assignment=e.known_assignment()
        self.process.stdin.write(f'phase {len(assignment)}\n')
        self.process.stdin.write(' '.join(str(v if b else -v) for v,b in assignment.items())+'\n')
        self.process.stdin.flush()

    def close(self):
        if self.process.poll() is None:
            try:self.process.stdin.write('quit\n');self.process.stdin.flush()
            except BrokenPipeError:pass
        self.process.stdin.close()
        for line in self.process.stdout:self.log.write(line)
        self.process.wait();self.log.close()
        return self.process.returncode

def initial(seed,free,details,puncture_count):
    punctures=[]
    if puncture_count==4:punctures=[mask for (p,l),mask in geometry.PUNCTURES.items() if p==0]
    elif puncture_count==16:punctures=geometry.runner.additional_negatives(details)
    elif puncture_count==52:punctures=list(geometry.PUNCTURES.values())
    negatives=list(dict.fromkeys([base.NEGATIVE[0],base.NEGATIVE[-1]]+[1<<v for v in range(base.NINPUT)]+
                                punctures))
    e=Encoding(seed,free,base.POSITIVE+negatives);e.least_or_strict();e.least_singleton()
    return e,negatives

def report_circuit(circuit):
    actual=base.evaluate(circuit,base.POSITIVE+base.NEGATIVE)
    pm=(1<<len(base.POSITIVE))-1
    assert actual&pm==pm
    assert not m.reads_pair(circuit,m.forced_pair)
    return [mask for i,mask in enumerate(base.NEGATIVE) if actual>>(len(base.POSITIVE)+i)&1]

def control(args,root):
    seed,free,details=geometry.neighborhood(random.Random(76),0,0)
    e,negatives=initial(seed,free,details,args.punctures)
    server=Server(args.solver,e,root,0)
    reports=[]
    try:
        start=time.monotonic()
        status,model,span=server.solve(60,1000000)
        assert status==10
        circuit=e.decode(model);bad=report_circuit(circuit)
        reports.append(dict(stage='initial',status=status,false_boundaries=len(bad),log_span=span))
        assert not bad
        e.seed=circuit
        for mask in base.NEGATIVE:
            if mask in e.patterns:continue
            e.add_pattern(mask)
            assignment=e.known_assignment()
            assert all(any(assignment[abs(v)]==(v>0) for v in c) for c in e.clauses)
            server.add(e.clauses);e.clauses=[];negatives.append(mask)
            server.phases(e)
            status,model,span=server.solve(60,1000000)
            assert status==10
            circuit=e.decode(model);bad=report_circuit(circuit)
            reports.append(dict(stage='after_new_negative',status=status,false_boundaries=len(bad),log_span=span))
            assert not bad
            e.seed=circuit
            break
        server.add([[-e.truth]])
        status,model,span=server.solve(60,1000000)
        assert status==20
        reports.append(dict(stage='contradictory_unit',status=status,log_span=span))
        report=dict(seconds=time.monotonic()-start,queries=reports,circuit=circuit,details=details,
                    variables=e.count,clauses=server.total_clauses)
        (root/'control.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
    finally:server.close()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--solver',required=True);ap.add_argument('--out',required=True)
    ap.add_argument('--seconds',type=int,default=600);ap.add_argument('--seed',type=int,default=76)
    ap.add_argument('--query-seconds',type=int,default=30);ap.add_argument('--maximal-period',type=int,default=4)
    ap.add_argument('--punctures',type=int,choices=[0,4,16,52],default=4)
    ap.add_argument('--unknown-retries',type=int,default=2)
    ap.add_argument('--control',action='store_true');args=ap.parse_args()
    root=Path(args.out);root.mkdir(parents=True,exist_ok=True)
    if args.control:control(args,root);return
    rng=random.Random(args.seed);start=time.monotonic();trial=0
    while time.monotonic()-start<args.seconds:
        seed,free,details=geometry.neighborhood(rng,trial)
        e,negatives=initial(seed,free,details,args.punctures);server=Server(args.solver,e,root,trial)
        try:
            unknowns=0;cuts=0
            for round_index in range(128):
                remaining=args.seconds-(time.monotonic()-start)
                if remaining<=0:break
                record=dict(trial=trial,round=round_index,free_gates=free,seed_circuit=e.seed,
                            negative_patterns=negatives.copy(),variables=e.count,clauses=server.total_clauses,**details)
                prefix=root/f'trial-{trial:04d}-round-{round_index}'
                limit=max(1,min(args.query_seconds,int(remaining)))
                status,model,span=server.solve(limit,500000)
                record.update(status=status,seconds=time.monotonic()-start,solver_limit=limit,log_span=span)
                if status==10:
                    circuit=e.decode(model);bad=report_circuit(circuit)
                    record['false_positive_boundaries']=len(bad);record['circuit']=circuit
                prefix.with_suffix('.json').write_text(json.dumps(record)+'\n')
                print(json.dumps({k:v for k,v in record.items() if k not in ('seed_circuit','negative_patterns','circuit')}),flush=True)
                if status==0 and unknowns<args.unknown_retries:
                    unknowns+=1
                    continue
                if status!=10:break
                unknowns=0
                if not bad:
                    witness=dict(circuit=circuit,edges=base.EDGES,n=base.NINPUT,output=base.NINPUT+len(circuit)-1,
                                 forced_nonread1_edge=m.forced_pair,all_boundary_patterns=756,seed=args.seed)
                    (root/'witness.json').write_text(json.dumps(witness,indent=2)+'\n')
                    print('FOUND COUNTEREXAMPLE CANDIDATE',flush=True);return
                preferred=[mask for mask in bad if mask in geometry.runner.priority_negatives]
                bad_mask=rng.choice(preferred or bad)
                use_maximal=args.maximal_period>0 and (cuts+1)%args.maximal_period==0
                order=list(range(base.NINPUT));rng.shuffle(order)
                for vertex in ([] if use_maximal else order):
                    if bad_mask>>vertex&1:
                        smaller=bad_mask&~(1<<vertex)
                        if base.evaluate(circuit,[smaller])&1:bad_mask=smaller
                assert bad_mask not in negatives
                print(json.dumps(dict(event='false_cut',kind='maximal' if use_maximal else 'minimal',
                                      trial=trial,round=round_index,vertices=bad_mask.bit_count(),mask=bad_mask)),flush=True)
                cuts+=1
                e.seed=circuit;e.add_pattern(bad_mask);negatives.append(bad_mask)
                server.add(e.clauses);e.clauses=[];server.phases(e)
        finally:server.close()
        trial+=1
    print(json.dumps(dict(event='finished',trials=trial,seconds=time.monotonic()-start)),flush=True)

if __name__=='__main__':main()
