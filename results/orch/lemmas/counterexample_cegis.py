import sys
sys.dont_write_bytecode=True
import argparse,json,time,hashlib
from datetime import datetime,timezone
from pathlib import Path
from counterexample_sat_boundary import z3,truth,automorphisms

def run(N,k,seconds):
    n=2*N
    mask=sum(1<<(N*p+l) for p in range(N) for l in [p,(p+1)%N])
    rows=[(mask>>(N*p))&((1<<N)-1) for p in range(N)]
    assert all((rows[p]&rows[q]).bit_count()<=1 for p in range(N) for q in range(p+1,N))
    full_xs,target,forbidden=truth(N,mask)
    clean_gates=[];outs=[];values=full_xs[:]
    def upper_gate(op,a,b):
        clean_gates.append([op,a,b]);v=values[a]&values[b] if op=='and' else values[a]|values[b]
        if op=='and':assert not v&forbidden
        values.append(v);return len(values)-1
    for p in range(N):outs.append(upper_gate('and',p,upper_gate('or',N+p,N+(p+1)%N)))
    output=outs[0]
    for v in outs[1:]:output=upper_gate('or',output,v)
    assert values[output]==target
    s=z3.SolverFor('QF_BV');s.set(random_seed=3451)
    width=(n+k).bit_length();sels=[]
    for j in range(k):
        a=z3.BitVec('a'+str(j),width);b=z3.BitVec('b'+str(j),width);op=z3.Bool('and'+str(j))
        s.add(z3.ULE(a,b),z3.ULT(b,n+j));sels.append((a,b,op))
    for i in range(n):s.add(z3.Or(*[z3.Or(a==i,b==i) for a,b,op in sels]))
    for j in range(k-1):
        s.add(z3.Or(*[z3.Or(a==n+j,b==n+j) for a,b,op in sels[j+1:]]))
        a,b,op=sels[j];aa,bb,opp=sels[j+1]
        independent=z3.And(aa!=n+j,bb!=n+j)
        ordered=z3.Or(z3.ULT(a,aa),z3.And(a==aa,z3.ULT(b,bb)),z3.And(a==aa,b==bb,z3.Or(z3.Not(op),opp)))
        s.add(z3.Implies(independent,ordered))
    autos=automorphisms(N,mask)
    def transformed(v,perm):
        out=v
        for i in range(n-1,-1,-1):out=z3.If(v==i,z3.BitVecVal(perm[i],width),out)
        return out
    for perm in autos:
        if perm==tuple(range(n)):continue
        original=[];image=[]
        for a,b,op in sels:
            aa=transformed(a,perm);bb=transformed(b,perm)
            original.extend([a,b]);image.extend([z3.If(z3.ULE(aa,bb),aa,bb),z3.If(z3.ULE(aa,bb),bb,aa)])
        le=z3.BoolVal(True)
        for a,b in reversed(list(zip(original,image))):le=z3.If(a==b,le,z3.ULT(a,b))
        s.add(le)
    samples=set()
    def pick(v,wires):
        out=wires[-1]
        for i in range(len(wires)-2,-1,-1):out=z3.If(v==i,wires[i],out)
        return out
    def add_sample(x):
        if x in samples:return
        samples.add(x);wires=[z3.BoolVal(bool(x>>i&1)) for i in range(n)]
        for j,(a,b,op) in enumerate(sels):
            aa=pick(a,wires);bb=pick(b,wires);v=z3.Bool('sample'+str(x)+'gate'+str(j))
            s.add(v==z3.If(op,z3.And(aa,bb),z3.Or(aa,bb)));wires.append(v)
        s.add(wires[-1]==bool(target>>x&1))
    initial={1<<i for i in range(n)}|{(1<<p)|(1<<(N+l)) for p in range(N) for l in range(N)}
    for x in sorted(initial):add_sample(x)
    started=time.monotonic();deadline=started+seconds;round_no=0;consecutive_timeouts=0
    print(json.dumps({'event':'start','at':datetime.now(timezone.utc).isoformat(),'N':N,'mask':mask,'gates':k,'seconds':seconds,'initial_samples':sorted(samples),'automorphisms':len(autos),'verified_clean_upper':len(clean_gates),'clean_upper_circuit':clean_gates,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}),flush=True)
    while time.monotonic()<deadline:
        round_no+=1
        budget=min(120*(2**consecutive_timeouts),deadline-time.monotonic())
        s.set(timeout=max(1,int(1000*budget)));tick=time.monotonic();ans=s.check();elapsed=time.monotonic()-tick
        stats=s.statistics();record={'event':'check','round':round_no,'N':N,'mask':mask,'gates':k,'sample_count':len(samples),'status':str(ans),'budget_s':budget,'elapsed_s':elapsed,'total_elapsed_s':time.monotonic()-started,'statistics':{key:stats.get_key_value(key) for key in stats.keys()}}
        if ans==z3.unsat:
            print(json.dumps(record),flush=True);return
        if ans==z3.unknown:
            record['reason']=s.reason_unknown();print(json.dumps(record),flush=True)
            consecutive_timeouts+=1
            if consecutive_timeouts>=3:break
            continue
        consecutive_timeouts=0
        model=s.model();wires=full_xs[:];gates=[]
        for a,b,op in sels:
            aa=model.eval(a,model_completion=True).as_long();bb=model.eval(b,model_completion=True).as_long();isand=z3.is_true(model.eval(op,model_completion=True))
            assert 0<=aa<=bb<len(wires)
            value=wires[aa]&wires[bb] if isand else wires[aa]|wires[bb]
            wires.append(value);gates.append(['and' if isand else 'or',aa,bb])
        actual=wires[-1]
        assert all((actual>>x&1)==(target>>x&1) for x in samples)
        assert not target&~actual
        bad=actual&~target
        record['full_error_count']=bad.bit_count();record['candidate_circuit']=gates
        if not bad:
            record['event']='full_validated_sat';record['all_inputs_checked']=1<<n
            record['all_ANDs_clean']=all(op!='and' or not wires[n+j]&forbidden for j,(op,a,b) in enumerate(gates))
            print(json.dumps(record),flush=True);return
        new=set()
        for x in range(1<<n):
            if not bad>>x&1:continue
            maximum=x
            for i in range(n):
                enlarged=maximum|(1<<i)
                if not target>>enlarged&1:maximum=enlarged
            assert not target>>maximum&1 and actual>>maximum&1
            assert all(maximum>>i&1 or target>>(maximum|(1<<i))&1 for i in range(n))
            if maximum not in samples:new.add(maximum)
        assert new
        record['added_maximal_negative_tests']=sorted(new)
        print(json.dumps(record),flush=True)
        for x in sorted(new):add_sample(x)
    print(json.dumps({'event':'end','status':'unknown','reason':'budget or repeated timeouts','rounds':round_no,'samples':len(samples),'elapsed_s':time.monotonic()-started}),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--N',type=int,default=5);ap.add_argument('--gates',type=int,default=13);ap.add_argument('--seconds',type=float,default=1200);a=ap.parse_args()
    run(a.N,a.gates,a.seconds)
