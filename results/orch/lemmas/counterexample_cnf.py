import sys
sys.dont_write_bytecode=True
import argparse,json,hashlib,time
from pathlib import Path
from counterexample_sat_ordered import z3,truth,automorphisms

def emit(N,mask,k,clean,timeout,destination):
    assert N >= 1 and 0 < mask < (1 << (N*N)) and k >= 1
    full_xs,fulltarget,fullforbidden=truth(N,mask);n=2*N;selbits=(n+k).bit_length()
    edge_inputs={ (1<<p)|(1<<(N+l)) for p in range(N) for l in range(N) if mask>>(N*p+l)&1 }
    maximal_false={a for a in range(1<<n) if not fulltarget>>a&1 and all(a>>i&1 or fulltarget>>(a|(1<<i))&1 for i in range(n))}
    clean_inputs={a for a in range(1<<n) if fullforbidden>>a&1}
    tests=sorted(edge_inputs|maximal_false|clean_inputs)
    bits=len(tests)
    xs=[sum(1<<j for j,a in enumerate(tests) if a>>i&1) for i in range(n)]
    target=sum(1<<j for j,a in enumerate(tests) if fulltarget>>a&1)
    forbidden=sum(1<<j for j,a in enumerate(tests) if a in clean_inputs)
    s=z3.SolverFor('QF_BV');s.set(timeout=int(timeout*1000));s.set(random_seed=3451)
    ws=[z3.BitVecVal(x,bits) for x in xs];sels=[]
    def pick(v,values):
        r=values[-1]
        for i in range(len(values)-2,-1,-1):r=z3.If(v==i,values[i],r)
        return r
    for j in range(k):
        a=z3.BitVec('a'+str(j),selbits);b=z3.BitVec('b'+str(j),selbits);op=z3.Bool('and'+str(j));v=z3.BitVec('w'+str(j),bits)
        s.add(z3.ULT(b,n+j),z3.ULE(a,b))
        va=pick(a,ws);vb=pick(b,ws)
        s.add(v==z3.If(op,va&vb,va|vb))
        if clean:s.add(z3.Implies(op,v&z3.BitVecVal(forbidden,bits)==0))
        ws.append(v);sels.append((a,b,op))
    for i in range(n):
        if any(((fulltarget>>a)^(fulltarget>>(a^(1<<i))))&1 for a in range(1<<n)):
            s.add(z3.Or(*[z3.Or(a==i,b==i) for a,b,op in sels]))
    for j in range(k-1):
        s.add(z3.Or(*[z3.Or(a==n+j,b==n+j) for a,b,op in sels[j+1:]]))
    for j in range(k-1):
        a,b,op=sels[j];aa,bb,opp=sels[j+1]
        independent=z3.And(aa!=n+j,bb!=n+j)
        ordered=z3.Or(z3.ULT(a,aa),z3.And(a==aa,z3.ULT(b,bb)),z3.And(a==aa,b==bb,z3.Or(z3.Not(op),opp)))
        s.add(z3.Implies(independent,ordered))
    autos=automorphisms(N,mask)
    def transformed(v,perm):
        out=v
        for i in range(n-1,-1,-1):out=z3.If(v==i,z3.BitVecVal(perm[i],selbits),out)
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
    s.add(ws[-1]==z3.BitVecVal(target,bits))
    goal=z3.Goal()
    goal.add(*s.assertions())
    started=time.monotonic()
    applied=z3.Then('simplify','solve-eqs','bit-blast','tseitin-cnf')(goal)
    assert len(applied)==1
    text=applied[0].dimacs()
    Path(destination).write_text(text)
    meta={'N':N,'mask':mask,'gates':k,'clean':clean,'test_assignments':tests,'automorphisms':len(autos),'cnf_path':destination,'cnf_sha256':hashlib.sha256(text.encode()).hexdigest(),'cnf_bytes':len(text.encode()),'elapsed_s':time.monotonic()-started,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'cnf_header':next(x for x in text.splitlines() if x.startswith('p '))}
    print(json.dumps(meta),flush=True)
    return s,sels,applied[0],full_xs,fulltarget,fullforbidden

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--N',type=int,required=True);p.add_argument('--mask',type=int,required=True);p.add_argument('--gates',type=int,required=True);p.add_argument('--clean',action='store_true');p.add_argument('--output',required=True);a=p.parse_args()
    emit(a.N,a.mask,a.gates,a.clean,90,a.output)
