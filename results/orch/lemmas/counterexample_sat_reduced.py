import argparse,json,itertools,time,sys,hashlib
from pathlib import Path
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-51/z3-python')
import z3

def truth(N,mask):
    n=2*N
    xs=[sum(1<<a for a in range(1<<n) if a>>i&1) for i in range(n)]
    target=0
    for p in range(N):
        for l in range(N):
            if mask>>(N*p+l)&1:target|=xs[p]&xs[N+l]
    forbidden=sum(1<<(1<<i) for i in range(n))
    forbidden|=sum(1<<((1<<p)|(1<<(N+l))) for p in range(N) for l in range(N) if not mask>>(N*p+l)&1)
    return xs,target,forbidden

def automorphisms(N,mask):
    perms=list(itertools.permutations(range(N)))
    def edge(p,l):return mask>>(N*p+l)&1
    out=[]
    for p in perms:
        for q in perms:
            if all(edge(i,j)==edge(p[i],q[j]) for i in range(N) for j in range(N)):
                out.append(tuple(p)+tuple(N+x for x in q))
            if all(edge(i,j)==edge(q[j],p[i]) for i in range(N) for j in range(N)):
                out.append(tuple(N+x for x in p)+tuple(q))
    return out

def solve(N,mask,k,clean,timeout):
    assert N >= 1 and 0 < mask < (1 << (N*N)) and k >= 1
    xs,target,forbidden=truth(N,mask);n=2*N;bits=1<<n;selbits=(n+k).bit_length()
    s=z3.SolverFor('QF_BV');s.set(timeout=int(timeout*1000));s.set(random_seed=3451)
    ws=[z3.BitVecVal(x,bits) for x in xs];sels=[];padding=[]
    def pick(v,values):
        r=values[-1]
        for i in range(len(values)-2,-1,-1):r=z3.If(v==i,values[i],r)
        return r
    for j in range(k):
        a=z3.BitVec('a'+str(j),selbits);b=z3.BitVec('b'+str(j),selbits);op=z3.Bool('and'+str(j));v=z3.BitVec('w'+str(j),bits)
        s.add(z3.ULT(b,n+j),z3.ULE(a,b))
        va=pick(a,ws);vb=pick(b,ws)
        s.add(v==z3.If(op,va&vb,va|vb))
        pad=z3.Bool('padding'+str(j));padding.append(pad)
        if j==0:s.add(z3.Not(pad))
        else:
            s.add(z3.Implies(padding[j-1],pad))
            s.add(z3.Implies(pad,z3.And(z3.Not(op),a==n+j-1,b==n+j-1)))
        s.add(z3.Implies(z3.Not(pad),z3.And(*[v!=w for w in ws])))
        if clean:s.add(z3.Implies(op,v&z3.BitVecVal(forbidden,bits)==0))
        ws.append(v);sels.append((a,b,op))
    for i in range(n):
        if any(((target>>a)^(target>>(a^(1<<i))))&1 for a in range(bits)):
            s.add(z3.Or(*[z3.Or(a==i,b==i) for a,b,op in sels]))
    for j in range(k-1):
        s.add(z3.Or(*[z3.Or(a==n+j,b==n+j) for a,b,op in sels[j+1:]]))
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
    start=time.monotonic();ans=s.check();elapsed=time.monotonic()-start
    stats=s.statistics()
    statistics={key:stats.get_key_value(key) for key in stats.keys()}
    rec={'solver':z3.get_version_string(),'statistics':statistics,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'N':N,'mask':mask,'gates':k,'clean':clean,'timeout_s':timeout,'status':str(ans),'elapsed_s':elapsed,'automorphisms':len(autos),'encoding':'binary AND/OR, functional duplicate elimination + OR-copy suffix, full table, input-automorphism lex leaders'}
    if ans==z3.unknown:rec['reason']=s.reason_unknown()
    if ans==z3.sat:
        m=s.model();values=xs[:];gs=[]
        for a,b,op in sels:
            aa=m.eval(a).as_long();bb=m.eval(b).as_long();oo=z3.is_true(m.eval(op))
            assert aa<=bb<len(values)
            v=values[aa]&values[bb] if oo else values[aa]|values[bb]
            if clean and oo:assert not v&forbidden
            values.append(v);gs.append(['and' if oo else 'or',aa,bb])
        assert values[-1]==target
        rec['verified_circuit']=gs
    return rec

def canonical(N,mask):
    rows=[(mask>>(N*p))&((1<<N)-1) for p in range(N)]
    best=1<<(N*N)
    for perm in itertools.permutations(range(N)):
        rr=[sum((r>>i&1)<<perm[i] for i in range(N)) for r in rows]
        rr.sort();e=sum(r<<(N*i) for i,r in enumerate(rr));best=min(best,e)
    return best

def classes(N):
    out={}
    for e in range(1,1<<(N*N)):
        rows=[(e>>(N*p))&((1<<N)-1) for p in range(N)]
        if any((a&b).bit_count()>1 for a,b in itertools.combinations(rows,2)):continue
        if any(r==0 for r in rows):continue
        if any(not any(r>>l&1 for r in rows) for l in range(N)):continue
        transpose=sum(((e>>(N*p+l))&1)<<(N*l+p) for p in range(N) for l in range(N))
        c=min(canonical(N,e),canonical(N,transpose))
        if c in out:continue
        edges=[(p,N+l) for p in range(N) for l in range(N) if c>>(N*p+l)&1]
        tau=min(t.bit_count() for t in range(1<<(2*N)) if all(t>>u&1 or t>>v&1 for u,v in edges))
        out[c]={'N':N,'mask':c,'edges':len(edges),'cover_number':tau,'clean_upper':len(edges)+tau-1}
    return sorted(out.values(),key=lambda r:(-r['clean_upper'],-r['edges'],r['mask']))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--N',type=int,default=4);ap.add_argument('--mask',type=int);ap.add_argument('--gates',type=int);ap.add_argument('--clean',action='store_true');ap.add_argument('--timeout',type=float,default=60);ap.add_argument('--classes',action='store_true');args=ap.parse_args()
    if args.classes:print(json.dumps(classes(args.N)))
    else:print(json.dumps(solve(args.N,args.mask,args.gates,args.clean,args.timeout)),flush=True)
