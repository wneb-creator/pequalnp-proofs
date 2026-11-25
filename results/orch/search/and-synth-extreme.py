import sys,json,time
from datetime import datetime, timezone
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
p=int(sys.argv[1]);q=p;n=p+q;k=p-1
limit=int(sys.argv[2]) if len(sys.argv)>2 else 120000
t0=len(sys.argv)>3 and sys.argv[3]=='t0'
fullwidth=1<<n
edges=[(a,a) for a in range(p)]+[(a,(a+1)%q) for a in range(p)]
uv=[(a,p+b) for a,b in edges]
neighbors=[sum(1<<w for a,b in uv for w in ([b] if a==v else [a] if b==v else [])) for v in range(n)]
def edgefun(x):return any(x>>a&1 and x>>b&1 for a,b in uv)
mins=[(1<<a)|(1<<b) for a,b in uv]
maxzeros=[x for x in range(fullwidth) if not edgefun(x) and all(x>>v&1 or x&neighbors[v] for v in range(n))]
patterns=sorted(set(mins+maxzeros));width=len(patterns)
inputs=[sum(1<<j for j,x in enumerate(patterns) if x>>i&1) for i in range(n)]
target=0
for a,b in edges:target |= inputs[a]&inputs[p+b]
s=z3.Solver();s.set(timeout=limit)
signals=[z3.BitVecVal(x,width) for x in inputs]
selectors=[]
zero=z3.BitVecVal(0,width)
for i in range(k):
    sides=[];smasks=[];selections=[]
    for side in range(2):
        bs=[z3.Bool(f's_{i}_{side}_{j}') for j in range(n+i)]
        v=zero
        mask=z3.BitVecVal(0,n+i)
        for j,b in enumerate(bs):
            v=v|z3.If(b,signals[j],zero)
            mask=mask|z3.If(b,z3.BitVecVal(1<<j,n+i),z3.BitVecVal(0,n+i))
        s.add(z3.Or(bs))
        if t0:s.add(z3.Not(z3.And(z3.Or(bs[:p]),z3.Or(bs[p:n]))))
        sides.append(v);smasks.append(mask);selections.append(bs)
    s.add(z3.ULE(smasks[0],smasks[1]))
    gi=z3.BitVec(f'g_{i}',width)
    s.add(gi==sides[0]&sides[1])
    signals.append(gi);selectors.append(selections)
outs=[z3.Bool(f'out_{i}') for i in range(k)]
out=zero
for i,b in enumerate(outs):out=out|z3.If(b,signals[n+i],zero)
s.add(out==z3.BitVecVal(target,width))
if len(sys.argv)>4 and sys.argv[4]=='dump':
    from pathlib import Path
    dst=Path(f'/tmp/oec/pequalnp-pilot-152/and-synth-c{2*p}-extreme-t0{t0}.smt2')
    dst.write_text(s.to_smt2())
    print(dst)
    raise SystemExit(0)
print(datetime.now(timezone.utc).isoformat(),'cycle',2*p,'AND budget',k,'truth bits',width,flush=True)
start=time.monotonic();res=s.check()
print('RESULT',res,'seconds',round(time.monotonic()-start,3),flush=True)
if res==z3.sat:
    m=s.model();concrete=inputs[:];description=[]
    for i,ss in enumerate(selectors):
        sets=[[j for j,b in enumerate(side) if z3.is_true(m.eval(b,model_completion=True))] for side in ss]
        lhs=rhs=0
        for j in sets[0]:lhs|=concrete[j]
        for j in sets[1]:rhs|=concrete[j]
        concrete.append(lhs&rhs);description.append(sets)
    outids=[i for i,b in enumerate(outs) if z3.is_true(m.eval(b,model_completion=True))]
    actual=0
    for i in outids:actual|=concrete[n+i]
    assert actual==target
    fullinputs=[sum(1<<x for x in range(fullwidth) if x>>i&1) for i in range(n)]
    full=fullinputs[:]
    for aa,bb in description:
        va=vb=0
        for j in aa:va|=full[j]
        for j in bb:vb|=full[j]
        full.append(va&vb)
    actualfull=0
    for i in outids:actualfull|=full[n+i]
    expectedfull=sum(1<<x for x in range(fullwidth) if edgefun(x))
    assert actualfull==expectedfull
    print('VERIFIED_FULL_TRUTH_TABLE',json.dumps(dict(p=p,q=q,edges=edges,gates=description,outputs=outids,t0=t0)),flush=True)
else:
    if res==z3.unknown:print('REASON',s.reason_unknown(),flush=True)
print(s.statistics(),flush=True)
