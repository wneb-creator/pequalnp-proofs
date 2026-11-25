import sys,json,time,math
from datetime import datetime, timezone
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
from pathlib import Path
spec=json.loads(Path(sys.argv[1]).read_text())
p=spec['p'];q=spec['q'];n=p+q;m=int(sys.argv[2]);limit=int(sys.argv[3]);label=spec['label']
edges=[tuple(e) for e in spec['edges']]
uv=[(a,p+b) for a,b in edges]
allmask=(1<<n)-1
neighbors=[sum(1<<w for a,b in uv for w in ([b] if a==v else [a] if b==v else [])) for v in range(n)]
def target(x):return any(x>>a&1 and x>>b&1 for a,b in uv)
mins=[(1<<a)|(1<<b) for a,b in uv]
maxzeros=[x for x in range(1<<n) if not target(x) and all(x>>v&1 or x&neighbors[v] for v in range(n))]
starrows=[]
for v,N in enumerate(neighbors):
 for Q in range(1<<n):
  if Q&N==Q and Q.bit_count()>=2:starrows.append((v,Q))
patterns=sorted(set(mins+maxzeros+[1<<i for i in range(n)]+[allmask^Q for v,Q in starrows]))
indexes={x:i for i,x in enumerate(patterns)}
width=len(patterns);idxwidth=(n+m).bit_length()
inputs=[sum(1<<j for j,x in enumerate(patterns) if x>>i&1) for i in range(n)]
mask=sum(1<<indexes[x] for x in mins+maxzeros)
expected=sum(1<<indexes[x] for x in mins)
s=z3.SolverFor('QF_BV');s.set(timeout=limit)
signals=[z3.BitVecVal(x,width) for x in inputs]
lreach=[z3.BoolVal(i<p) for i in range(n)];rreach=[z3.BoolVal(i>=p) for i in range(n)]
gates=[]
def select(index,values):
    result=values[-1]
    for j in range(len(values)-2,-1,-1):result=z3.If(index==j,values[j],result)
    return result
for i in range(m):
    a=z3.BitVec(f'a{i}',idxwidth);b=z3.BitVec(f'b{i}',idxwidth);op=z3.Bool(f'or{i}')
    s.add(z3.ULT(a,n+i),z3.ULT(b,n+i),z3.ULE(a,b))
    va=select(a,signals);vb=select(b,signals)
    g=z3.BitVec(f'g{i}',width)
    s.add(g==z3.If(op,va|vb,va&vb))
    l=z3.Bool(f'l{i}');r=z3.Bool(f'r{i}')
    s.add(l==z3.And(op,z3.Or(select(a,lreach),select(b,lreach))))
    s.add(r==z3.And(op,z3.Or(select(a,rreach),select(b,rreach))))
    s.add(z3.Not(z3.And(l,r)))
    signals.append(g);lreach.append(l);rreach.append(r);gates.append((op,a,b,g))
for i in range(1,m):
    op,a,b,g=gates[i];op0,a0,b0,g0=gates[i-1]
    key=z3.Concat(z3.If(op,z3.BitVecVal(0,1),z3.BitVecVal(1,1)),a,b)
    key0=z3.Concat(z3.If(op0,z3.BitVecVal(0,1),z3.BitVecVal(1,1)),a0,b0)
    s.add(z3.Or(a==n+i-1,b==n+i-1,z3.ULE(key0,key)))
out=z3.BitVec('out',idxwidth);s.add(z3.ULT(out,n+m))
s.add(select(out,signals)&z3.BitVecVal(mask,width)==z3.BitVecVal(expected,width))
stars=[]
for v,Q in starrows:
    leaves=[i for i in range(n) if Q>>i&1]
    hits=[]
    for op,a,b,g in gates:
        hits.append(z3.And(op,*[z3.Extract(indexes[1<<i],indexes[1<<i],g)==1 for i in leaves],z3.Extract(indexes[allmask^Q],indexes[allmask^Q],g)==0))
    stars.append(z3.Or(hits))
for a,b in uv:s.add(z3.Or([stars[r] for r,(v,Q) in enumerate(starrows) if (v==a and Q>>b&1) or (v==b and Q>>a&1)]))
# Distinct degree-two stars have distinct Boolean functions; a cover needs at least p such OR gates.
tau=min(S.bit_count() for S in range(1<<n) if all((S>>a&1) or (S>>b&1) for a,b in uv))

if len(sys.argv)>4 and sys.argv[4]=='dump':
    from pathlib import Path
    dst=Path(f'/tmp/oec/pequalnp-pilot-152/posted-synth-{label}-size{m}.smt2')
    dst.write_text(s.to_smt2())
    print(dst)
    raise SystemExit(0)
print(datetime.now(timezone.utc).isoformat(),'GRAPH',label,'size',m,'patterns',width,'edges',len(mins),'maxzeros',len(maxzeros),flush=True)
print('T0 and all posted star witnesses encoded; no assumptions on intermediate gate purity.',flush=True)
start=time.monotonic();res=s.check()
print('RESULT',res,'seconds',round(time.monotonic()-start,3),flush=True)
if res==z3.sat:
    mo=s.model();cs=[]
    for op,a,b,g in gates:cs.append([bool(z3.is_true(mo.eval(op))),mo.eval(a).as_long(),mo.eval(b).as_long()])
    oi=mo.eval(out).as_long()
    fullw=1<<n
    fullinputs=[sum(1<<x for x in range(fullw) if x>>i&1) for i in range(n)]
    full=fullinputs[:];reaches=[1<<i for i in range(n)]
    for op,a,b in cs:
        full.append((full[a]|full[b]) if op else (full[a]&full[b]))
        reaches.append((reaches[a]|reaches[b]) if op else 0)
        assert not (op and reaches[-1]&((1<<p)-1) and reaches[-1]&(((1<<q)-1)<<p))
    expectedfull=sum(1<<x for x in range(fullw) if target(x))
    assert full[oi]==expectedfull
    starids=[]
    for v,Q in starrows:
        f=0
        for i in range(n):
            if Q>>i&1:f|=fullinputs[i]
        starids.append([j for j,(op,a,b) in enumerate(cs) if op and full[n+j]==f])
    assert all(any(starids[r] for r,(v,Q) in enumerate(starrows) if (v==a and Q>>b&1) or (v==b and Q>>a&1)) for a,b in uv)
    data=dict(p=p,q=q,edges=edges,gates=cs,output=oi,star_witnesses=starids,starrows=starrows,tau=tau)
    print('VERIFIED_FULL_TRUTH_TABLE',json.dumps(data),flush=True)
    from pathlib import Path
    Path(f'/tmp/oec/pequalnp-pilot-152/posted-synth-{label}-size{m}-model.json').write_text(json.dumps(data,indent=2))
else:
    if res==z3.unknown:print('REASON',s.reason_unknown(),flush=True)
print(s.statistics(),flush=True)
