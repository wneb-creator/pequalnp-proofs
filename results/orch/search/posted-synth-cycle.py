import sys,json,time,math
from datetime import datetime, timezone
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
p=int(sys.argv[1]);q=p;n=p+q;m=int(sys.argv[2]);limit=int(sys.argv[3])
edges=[(a,a) for a in range(p)]+[(a,(a+1)%q) for a in range(p)]
uv=[(a,p+b) for a,b in edges]
allmask=(1<<n)-1
neighbors=[sum(1<<w for a,b in uv for w in ([b] if a==v else [a] if b==v else [])) for v in range(n)]
def target(x):return any(x>>a&1 and x>>b&1 for a,b in uv)
mins=[(1<<a)|(1<<b) for a,b in uv]
maxzeros=[x for x in range(1<<n) if not target(x) and all(x>>v&1 or x&neighbors[v] for v in range(n))]
patterns=sorted(set(mins+maxzeros+[1<<i for i in range(n)]+[allmask^s for s in neighbors]))
indexes={x:i for i,x in enumerate(patterns)}
width=len(patterns);idxwidth=(n+m).bit_length()
inputs=[sum(1<<j for j,x in enumerate(patterns) if x>>i&1) for i in range(n)]
mask=sum(1<<indexes[x] for x in mins+maxzeros)
expected=sum(1<<indexes[x] for x in mins)
s=z3.Solver();s.set(timeout=limit)
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
out=z3.BitVec('out',idxwidth);s.add(z3.ULT(out,n+m))
s.add(select(out,signals)&z3.BitVecVal(mask,width)==z3.BitVecVal(expected,width))
stars=[]
for v,Q in enumerate(neighbors):
    leaves=[i for i in range(n) if Q>>i&1]
    assert len(leaves)==2
    hits=[]
    for op,a,b,g in gates:
        hits.append(z3.And(op,*[z3.Extract(indexes[1<<i],indexes[1<<i],g)==1 for i in leaves],z3.Extract(indexes[allmask^Q],indexes[allmask^Q],g)==0))
    stars.append(z3.Or(hits))
for a,b in uv:s.add(z3.Or(stars[a],stars[b]))
# Distinct degree-two stars have distinct Boolean functions; a cover needs at least p such OR gates.
s.add(z3.PbGe([(op,1) for op,a,b,g in gates],p))
if len(sys.argv)>4 and sys.argv[4]=='starsfirst':
    for v in range(p):
        op,a,b,g=gates[v]
        x=p+v;y=p+(v+1)%p
        s.add(op,a==min(x,y),b==max(x,y))
    s.add(out==n+m-1)
    for j in range(p,m-1):
        s.add(z3.Or([z3.Or(a==n+j,b==n+j) for op,a,b,g in gates[j+1:]]))
    print('RESTRICTED SEARCH: canonical left star OR prefix, all remaining gates used.',flush=True)
if len(sys.argv)>4 and sys.argv[4]=='canonical':
    canonical=[]
    for v in range(p):
        canonical.append((True,p+v,p+(v+1)%p))
        canonical.append((False,v,n+2*v))
    current=n+1
    for v in range(1,p):
        canonical.append((True,current,n+2*v+1))
        current=n+len(canonical)-1
    assert len(canonical)==m
    for (op,a,b,g),(v,x,y) in zip(gates,canonical):
        s.add(op==v,a==min(x,y),b==max(x,y))
    s.add(out==current)
if len(sys.argv)>4 and sys.argv[4]=='dump':
    from pathlib import Path
    dst=Path(f'/tmp/oec/pequalnp-pilot-152/posted-synth-c{2*p}-size{m}.smt2')
    dst.write_text(s.to_smt2())
    print(dst)
    raise SystemExit(0)
print(datetime.now(timezone.utc).isoformat(),'CYCLE',2*p,'size',m,'patterns',width,'edges',len(mins),'maxzeros',len(maxzeros),flush=True)
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
    for Q in neighbors:
        f=0
        for i in range(n):
            if Q>>i&1:f|=fullinputs[i]
        starids.append([j for j,(op,a,b) in enumerate(cs) if op and full[n+j]==f])
    assert all(starids[a] or starids[b] for a,b in uv)
    data=dict(p=p,q=q,edges=edges,gates=cs,output=oi,star_witnesses=starids)
    print('VERIFIED_FULL_TRUTH_TABLE',json.dumps(data),flush=True)
    from pathlib import Path
    Path(f'/tmp/oec/pequalnp-pilot-152/posted-synth-c{2*p}-size{m}-model.json').write_text(json.dumps(data,indent=2))
else:
    if res==z3.unknown:print('REASON',s.reason_unknown(),flush=True)
print(s.statistics(),flush=True)
