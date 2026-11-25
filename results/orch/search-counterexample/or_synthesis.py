import argparse
import json
from pathlib import Path
import time
import z3

ap=argparse.ArgumentParser()
ap.add_argument('scenario')
ap.add_argument('or_count',type=int)
ap.add_argument('--seconds',type=int,default=120)
args=ap.parse_args()
N=13; U=(1<<N)-1
lines=[sum(1<<((l+d)%N) for d in (0,1,3,9)) for l in range(N)]
pencils=[sum(1<<l for l in range(N) if lines[l]>>p&1) for p in range(N)]
negative=[]
for p in range(1<<N):
    q=sum(1<<l for l in range(N) if lines[l]&p==0)
    closure=U
    for l in range(N):
        if q>>l&1: closure&=U^lines[l]
    if closure==p and not any(p&~l==0 for l in lines) and not any(q&~t==0 for t in pencils):
        negative.append(p|(q<<13))
if args.scenario=='theta':
    ell=0; point=2
    ps=[p for p in range(N) if lines[ell]>>p&1][:3]
    ls=[next(l for l in range(N) if (lines[l]>>point&1) and (lines[l]>>p&1)) for p in ps]
    vertices=[point]+ps+[13+ell]+[13+l for l in ls]
elif args.scenario=='quadrangle':
    ps=[0,1,2,5]
    assert all(sum(lines[l]>>p&1 for p in ps)<=2 for l in range(N))
    ls=sorted({l for l in range(N) if sum(lines[l]>>p&1 for p in ps)==2})
    vertices=ps+[13+l for l in ls]
elif args.scenario=='full':
    vertices=list(range(26))
else:
    vertices=[int(x) for x in args.scenario.split(',')]
def proj(v): return sum(((v>>x)&1)<<i for i,x in enumerate(vertices))
positives=[]
for p in range(N):
    for l in range(N):
        if lines[l]>>p&1 and p in vertices and 13+l in vertices:
            positives.append(proj((1<<p)|(1<<(13+l))))
neg=set(map(proj,negative))
neg=sorted(v for v in neg if not any(v!=w and v&~w==0 for w in neg))
samples=positives+neg
m=len(samples); nv=len(vertices); k=args.or_count
positive_mask=(1<<len(positives))-1
all_mask=(1<<m)-1
print(json.dumps({'scenario':args.scenario,'vertices':vertices,'positives':len(positives),'negative_maxima':len(neg),'or_count':k}),flush=True)
start=time.monotonic()
s=z3.SolverFor('QF_BV');s.set(timeout=args.seconds*1000)
full=z3.BitVecVal(all_mask,m)
pm=z3.BitVecVal(positive_mask,m)
wires=[z3.BitVecVal(sum(((v>>i)&1)<<j for j,v in enumerate(samples)),m) for i in range(nv)]
selectors=[]
for i in range(k):
    terms=[]; sels=[]
    for b in range(2):
        selected=[z3.Bool(f's_{i}_{b}_{j}') for j in range(nv+i)]
        term=full
        for sel,wire in zip(selected,wires):
            term=term&z3.If(sel,wire,full)
        termvar=z3.BitVec(f't_{i}_{b}',m)
        s.add(termvar==term)
        sels.append(selected);terms.append(termvar)
    # An OR with a branch redundant on all required positives can be removed.
    s.add((terms[0]&~terms[1]&pm)!=0)
    s.add((terms[1]&~terms[0]&pm)!=0)
    s.add(z3.ULT(terms[0]&pm,terms[1]&pm))
    gate=z3.BitVec(f'g_{i}',m)
    s.add(gate==terms[0]|terms[1])
    wires.append(gate);selectors.append(sels)
outsel=[z3.Bool(f'o_{i}') for i in range(k)]
out=full
for sel,wire in zip(outsel,wires[nv:]):out=out&z3.If(sel,wire,full)
s.add(out==pm)
print('encoded',round(time.monotonic()-start,3),flush=True)
ans=s.check()
print('result',ans,'elapsed',round(time.monotonic()-start,3),flush=True)
print(s.statistics(),flush=True)
if ans==z3.sat:
    model=s.model()
    chosen=lambda xs:[j for j,x in enumerate(xs) if z3.is_true(model.eval(x,model_completion=True))]
    result={'vertices':vertices,'ors':[[chosen(b) for b in g] for g in selectors],'output':chosen(outsel)}
    path=Path('/tmp/oec/pequalnp-pilot-62')/f'or-witness-{args.scenario}-{k}.json'
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)
