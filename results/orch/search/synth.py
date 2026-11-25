import argparse
import json
import random
import time
from pathlib import Path
import z3

p = argparse.ArgumentParser()
p.add_argument('--gates', type=int, default=19)
p.add_argument('--nots', type=int, default=1)
p.add_argument('--seed', type=int, default=1)
p.add_argument('--seconds', type=int, default=600)
p.add_argument('--out', required=True)
p.add_argument('--first', choices=['any','and-edge','or-edge','and-nonedge','or-nonedge','not'],default='any')
p.add_argument('--fixed')
p.add_argument('--near')
p.add_argument('--distance',type=int,default=4)
args = p.parse_args()
random.seed(args.seed)
edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
target = [any((x >> a & 1) and (x >> b & 1) for a,b in edges) for x in range(1024)]
indep = [x for x in range(1024) if not target[x]]
maxind = [x for x in indep if not any(x != y and (x & y) == x for y in indep)]
samples = set(maxind + [(1 << a) | (1 << b) for a,b in edges] + [0, 1023])
n=args.gates
s=z3.Solver()
s.set(timeout=1000*args.seconds, random_seed=args.seed)
A=[[z3.Bool(f'a_{i}_{j}') for j in range(10+i)] for i in range(n)]
B=[[z3.Bool(f'b_{i}_{j}') for j in range(10+i)] for i in range(n)]
N=[z3.Bool(f'n_{i}') for i in range(n)]
O=[z3.Bool(f'o_{i}') for i in range(n)]
s.add(z3.PbEq([(v,1) for v in N],args.nots))
for i in range(n):
    s.add(z3.PbEq([(v,1) for v in A[i]],1))
    s.add(z3.PbEq([(v,1) for v in B[i]],1))
    s.add(z3.Implies(N[i],z3.And(z3.Not(O[i]), B[i][0])))
    for j in range(10+i):
        s.add(z3.Implies(z3.And(z3.Not(N[i]),A[i][j]),z3.Or(B[i][j+1:])))
for i in range(n-1):
    s.add(z3.Or([A[j][10+i] for j in range(i+1,n)]+[z3.And(z3.Not(N[j]),B[j][10+i]) for j in range(i+1,n)]))
for i in range(10):
    s.add(z3.Or([A[j][i] for j in range(n)]+[z3.And(z3.Not(N[j]),B[j][i]) for j in range(n)]))
if args.nots==1:
    s.add(z3.Not(N[-1]))
if args.first!='any':
    s.add(A[0][0])
    if args.first=='not':
        s.add(N[0])
    else:
        s.add(z3.Not(N[0]),O[0] == args.first.startswith('or'))
        s.add(B[0][1 if args.first.endswith('-edge') else 2])
else:
    s.add(A[0][0],z3.Or(N[0],B[0][1],B[0][2]))
if args.fixed:
    fixed=json.loads(Path(args.fixed).read_text())['gates']
    assert len(fixed)==n
    for i,(op,a,b) in enumerate(fixed):
        s.add(N[i] == (op=='not'),O[i] == (op=='or'),A[i][a],B[i][b])
if args.near:
    fixed=json.loads(Path(args.near).read_text())['gates']
    assert len(fixed)==n
    changed=[]
    for i,(op,a,b) in enumerate(fixed):
        changed.append(z3.Not(z3.And(N[i] == (op=='not'),O[i] == (op=='or'),A[i][a],B[i][b if op!='not' else 0])))
    s.add(z3.PbLe([(v,1) for v in changed],args.distance))

def add_sample(x):
    values=[z3.BoolVal(bool(x>>j&1)) for j in range(10)]
    for i in range(n):
        av=z3.Bool(f'av_{x}_{i}')
        bv=z3.Bool(f'bv_{x}_{i}')
        v=z3.Bool(f'v_{x}_{i}')
        for j in range(10+i):
            s.add(z3.Implies(A[i][j],av == values[j]))
            s.add(z3.Implies(B[i][j],bv == values[j]))
        s.add(v == z3.If(N[i],z3.Not(av),z3.If(O[i],z3.Or(av,bv),z3.And(av,bv))))
        values.append(v)
    s.add(values[-1] == target[x])

for x in sorted(samples): add_sample(x)

def evaluate(c,x):
    w=[bool(x>>j&1) for j in range(10)]
    for op,a,b in c:
        w.append(not w[a] if op=='not' else (w[a] or w[b]) if op=='or' else (w[a] and w[b]))
    return w[-1]

started=time.monotonic()
print(json.dumps({'event':'start','args':vars(args),'samples':len(samples)}),flush=True)
for iteration in range(200):
    t=time.monotonic()
    result=s.check()
    print(json.dumps({'event':'solve','iteration':iteration,'result':str(result),'seconds':time.monotonic()-t,'samples':len(samples),'total':time.monotonic()-started}),flush=True)
    if result != z3.sat:
        print(s.statistics(),flush=True)
        break
    m=s.model()
    c=[]
    for i in range(n):
        a=next(j for j,v in enumerate(A[i]) if z3.is_true(m.eval(v)))
        b=next(j for j,v in enumerate(B[i]) if z3.is_true(m.eval(v)))
        op='not' if z3.is_true(m.eval(N[i])) else 'or' if z3.is_true(m.eval(O[i])) else 'and'
        c.append((op,a,b))
    bad=[x for x in range(1024) if evaluate(c,x) != target[x]]
    print(json.dumps({'event':'candidate','circuit':c,'bad':len(bad),'bad_examples':bad[:20]}),flush=True)
    if not bad:
        Path(args.out).write_text(json.dumps({'gates':c,'output':9+n,'inputs':10,'verified':1024},indent=2)+'\n')
        break
    random.shuffle(bad)
    new=bad[:min(30,len(bad))]
    for x in new:
        assert x not in samples
        add_sample(x)
        samples.add(x)
