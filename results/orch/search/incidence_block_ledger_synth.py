import itertools
import json
import subprocess
import sys
import time
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-131')
SOLVER = BASE / 'elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
lines = tuple(map(int, sys.argv[1].split(',')))
size = int(sys.argv[2])
seconds = int(sys.argv[3]) if len(sys.argv)>3 else 600
sanity = len(sys.argv)>4 and sys.argv[4]=='sanity'
D = {0,1,3,9}
points = tuple(p for p in range(13) if any((p-l)%13 in D for l in lines))
P,L = len(points),len(lines)
arity = P+L
edges = [(i,P+j) for i,p in enumerate(points) for j,l in enumerate(lines) if (p-l)%13 in D]
supports = [tuple(j for j,l in enumerate(lines) if (p-l)%13 in D) for p in points]
groups = {s:tuple(i for i,t in enumerate(supports) if t==s) for s in set(supports)}
autos=[]
for lp in itertools.permutations(range(L)):
    transformed={s:tuple(sorted(lp[j] for j in s)) for s in groups}
    if not all(t in groups and len(groups[s])==len(groups[t]) for s,t in transformed.items()):continue
    keys=list(groups)
    for choices in itertools.product(*(list(itertools.permutations(groups[transformed[s]])) for s in keys)):
        perm=[0]*arity
        for s,targets in zip(keys,choices):
            for old,new in zip(groups[s],targets):perm[old]=new
        for j in range(L):perm[P+j]=P+lp[j]
        assert {tuple(sorted((perm[a],perm[b]))) for a,b in edges}=={tuple(sorted(e)) for e in edges}
        autos.append(tuple(perm))
reps={min(tuple(sorted((g[i],g[j]))) for g in autos) for i in range(arity) for j in range(i+1,arity)}
true_rows=[(1<<a)|(1<<b) for a,b in edges]
false_rows=[]
for ys in range(1<<L):
    xs=sum(1<<i for i,s in enumerate(supports) if not any((ys>>j)&1 for j in s))
    closure=sum(1<<j for j in range(L) if not any((xs>>i)&1 and j in supports[i] for i in range(P)))
    if closure==ys:false_rows.append(xs|(ys<<P))
samples=sorted(set(true_rows+false_rows))
name='incidence-block-'+('-'.join(map(str,lines)))+'-s'+str(size)+'-ledger'
if sanity:name+='-sanity'
data={'lines':lines,'points':points,'arity':arity,'edges':edges,'minimal_true':true_rows,'maximal_false':false_rows,'automorphisms':len(autos),'first_pair_representatives':sorted(reps)}
(BASE/(name+'-data.json')).write_text(json.dumps(data,indent=2))
print(json.dumps(data),flush=True)
if len(sys.argv)>4 and sys.argv[4]=='data':raise SystemExit(0)
clauses=[]
nv=0
def var():
    global nv
    nv+=1
    return nv
def clause(*xs):clauses.append(xs)
def one(vs):
    clause(*vs)
    for a,b in itertools.combinations(vs,2):clause(-a,-b)
def atmost(vs,k):
    if k>=len(vs):return
    if k<0:clause();return
    if k==0:
        for v in vs:clause(-v)
        return
    prev=[]
    for i,x in enumerate(vs):
        curr=[var() for j in range(k)]
        clause(-x,curr[0])
        if prev:
            for j in range(k):clause(-prev[j],curr[j])
            for j in range(1,k):clause(-x,-prev[j-1],curr[j])
            clause(-x,-prev[k-1])
        prev=curr
ops=[];selectors=[]
for j in range(size):
    ops.append(var())
    a=[var() for k in range(arity+j)]
    b=[var() for k in range(arity+j)]
    one(a);one(b);selectors.append((a,b))
    for u in range(arity+j):
        for v in range(u):clause(-a[u],-b[v])
for i in range(arity):
    for j in range(i,arity):
        if (i,j) not in reps:clause(-selectors[0][0][i],-selectors[0][1][j])
for j in range(size-1):
    clause(*(selectors[k][side][arity+j] for k in range(j+1,size) for side in range(2)))
atmost([-o for o in ops],L)
atmost(ops,size-L)
if sanity:
    known=[];stars=[]
    def gate(op,a,b):
        known.append((op,min(a,b),max(a,b)))
        return arity+len(known)-1
    for j in range(L):
        xs=[i for i,s in enumerate(supports) if j in s]
        w=xs[0]
        for x in xs[1:]:w=gate('or',w,x)
        stars.append(gate('and',w,P+j))
    w=stars[0]
    for x in stars[1:]:w=gate('or',w,x)
    assert len(known)==size
    for j,(op,a,b) in enumerate(known):
        clause(ops[j] if op=='or' else -ops[j])
        clause(selectors[j][0][a]);clause(selectors[j][1][b])
def aim(x):return any((x>>a)&1 and (x>>b)&1 for a,b in edges)
dirty=[]
for x in samples:
    values=[]
    for j in range(size):
        a,b,v=var(),var(),var();values.append(v)
        for side,sv in enumerate((a,b)):
            for k,s in enumerate(selectors[j][side]):
                if k<arity:clause(-s,sv if (x>>k)&1 else -sv)
                else:
                    source=values[k-arity]
                    clause(-s,-sv,source);clause(-s,sv,-source)
        o=ops[j]
        clause(o,-a,-b,v);clause(o,a,-v);clause(o,b,-v)
        clause(-o,a,b,-v);clause(-o,-a,v);clause(-o,-b,v)
        if not aim(x):
            e=var();dirty.append(e)
            clause(-e,-o);clause(-e,v);clause(o,-v,e)
    clause(values[-1] if aim(x) else -values[-1])
atmost(dirty,(1<<L)-len(false_rows))
cnf=BASE/(name+'.cnf')
with cnf.open('w') as f:
    f.write(f'p cnf {nv} {len(clauses)}\n')
    for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
print('rows',len(samples),'vars',nv,'clauses',len(clauses),flush=True)
start=time.monotonic()
out=BASE/(name+'.solver.stdout');err=BASE/(name+'.solver.stderr')
with out.open('w') as fo,err.open('w') as fe:
    cp=subprocess.run([str(SOLVER),'-t',str(seconds),'--seed=2583',str(cnf)],stdout=fo,stderr=fe)
print('solver_exit',cp.returncode,'elapsed_s',time.monotonic()-start,flush=True)
if cp.returncode==10:
    trues=set()
    for line in out.read_text().splitlines():
        if line.startswith('v '):trues.update(int(t) for t in line[2:].split() if int(t)>0)
    gs=[('or' if o in trues else 'and',*(next(i for i,s in enumerate(ss) if s in trues) for ss in ab)) for o,ab in zip(ops,selectors)]
    def ev(x):
        v=[bool((x>>i)&1) for i in range(arity)]
        for o,a,b in gs:v.append(v[a] or v[b] if o=='or' else v[a] and v[b])
        return v[-1]
    bad=[x for x in range(1<<arity) if ev(x)!=aim(x)]
    print('gates',gs,'full_table_errors',len(bad),flush=True)
    (BASE/(name+'-candidate.json')).write_text(json.dumps({'gates':gs,'errors':bad,'data':data},indent=2))
