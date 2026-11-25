import sys,json,time,subprocess,hashlib
from pathlib import Path

graph=Path(sys.argv[1]);K=int(sys.argv[2]);seconds=int(sys.argv[3]);prefix=Path(sys.argv[4])
solver=Path(sys.argv[5]);ordered='ordered' in sys.argv[6:];or_only='or_only' in sys.argv[6:]
data=list(map(int,graph.read_text().split()));n,m=data[:2];edges=list(zip(data[2::2],data[3::2]))
ind=[s for s in range(1<<n) if not any((s>>a&1) and (s>>b&1) for a,b in edges)]
maxi=[s for s in ind if not any((s|1<<i) in ind for i in range(n) if not(s>>i&1))]
rows=[(1<<a)|(1<<b) for a,b in edges]+maxi;R=len(rows);target=[1]*m+[0]*len(maxi)
variables=[]
def var(name):
    variables.append(name)
    return len(variables)
ops=[var(('op',j)) for j in range(K)]
vals=[[var(('val',j,t)) for t in range(R)] for j in range(K)]
av=[[var(('aval',j,t)) for t in range(R)] for j in range(K)]
bv=[[var(('bval',j,t)) for t in range(R)] for j in range(K)]
asel=[[var(('asel',j,i)) for i in range(n+j)] for j in range(K)]
bsel=[[var(('bsel',j,i)) for i in range(n+j)] for j in range(K)]
clauses=[]
def clause(*lits):clauses.append(list(lits))
def onehot(vs):
    clause(*vs)
    for a in range(len(vs)):
        for b in range(a):clause(-vs[a],-vs[b])
for j in range(K):
    onehot(asel[j]);onehot(bsel[j])
    for a in range(n+j):
        for b in range(a+1):clause(-asel[j][a],-bsel[j][b])
    for selected,signals in [(asel[j],av[j]),(bsel[j],bv[j])]:
        for i,s in enumerate(selected):
            for t,point in enumerate(rows):
                v=signals[t]
                if i<n:clause(-s,v if point>>i&1 else -v)
                else:
                    other=vals[i-n][t]
                    clause(-s,-v,other);clause(-s,v,-other)
    for t in range(R):
        z,a,b,o=vals[j][t],av[j][t],bv[j][t],ops[j]
        clause(o,-z,a);clause(o,-z,b);clause(o,z,-a,-b)
        clause(-o,z,-a);clause(-o,z,-b);clause(-o,-z,a,b)
for t,want in enumerate(target):clause(vals[-1][t] if want else -vals[-1][t])
for i in range(n):clause(*[s[i] for side in [asel,bsel] for s in side])
if ordered:
    for j in range(K-1):
        for b in range(n+j):
            for c in range(b):clause(-bsel[j][b],-bsel[j+1][c])
for j in range(K-1):
    clause(*[s[n+j] for side in [asel,bsel] for s in side[j+1:]])
choices=[]
for j in range(K-2):
    uses=[s[n+j] for side in [asel,bsel] for s in side[j+1:]]
    q=var(('fanout',j));choices.append(q)
    if or_only:clause(-q,ops[j])
    for i in range(len(uses)):clause(-q,*uses[:i],*uses[i+1:])
clause(*choices)
cnf=prefix.with_suffix('.cnf')
cnf.write_text('p cnf '+str(len(variables))+' '+str(len(clauses))+'\n'+'\n'.join(' '.join(map(str,c))+' 0' for c in clauses)+'\n')
meta={'graph':graph.name,'n':n,'edges':edges,'K':K,'rows':rows,'variables':variables,'ops':ops,'asel':asel,'bsel':bsel,'ordered':ordered,'fanout_goal':'or' if or_only else 'any','clauses':len(clauses),'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest()}
prefix.with_suffix('.json').write_text(json.dumps(meta,indent=2)+'\n')
print('MODEL',json.dumps({k:v for k,v in meta.items() if k not in ['variables','ops','asel','bsel']}),flush=True)
started=time.monotonic();solverlog=prefix.with_suffix('.solver.log')
with solverlog.open('w') as f:
    result=subprocess.run([str(solver),'-t',str(seconds),str(cnf)],stdout=f,stderr=subprocess.STDOUT,timeout=seconds+30)
print('RESULT',result.returncode,'SECONDS',time.monotonic()-started,flush=True)
lines=solverlog.read_text().splitlines();status=[s for s in lines if s.startswith('s ')]
print('STATUS',status,flush=True)
if result.returncode==10:
    literals=[int(x) for line in lines if line.startswith('v ') for x in line[2:].split() if x!='0']
    truth={abs(x):x>0 for x in literals}
    gates=[]
    for j in range(K):
        aa=[i for i,s in enumerate(asel[j]) if truth[s]];bb=[i for i,s in enumerate(bsel[j]) if truth[s]]
        assert len(aa)==len(bb)==1
        gates.append((int(truth[ops[j]]),aa[0],bb[0]))
        print(j,'or' if truth[ops[j]] else 'and',aa[0],bb[0],flush=True)
    failed=[]
    for point in range(1<<n):
        v=[point>>i&1 for i in range(n)]
        for op,a,b in gates:v.append((v[a]|v[b]) if op else (v[a]&v[b]))
        want=int(any((point>>a&1) and (point>>b&1) for a,b in edges))
        if v[-1]!=want:failed.append(point)
    print('FULL_TRUTH_FAILED',failed,flush=True)
    prefix.with_suffix('.witness.json').write_text(json.dumps({'n':n,'edges':edges,'gates':gates,'failed':failed},indent=2)+'\n')
