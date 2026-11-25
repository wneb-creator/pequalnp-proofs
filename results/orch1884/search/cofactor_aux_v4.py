import argparse, hashlib, itertools, json, subprocess, time
from datetime import datetime, timezone
from pathlib import Path

P = argparse.ArgumentParser()
P.add_argument('--gates', type=int, default=16)
P.add_argument('--seconds', type=int, default=120)
P.add_argument('--tag', default='cofactor-aux')
P.add_argument('--pin')
P.add_argument('--plain', action='store_true')
P.add_argument('--fresh', action='store_true')
P.add_argument('--productive', action='store_true')
P.add_argument('--sat-preset', action='store_true')
P.add_argument('--seed', type=int, default=0)
P.add_argument('--prefix-b', type=int)
P.add_argument('--pin-prefix')
P.add_argument('--primary-minimal', action='store_true')
P.add_argument('--relax-negative', type=int)
P.add_argument('--extra-negative', type=int)
args = P.parse_args()
root = Path('/tmp/oec/pequalnp-pilot-103/orch1884')
solver = Path('/tmp/oec/pequalnp-pilot-103/setup/lean-4.36.0-linux/bin/cadical')
E = [(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(3,8),(4,6),(6,8),(8,5),(5,7),(7,4)]
all_negative = [25,52,58,69,100,104,138,201,274,277,385,386]
negative = list(all_negative)
if args.relax_negative is not None:
    assert args.plain and args.relax_negative in all_negative
    negative.remove(args.relax_negative)
if args.extra_negative is not None:
    assert args.plain and args.extra_negative not in negative
    assert not any(args.extra_negative>>a&1 and args.extra_negative>>b&1 for a,b in E)
    negative.append(args.extra_negative)
positive = [(1 << a) | (1 << b) for a,b in E]
rows = sorted(positive + negative)
assert len(set(rows)) == len(rows)
bad_negative = [x for x in negative if x not in (100,386)]
n, N = 9, args.gates

def target(x):
    return any(x >> a & 1 and x >> b & 1 for a,b in E)

class CNF:
    def __init__(self): self.nv, self.cs = 0, []
    def var(self): self.nv += 1; return self.nv
    def clause(self,*xs): self.cs.append(tuple(xs))
    def one(self,xs):
        self.clause(*xs)
        for a,b in itertools.combinations(xs,2): self.clause(-a,-b)
    def write(self,p):
        with p.open('w') as f:
            f.write(f'p cnf {self.nv} {len(self.cs)}\n')
            for c in self.cs: f.write(' '.join(map(str,c))+' 0\n')

start = time.monotonic()
started = datetime.now(timezone.utc).isoformat()
c = CNF(); A=[]; B=[]; O=[]
for i in range(N):
    A.append([c.var() for _ in range(n+i)])
    B.append([c.var() for _ in range(n+i)])
    O.append(c.var())
    c.one(A[i]); c.one(B[i])
    for a in range(n+i):
        for b in range(a): c.clause(-A[i][a],-B[i][b])
for i in range(N-1):
    c.clause(*(v for j in range(i+1,N) for v in (A[j][n+i],B[j][n+i])))
for src in range(n):
    c.clause(*(v for j in range(N) for v in (A[j][src],B[j][src])))
if args.pin:
    pin=json.loads(Path(args.pin).read_text())
    if isinstance(pin,dict): pin=pin['gates']
    assert len(pin)==N
    for i,(op,a,b) in enumerate(pin):
        a,b=sorted((a,b))
        assert op in [0,1] and 0<=a<=b<n+i
        c.clause(O[i] if op else -O[i]); c.clause(A[i][a]); c.clause(B[i][b])
fixed_h_index=None
if args.prefix_b is not None:
    assert args.prefix_b in [0,2,6] and N>=4 and not args.plain
    prefix=[(1,args.prefix_b,7),(1,args.prefix_b,8),(0,9,10),(0,1,11)]
    for i,(op,a,b) in enumerate(prefix):
        a,b=sorted((a,b))
        c.clause(O[i] if op else -O[i]);c.clause(A[i][a]);c.clause(B[i][b])
    fixed_h_index=3
if args.pin_prefix:
    assert args.prefix_b is None and not args.plain
    prefix=json.loads(Path(args.pin_prefix).read_text())
    if isinstance(prefix,dict):prefix=prefix['gates']
    assert 0<len(prefix)<=N
    for i,(op,a,b) in enumerate(prefix):
        a,b=sorted((a,b));assert op in[0,1]and 0<=a<=b<n+i
        c.clause(O[i] if op else -O[i]);c.clause(A[i][a]);c.clause(B[i][b])
    fixed_h_index=len(prefix)-1
V={}
for x in rows:
    values=[]
    for i in range(N):
        u,v,w=c.var(),c.var(),c.var()
        for src in range(n+i):
            for sels,dest in ((A[i],u),(B[i],v)):
                if src<n: c.clause(-sels[src],dest if x>>src&1 else -dest)
                else:
                    r=values[src-n]
                    c.clause(-sels[src],-dest,r); c.clause(-sels[src],dest,-r)
        o=O[i]
        c.clause(o,-u,-v,w); c.clause(o,u,-w); c.clause(o,v,-w)
        c.clause(-o,u,v,-w); c.clause(-o,-u,w); c.clause(-o,-v,w)
        values.append(w)
    c.clause(values[-1] if x in positive else -values[-1])
    V[x]=values
if args.productive:
    for i in range(N): c.clause(*(V[x][i] for x in positive))
if args.primary_minimal:
    for i in range(N):
        for src in range(n):
            differences=[V[x][i] if not(x>>src&1) else -V[x][i]for x in positive]
            increases=[-V[x][i]for x in negative if x>>src&1]
            c.clause(*(differences+increases))
if args.fresh:
    for i in range(N):
        vals=[V[x][i] for x in rows]
        c.clause(*vals); c.clause(*(-v for v in vals))
        for src in range(n): c.clause(*(v if not(x>>src&1) else -v for x,v in zip(rows,vals)))
        for j in range(i):
            diffs=[]
            for x in rows:
                u,v=V[x][j],V[x][i];d=c.var();diffs.append(d)
                c.clause(-d,u,v);c.clause(-d,-u,-v);c.clause(d,u,-v);c.clause(d,-u,v)
            c.clause(*diffs)
H=[]
if not args.plain:
    H=[c.var() for _ in range(N)]
    c.one(H)
    if fixed_h_index is not None: c.clause(H[fixed_h_index])
    for i,h in enumerate(H):
        c.clause(-h,V[386][i])
        for x in bad_negative: c.clause(-h,-V[x][i])
        c.clause(-h,*(V[x][i] for x in positive))
cnf=root/f'{args.tag}.cnf'; c.write(cnf)
stdout=root/f'{args.tag}.stdout'; stderr=root/f'{args.tag}.stderr'
command=[str(solver),'-t',str(args.seconds),'--seed='+str(args.seed)]
if args.sat_preset: command.append('--sat')
command.append(str(cnf))
print('START',started,vars(args),'variables',c.nv,'clauses',len(c.cs),flush=True)
with stdout.open('w') as out,stderr.open('w') as err:
    try:
        run=subprocess.run(command,stdout=out,stderr=err,timeout=args.seconds+10)
        code=run.returncode
    except subprocess.TimeoutExpired: code='external timeout'
text=stdout.read_text()
status='SAT' if 's SATISFIABLE' in text else 'UNSAT' if 's UNSATISFIABLE' in text else 'UNKNOWN'
result={'started_at':started,'finished_at':datetime.now(timezone.utc).isoformat(),
        'elapsed_seconds':time.monotonic()-start,'arguments':vars(args),'status':status,
        'exit':code,'rows':rows,'variables':c.nv,'clauses':len(c.cs),
        'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest(),
        'solver_arguments':command[1:],'strict_earlier_wires':True,
        'statement_is_auxiliary_not_posted_gap':True}
if status=='SAT':
    pos={int(v) for line in text.splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v)>0}
    gates=[(int(O[i] in pos),next(j for j,v in enumerate(A[i]) if v in pos),
            next(j for j,v in enumerate(B[i]) if v in pos)) for i in range(N)]
    h=next((i for i,v in enumerate(H) if v in pos),None)
    def ev(x):
        values=[bool(x>>j&1) for j in range(n)]
        for op,a,b in gates: values.append((values[a] or values[b]) if op else (values[a] and values[b]))
        return values
    false_negatives=[x for x in range(512) if target(x) and not ev(x)[-1]]
    false_positives=[x for x in range(512) if ev(x)[-1] and not target(x)]
    if args.relax_negative is None:
        bad=false_negatives+false_positives
    else:
        bad=false_negatives+[x for x in false_positives if x&~args.relax_negative]
    if args.extra_negative is not None and ev(args.extra_negative)[-1]:
        bad.append(args.extra_negative)
    bad_h=[] if h is None else [x for x in range(512) if ev(x)[n+h] and x&25 and not target(x)]
    h_true_triads=[] if h is None else [x for x in (100,386) if ev(x)[n+h]]
    h_true_edges=[] if h is None else [x for x in positive if ev(x)[n+h]]
    result.update({'full_rows_checked':512,'bad_output_rows':bad,'bad_auxiliary_rows':bad_h,
                   'false_negative_rows':false_negatives,'false_positive_rows':false_positives,
                   'validation_kind':'exact function' if args.relax_negative is None else
                       'superfunction; false positives confined to the exceptional independent set; extra negative checked',
                   'H_gate_index':h,'H_true_triads':h_true_triads,'H_true_edge_rows':h_true_edges,
                   'gates':gates})
    valid=not bad and (args.plain or (not bad_h and 386 in h_true_triads and h_true_edges))
    if valid:
        (root/f'{args.tag}-witness.json').write_text(json.dumps(result,indent=2)+'\n')
        print('VALIDATED_WITNESS',json.dumps(result),flush=True)
    else: print('INVALID_ENCODING_MODEL',json.dumps(result),flush=True)
(root/f'{args.tag}-result.json').write_text(json.dumps(result,indent=2)+'\n')
print('RESULT',json.dumps(result),flush=True)
