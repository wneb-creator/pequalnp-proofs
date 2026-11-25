"""SAT extraction of a circuit from a fixed, acyclic semantic recipe library."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import resource
import subprocess
import time

p=argparse.ArgumentParser()
p.add_argument('library');p.add_argument('--seconds',type=int,default=120)
p.add_argument('--out',required=True);p.add_argument('--allow-baseline',action='store_true')
p.add_argument('--free-helper-json')
p.add_argument('--observed-helper-json')
args=p.parse_args();base=Path(args.out);start=time.monotonic()
raw=Path(args.library).read_bytes();d=json.loads(raw)
n=d['graph']['n'];edges=d['graph']['edges'];nodes=d['nodes'];recipes=d['recipes']
active=d['active'];clean=d['clean'];nv=0;clauses=[]
observed={};protected={i:frozenset([i]) for i in range(n)};observed_overhead=0
if args.observed_helper_json:
    if args.free_helper_json:raise ValueError('select one helper charging mode')
    groups=[frozenset(S) for S in json.loads(Path(args.observed_helper_json).read_text())]
    assert all(len(S)>=2 and all(0<=v<n for v in S) for S in groups)
    assert len(groups)==len(set(groups)) and all(len(A&B)<=1 for A,B in itertools.combinations(groups,2))
    adj=[set() for _ in range(n)]
    for a,b in edges:adj[a].add(b);adj[b].add(a)
    colors=[None]*n
    for first in range(n):
        if colors[first] is not None:continue
        colors[first]=0;queue=[first]
        for a in queue:
            for b in adj[a]:
                if colors[b] is None:colors[b]=1-colors[a];queue.append(b)
                else:assert colors[b]!=colors[a]
    assert all(len(adj[a]&adj[b])<=1 for a,b in itertools.combinations(range(n),2))
    assert all(len({colors[v] for v in S})==1 and all(len(S&A)<=1 for A in adj) for S in groups)
    by_value={z['value']:i for i,z in enumerate(nodes)}
    for S in groups:
        for r in range(2,len(S)+1):
            for part in itertools.combinations(sorted(S),r):
                value=0
                for i in part:value|=nodes[i]['value']
                k=by_value[value];support=frozenset(part)
                assert k not in protected or protected[k]==support
                protected[k]=support
                if support==S:observed[k]=sorted(S)
        observed_overhead+=len(S)-1
    needed=set(active)|set(observed);todo=list(observed)
    while todo:
        k=todo.pop()
        for _,a,b in recipes[k]:
            for v in (a,b):
                if v>=n and v not in needed:needed.add(v);todo.append(v)
    active=sorted(needed)
free_nodes={};program_gates=[];program_nodes=[];program_metadata=None
if args.free_helper_json:
    program_metadata=json.loads(Path(args.free_helper_json).read_text())
    if isinstance(program_metadata,list):
        program_metadata={'gates':[['or',a,b] for a,b in program_metadata],
                          'supports':program_metadata,'outputs':[n+i for i in range(len(program_metadata))]}
    program_gates=program_metadata['gates']
    pvalues=[nodes[i]['value'] for i in range(n)];pids=list(range(n))
    by_value={z['value']:i for i,z in enumerate(nodes)}
    for j,(op,a,b) in enumerate(program_gates):
        if op!='or' or not(0<=a<n+j and 0<=b<n+j):raise ValueError('free program must be a valid OR program')
        value=pvalues[a]|pvalues[b]
        matches=[by_value[value]] if value in by_value else []
        if len(matches)!=1:raise ValueError(('free helper missing/ambiguous',a,b,matches))
        k=matches[0];program_nodes.append(k);pvalues.append(value)
        if k in active:free_nodes[k]=tuple(sorted((pids[a],pids[b])))
        pids.append(k)
def var():
    global nv
    nv+=1;return nv
def clause(*xs):clauses.append(tuple(xs))
x={k:var() for k in active};t={k:var() for k in clean}
y={};out={k:[] for k in active};uses={k:[] for k in range(len(nodes))}
for k in active:
    for r in recipes[k]:
        if k in free_nodes and tuple(r)!=('or',*free_nodes[k]):continue
        if k in protected and (r[0]!='or' or r[1] not in protected or r[2] not in protected or
                               protected[r[1]]|protected[r[2]]!=protected[k]):continue
        v=var();y[v]=(k,r);out[k].append(v)
        clause(-v,x[k])
        for a in r[1:]:
            uses[a].append(v)
            if a>=n:clause(-v,x[a])
for k in active:
    clause(-x[k],*out[k])
    # An output-reaching producer selection is sufficient; unused gates can go.
    if k in observed:clause(x[k])
    else:clause(-x[k],*uses[k],*([t[k]] if k in t else []))
    # At most one producer per selected semantic wire.
    prev=None
    for v in out[k][:-1]:
        cur=var();clause(-v,cur)
        if prev is not None:clause(-prev,cur);clause(-v,-prev)
        prev=cur
    if len(out[k])>1:clause(-out[k][-1],-prev)
for k in clean:clause(-t[k],x[k])
for e in range(len(edges)):
    clause(*(t[k] for k in clean if nodes[k]['value']>>e&1))
for i in {a for e in edges for a in e}:
    clause(*uses[i])

# Forward sequential cardinality counter. If too many charged gates/outputs are
# true, propagation forces the forbidden overflow literal regardless of choices
# for the auxiliary variables.
upper=d['graph'].get('star_cover_upper')
if upper is None:
    tau=min(s.bit_count() for s in range(1<<n) if all(s>>a&1 or s>>b&1 for a,b in edges))
    upper=len(edges)+tau-1
paid_limit=upper+int(args.allow_baseline)
budget=paid_limit+observed_overhead
previous=[]
charged=[v for k,v in x.items() if k not in free_nodes]+list(t.values())
for i,v in enumerate(charged):
    current=[var() for _ in range(min(i+1,budget))]
    clause(-v,current[0])
    for j,s in enumerate(previous):
        clause(-s,current[j])
        if j+1<budget:clause(-v,-s,current[j+1])
        else:clause(-v,-s)
    previous=current
cnf=base.with_suffix('.cnf');log=base.with_suffix('.solver.log')
with cnf.open('w') as f:
    f.write(f'p cnf {nv} {len(clauses)}\n')
    for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
print(json.dumps({'variables':nv,'clauses':len(clauses),'budget':budget,
                  'generation_seconds':time.monotonic()-start}),flush=True)
def cap():
    resource.setrlimit(resource.RLIMIT_AS,(2_000_000_000,2_000_000_000))
with log.open('w') as f:
    r=subprocess.run(['/tmp/oec/pequalnp-pilot-178/toolchain/lean-4.36.0-linux/bin/cadical',
                      '--sat','-t',str(args.seconds),str(cnf)],stdout=f,stderr=subprocess.STDOUT,
                      preexec_fn=cap)
result={'graph':d['graph'],'exit':r.returncode,'seconds':time.monotonic()-start,
        'library_sha256':hashlib.sha256(raw).hexdigest(),'variables':nv,'clauses':len(clauses),
        'budget':budget,'paid_limit':paid_limit,'helper_overhead':observed_overhead,
        'observed_helper_supports':list(observed.values()),
        'scope':'only the supplied finite recipe library'}
if r.returncode==10:
    model=set()
    for line in log.read_text().splitlines():
        if line.startswith('v '):model.update(int(s) for s in line[2:].split() if int(s)>0)
    chosen={k:r for v,(k,r) in y.items() if v in model}
    terms=[k for k in clean if t[k] in model]
    wire={i:i for i in range(n)};gates=[list(g) for g in program_gates];visiting=set();referenced_free=set()
    for j,k in enumerate(program_nodes):wire.setdefault(k,n+j)
    def emit(k):
        if k in wire:
            if k in free_nodes:referenced_free.add(k)
            return
        assert k not in visiting
        visiting.add(k)
        op,a,b=chosen[k];emit(a);emit(b)
        gates.append([op,wire[a],wire[b]]);wire[k]=n+len(gates)-1
        visiting.remove(k)
    for k in observed:emit(k)
    for k in terms:emit(k)
    output=wire[terms[0]]
    for k in terms[1:]:
        gates.append(['or',output,wire[k]]);output=n+len(gates)-1
    paid_size=len(gates)-len(program_gates)-observed_overhead
    assert paid_size<paid_limit
    wrong=[]
    for s in range(1<<n):
        w=[bool(s>>i&1) for i in range(n)]
        for op,a,b in gates:w.append((w[a] and w[b]) if op=='and' else (w[a] or w[b]))
        want=any(s>>a&1 and s>>b&1 for a,b in edges)
        if w[output]!=want:wrong.append(s)
        for k,S in observed.items():assert w[wire[k]]==any(s>>a&1 for a in S)
    result['witness']={'size':len(gates),'paid_size':paid_size,
                       'free_program':program_metadata,'referenced_free_nodes':sorted(referenced_free),
                       'observed_helpers':[{'support':S,'wire':wire[k]} for k,S in observed.items()],
                       'gates':gates,'output':output,'wrong_rows':wrong}
    assert not wrong
base.write_text(json.dumps(result,indent=2))
print(json.dumps({k:v for k,v in result.items() if k not in ('graph','witness')}),flush=True)
if 'witness' in result:print('FULLY_VERIFIED_SIZE',result['witness']['size'],'PAID',result['witness']['paid_size'],flush=True)
