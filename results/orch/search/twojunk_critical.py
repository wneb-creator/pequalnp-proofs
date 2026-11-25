import argparse,ctypes,ctypes.util,hashlib,json,re,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=6);p.add_argument('--gates',type=int,default=8);p.add_argument('--junk',type=int,default=2);p.add_argument('--timeout',type=int,default=120000);p.add_argument('--edges',default='');p.add_argument('--full',action='store_true');p.add_argument('--seed',type=int,default=0);p.add_argument('--prune-edge-support',action='store_true');a=p.parse_args()
n=a.n;k=a.gates
edges=sorted(set(tuple(sorted(map(int,e.split('-')))) for e in a.edges.split(','))) if a.edges else sorted((min(i,(i+1)%n),max(i,(i+1)%n)) for i in range(n))
assert all(0<=u<v<n for u,v in edges)
adj=[0]*n
for u,v in edges:adj[u]|=1<<v;adj[v]|=1<<u
def edge_true(v):return any(v>>u&1 and v>>z&1 for u,z in edges)
ind=[s for s in range(1<<n) if not edge_true(s)]
maxind=[s for s in ind if all(s>>u&1 or (s&adj[u]) for u in range(n))]
rows=list(range(1<<n)) if a.full else sorted(set([(1<<u)|(1<<v) for u,v in edges]+maxind))
w=len(rows);mask=(1<<w)-1
ins=[sum(1<<i for i,v in enumerate(rows) if v>>j&1) for j in range(n)]
f=sum(1<<i for i,v in enumerate(rows) if edge_true(v))
def bv(x):return f'(_ bv{x} {w})'
lines=['(set-option :produce-models true)',f'(set-option :timeout {a.timeout})',f'(set-option :smt.random_seed {a.seed})','(set-logic QF_AUFBV)']
selw=max(1,(n+k-1).bit_length())
for j,x in enumerate(ins):lines.append(f'(define-fun x{j} () (_ BitVec {w}) {bv(x)})')
for i in range(k):
    vs=[f'x{j}' for j in range(n)]+[f'v{j}' for j in range(i)]
    for var in ['a','b']:lines.append(f'(declare-fun {var}{i} () (_ BitVec {selw}))')
    lines.append(f'(declare-fun op{i} () Bool)')
    lines.append(f'(assert (bvult a{i} b{i}))')
    lines.append(f'(assert (bvult b{i} (_ bv{n+i} {selw})))')
    def choose(sel):
        out=vs[-1]
        for j in reversed(range(len(vs)-1)):out=f'(ite (= {sel} (_ bv{j} {selw})) {vs[j]} {out})'
        return out
    lines.append(f'(define-fun la{i} () (_ BitVec {w}) {choose(f"a{i}")})')
    lines.append(f'(define-fun lb{i} () (_ BitVec {w}) {choose(f"b{i}")})')
    lines.append(f'(define-fun v{i} () (_ BitVec {w}) (ite op{i} (bvand la{i} lb{i}) (bvor la{i} lb{i})))')
    lines.append(f'(define-fun junk{i} () Bool (and op{i} (distinct (bvand v{i} {bv(mask^f)}) {bv(0)})))')
    if a.prune_edge_support:
        lines.append(f'(assert (distinct (bvand v{i} {bv(f)}) {bv(0)}))')
        lines.append(f'(assert (distinct (bvand v{i} {bv(mask^f)}) {bv(mask^f)}))')
    for j in range(i):lines.append(f'(assert (distinct v{i} v{j}))')
    for j in range(n):lines.append(f'(assert (distinct v{i} x{j}))')
    if i>0:lines.append(f'(assert (or (= a{i} (_ bv{n+i-1} {selw})) (= b{i} (_ bv{n+i-1} {selw})) (bvule b{i-1} b{i})))')
lines.append(f'(assert (= v{k-1} {bv(f)}))')
if a.junk>=0:
    countw=max(1,(k+1).bit_length())
    ss=[f'(ite junk{i} (_ bv1 {countw}) (_ bv0 {countw}))' for i in range(k)]
    sm=ss[0]
    for s in ss[1:]:sm=f'(bvadd {sm} {s})'
    lines.append(f'(assert (= {sm} (_ bv{a.junk} {countw})))')
for i in range(k-1):
    readers=[f'(= {v}{j} (_ bv{n+i} {selw}))' for j in range(i+1,k) for v in ['a','b']]
    lines.append('(assert (or '+' '.join(readers)+'))')
if not a.edges:
    lines.append(f'(assert (= a0 (_ bv0 {selw})))')
    lines.append(f'(assert (bvule b0 (_ bv{n//2} {selw})))')
lines.append('(check-sat)')
model_command='(get-value ('+' '.join(f'a{i} b{i} op{i} junk{i}' for i in range(k))+'))'
script='\n'.join(lines)
meta={'n':n,'gates':k,'junk':a.junk,'edges':edges,'critical':not a.full,'rows':rows,'maximal_independent_sets':maxind,'seed':a.seed,'timeout_ms':a.timeout,'prune_edge_support':a.prune_edge_support}
digest=hashlib.sha256(json.dumps(meta,sort_keys=True).encode()).hexdigest()[:12]
r=Path('/tmp/oec/pequalnp-pilot-176');stem=f'twojunk-critical-{digest}'
(r/(stem+'.smt2')).write_text(script);(r/(stem+'.json')).write_text(json.dumps(meta,indent=2))
z=ctypes.CDLL(ctypes.util.find_library('z3'))
z.Z3_mk_config.restype=ctypes.c_void_p;z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p
z.Z3_del_config.argtypes=[ctypes.c_void_p];z.Z3_del_context.argtypes=[ctypes.c_void_p]
z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
conf=z.Z3_mk_config();ctx=z.Z3_mk_context(conf);z.Z3_del_config(conf)
print(json.dumps(meta),flush=True);print('artifact',stem,flush=True)
t=time.time();out=z.Z3_eval_smtlib2_string(ctx,script.encode()).decode();print(out,flush=True);print('elapsed',time.time()-t,flush=True)
if out.strip()=='sat':
    model=z.Z3_eval_smtlib2_string(ctx,model_command.encode()).decode();print(model,flush=True)
    vals={var+idx:(v=='true' if v in ['true','false'] else int(v[2:],2 if v[1]=='b' else 16)) for var,idx,v in re.findall(r'\((a|b|op|junk)(\d+)\s+(#b[01]+|#x[0-9a-f]+|true|false)\)',model)}
    gates=[{'op':'and' if vals['op'+str(i)] else 'or','a':vals['a'+str(i)],'b':vals['b'+str(i)],'junk':vals['junk'+str(i)]} for i in range(k)]
    junk=[False]*k
    for inp in range(1<<n):
        wires=[bool(inp>>j&1) for j in range(n)]
        for i,g in enumerate(gates):
            value=(wires[g['a']] and wires[g['b']]) if g['op']=='and' else (wires[g['a']] or wires[g['b']])
            wires.append(value)
            if g['op']=='and' and value and not edge_true(inp):junk[i]=True
        assert wires[-1]==edge_true(inp),(inp,wires[-1])
    assert all(junk[i]==g['junk'] for i,g in enumerate(gates))
    if a.junk>=0:assert sum(junk)==a.junk
    print('FULL_TRUTH_TABLE_VALIDATED',json.dumps(gates),flush=True)
    (r/(stem+'-model.json')).write_text(json.dumps({'metadata':meta,'gates':gates},indent=2))
elif out.strip()=='unknown':print(z.Z3_eval_smtlib2_string(ctx,b'(get-info :reason-unknown)').decode(),flush=True)
z.Z3_del_context(ctx)
