import argparse,ctypes,ctypes.util,hashlib,json,re,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=6);p.add_argument('--gates',type=int,default=8);p.add_argument('--junk',type=int,default=2);p.add_argument('--timeout',type=int,default=120000);p.add_argument('--edges',default='');p.add_argument('--full',action='store_true');p.add_argument('--seed',type=int,default=0);p.add_argument('--prune-edge-support',action='store_true');p.add_argument('--prune-negative-support',action='store_true');p.add_argument('--top-form',action='store_true');p.add_argument('--some-junk-cleaner',action='store_true');p.add_argument('--fixed-circuit',default='');a=p.parse_args()
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
if a.top_form:lines.append(f'(define-fun cleanBits0 () (_ BitVec {k}) (_ bv0 {k}))')
for i in range(k):
    vs=[f'x{j}' for j in range(n)]+[f'v{j}' for j in range(i)]
    for var in ['a','b']:lines.append(f'(declare-fun {var}{i} () (_ BitVec {selw}))')
    lines.append(f'(declare-fun op{i} () Bool)')
    lines.append(f'(assert (bvult a{i} b{i}))')
    lines.append(f'(assert (bvult b{i} (_ bv{n+i} {selw})))')
    def choose(sel,choices=None):
        choices=vs if choices is None else choices
        out=choices[-1]
        for j in reversed(range(len(choices)-1)):out=f'(ite (= {sel} (_ bv{j} {selw})) {choices[j]} {out})'
        return out
    lines.append(f'(define-fun la{i} () (_ BitVec {w}) {choose(f"a{i}")})')
    lines.append(f'(define-fun lb{i} () (_ BitVec {w}) {choose(f"b{i}")})')
    lines.append(f'(define-fun v{i} () (_ BitVec {w}) (ite op{i} (bvand la{i} lb{i}) (bvor la{i} lb{i})))')
    lines.append(f'(define-fun junk{i} () Bool (and op{i} (distinct (bvand v{i} {bv(mask^f)}) {bv(0)})))')
    if a.top_form:
        conechoices=[f'(_ bv0 {k})']*n+[f'fullAnc{j}' for j in range(i)]
        lines.append(f'(define-fun anc{i} () (_ BitVec {k}) (bvor {choose(f"a{i}",conechoices)} {choose(f"b{i}",conechoices)}))')
        lines.append(f'(assert (=> op{i} (= (bvand anc{i} cleanBits{i}) (_ bv0 {k}))))')
        lines.append(f'(define-fun fullAnc{i} () (_ BitVec {k}) (bvor anc{i} (_ bv{1<<i} {k})))')
        lines.append(f'(define-fun cleanBits{i+1} () (_ BitVec {k}) (bvor cleanBits{i} (ite (and op{i} (not junk{i})) (_ bv{1<<i} {k}) (_ bv0 {k}))))')
    if a.some_junk_cleaner:
        cleaners=[f'(= (bvand v{i} {bv((mask^f)&ins[j])}) {bv(0)})' for j in range(n)]
        lines.append(f'(define-fun hasCleaner{i} () Bool (or '+ ' '.join(cleaners)+'))')
    if a.prune_edge_support:
        lines.append(f'(assert (distinct (bvand v{i} {bv(f)}) {bv(0)}))')
    if a.prune_negative_support:
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
if a.some_junk_cleaner:
    lines.append('(assert (or '+' '.join(f'(and junk{i} hasCleaner{i})' for i in range(k))+'))')
fixed=None
if a.fixed_circuit:
    fixed=json.loads(Path(a.fixed_circuit).read_text())['gates'];assert len(fixed)==k
    for i,g in enumerate(fixed):
        aa,bb=sorted([g['a'],g['b']]);assert 0<=aa<bb<n+i and g['op'] in ['and','or']
        lines.append(f'(assert (= a{i} (_ bv{aa} {selw})))')
        lines.append(f'(assert (= b{i} (_ bv{bb} {selw})))')
        lines.append(f'(assert (= op{i} '+('true' if g['op']=='and' else 'false')+'))')
lines.append('(check-sat)')
model_command='(get-value ('+' '.join(f'a{i} b{i} op{i} junk{i}' for i in range(k))+'))'
script='\n'.join(lines)
meta={'n':n,'gates':k,'junk':a.junk,'edges':edges,'critical':not a.full,'rows':rows,'maximal_independent_sets':maxind,'seed':a.seed,'timeout_ms':a.timeout,'prune_edge_support':a.prune_edge_support,'prune_negative_support':a.prune_negative_support,'top_form':a.top_form,'some_junk_cleaner':a.some_junk_cleaner,'fixed_circuit':fixed}
digest=hashlib.sha256(json.dumps(meta,sort_keys=True).encode()).hexdigest()[:12]
r=Path('/tmp/oec/pequalnp-pilot-176');stem=f'twojunk-normalized-{digest}'
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
    junk=[False]*k;gate_tables=[0]*k
    for inp in range(1<<n):
        wires=[bool(inp>>j&1) for j in range(n)]
        for i,g in enumerate(gates):
            value=(wires[g['a']] and wires[g['b']]) if g['op']=='and' else (wires[g['a']] or wires[g['b']])
            wires.append(value)
            if value:gate_tables[i]|=1<<inp
            if g['op']=='and' and value and not edge_true(inp):junk[i]=True
        assert wires[-1]==edge_true(inp),(inp,wires[-1])
    assert all(junk[i]==g['junk'] for i,g in enumerate(gates))
    if a.junk>=0:assert sum(junk)==a.junk
    allF=sum(1<<x for x in range(1<<n) if edge_true(x))
    positivePairs=sum(1<<((1<<u)|(1<<v)) for u,v in edges)
    allInput=[sum(1<<x for x in range(1<<n) if x>>j&1) for j in range(n)]
    wmax=[sum(1<<v for v in range(n) if not (gate_tables[i]&allInput[v]&~allF)) for i in range(k)]
    ancestors=[]
    for i,g in enumerate(gates):
        anc=0
        for operand in [g['a'],g['b']]:
            if operand>=n:anc|=ancestors[operand-n]|(1<<(operand-n))
        ancestors.append(anc)
        if a.top_form and g['op']=='and':
            assert all(not (anc>>j&1 and gates[j]['op']=='and' and not junk[j]) for j in range(i))
        if a.prune_edge_support:assert gate_tables[i]&positivePairs
        if a.prune_negative_support:assert any(not(gate_tables[i]>>x&1) for x in maxind)
    if a.some_junk_cleaner:assert any(junk[i] and wmax[i] for i in range(k))
    print('FULL_TRUTH_TABLE_VALIDATED',json.dumps({'gates':gates,'wmax_bitsets':wmax,'ancestor_bitsets':ancestors}),flush=True)
    (r/(stem+'-model.json')).write_text(json.dumps({'metadata':meta,'gates':gates,'wmax_bitsets':wmax,'ancestor_bitsets':ancestors},indent=2))
elif out.strip()=='unknown':print(z.Z3_eval_smtlib2_string(ctx,b'(get-info :reason-unknown)').decode(),flush=True)
z.Z3_del_context(ctx)
