import argparse
import importlib.util
import json
import resource
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('--seed',type=int,required=True)
parser.add_argument('--seconds',type=int,required=True)
parser.add_argument('--size',type=int,required=True)
parser.add_argument('--rows')
parser.add_argument('--known',action='store_true')
parser.add_argument('--badedge',action='store_true')
parser.add_argument('--emit-only',action='store_true')
args=parser.parse_args()
resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,4*1024**3))
spec=importlib.util.spec_from_file_location('zs',str(Path(__file__).with_name('synth-2056.py')))
z=importlib.util.module_from_spec(spec)
spec.loader.exec_module(z)
base=Path(__file__).resolve().parent
data=json.loads((base/'theta4-data.json').read_text())
rows=json.loads(Path(args.rows).read_text()) if args.rows else data['rows']
E=data['edges']
n=data['n']
size=args.size
w=len(rows)
def bv(v,b):
    return f'(_ bv{v} {b})'
def target(r):
    return any(((r>>a)&1) and ((r>>b)&1) for a,b in E)
assert all((1<<a)|(1<<b) in rows for a,b in E)
true_mask=sum(int(target(r))<<k for k,r in enumerate(rows))
false_mask=((1<<w)-1)^true_mask
assert len(rows)==len(set(rows))
full_negatives=set(data['negative_rows']).issubset(set(rows))
vals=[bv(sum(((r>>i)&1)<<k for k,r in enumerate(rows)),w) for i in range(n)]
clean=['false']*n
lines=['(set-logic QF_BV)']
for j in range(size):
    m=n+j
    sw=m.bit_length()
    for name,bits in [(f'a{j}',sw),(f'b{j}',sw),(f'o{j}',2),(f'v{j}',w)]:
        lines.append(f'(declare-const {name} (_ BitVec {bits}))')
    lines.extend([f'(assert (bvult a{j} {bv(m,sw)}))',f'(assert (bvult b{j} {bv(m,sw)}))',f'(assert (bvult o{j} #b10))',f'(assert (bvule a{j} b{j}))'])
    def source(v,values):
        expr=values[-1]
        for k in reversed(range(len(values)-1)):
            expr=f'(ite (= {v} {bv(k,sw)}) {values[k]} {expr})'
        return expr
    a,b=source(f'a{j}',vals),source(f'b{j}',vals)
    lines.append(f'(assert (= v{j} (let ((a {a}) (b {b})) (ite (= o{j} #b00) (bvand a b) (bvor a b)))))')
    active=f'(not (= a{j} b{j}))'
    if j==0:
        lines.append(f'(assert {active})')
    else:
        lines.append(f'(assert (=> (not {active}) (and (= o{j} #b01) (= a{j} {bv(n+j-1,sw)}))))')
        lines.append(f'(assert (=> (= a{j-1} b{j-1}) (not {active})))')
    if full_negatives:
        for prev in vals+[bv(0,w),bv((1<<w)-1,w)]:
            worse=f'(and (= (bvand (bvand v{j} {bv(true_mask,w)}) (bvnot {prev})) {bv(0,w)}) (= (bvand (bvand {prev} {bv(false_mask,w)}) (bvnot v{j})) {bv(0,w)}))'
            lines.append(f'(assert (=> {active} (not {worse})))')
    edge_profile=f'(bvand v{j} {bv(true_mask,w)})'
    lines.append(f'(assert (not (= {edge_profile} {bv(0,w)})))')
    singleton=f'(= (bvand {edge_profile} (bvsub {edge_profile} {bv(1,w)})) {bv(0,w)})'
    direct=f'(and (= o{j} #b00) (bvult b{j} {bv(n,sw)}))' if m>n else f'(= o{j} #b00)'
    lines.append(f'(assert (=> {singleton} {direct}))')
    lines.append(f'(declare-const clean{j} Bool)')
    is_clean=f'(= (bvand v{j} {bv(false_mask,w)}) {bv(0,w)})'
    if full_negatives:
        lines.append(f'(assert (= clean{j} {is_clean}))')
        lines.append(f'(assert (not (= (bvand v{j} {bv(false_mask,w)}) {bv(false_mask,w)})))')
    else:
        lines.append(f'(assert (=> clean{j} {is_clean}))')
    ca,cb=source(f'a{j}',clean),source(f'b{j}',clean)
    lines.append(f'(assert (ite (= o{j} #b00) (and (not {ca}) (not {cb})) (and (= {ca} {cb}) (= clean{j} {ca}))))')
    primary=f'(bvult b{j} {bv(n,sw)})' if m>n else 'true'
    lines.append(f'(assert (=> (and (= o{j} #b00) {primary}) clean{j}))')
    vals.append(f'v{j}')
    clean.append(f'clean{j}')
for j in range(size-1):
    uses=[]
    previous='false'
    for k in range(j+1,size):
        sw=(n+k).bit_length()
        use=f'(or (= a{k} {bv(n+j,sw)}) (= b{k} {bv(n+j,sw)}))'
        uses.append(use)
        if previous!='false':
            lines.append(f'(assert (or (not clean{j}) (not {previous}) (not {use})))')
        name=f'seen{j}_{k}'
        lines.append(f'(declare-const {name} Bool)')
        lines.append(f'(assert (= {name} (or {previous} {use})))')
        previous=name
    lines.append('(assert (or '+' '.join(uses)+'))')
    s1,s2=(n+j).bit_length(),(n+j+1).bit_length()
    def extend(v):
        return v if s1==s2 else f'((_ zero_extend {s2-s1}) {v})'
    a,b=extend(f'a{j}'),extend(f'b{j}')
    order=f'(or (bvult {a} a{j+1}) (and (= {a} a{j+1}) (bvult {b} b{j+1})) (and (= {a} a{j+1}) (= {b} b{j+1}) (bvule o{j} o{j+1})))'
    dependency=f'(or (= a{j+1} {bv(n+j,s2)}) (= b{j+1} {bv(n+j,s2)}))'
    lines.append(f'(assert (or {dependency} {order}))')
lines.extend([f'(assert (= v{size-1} {bv(true_mask,w)}))',f'(assert clean{size-1})'])
if args.known:
    raw=data['control_gates']
    assert size==len(raw)
    mapping={i:i for i in range(n)}
    pending=set(range(size))
    for j in range(size):
        choices=[]
        for k in pending:
            op,a,b=raw[k]
            if a in mapping and b in mapping:
                a,b=sorted([mapping[a],mapping[b]])
                choices.append((a,b,op,k))
        a,b,op,k=min(choices)
        pending.remove(k)
        mapping[n+k]=n+j
        sw=(n+j).bit_length()
        lines.extend([f'(assert (= a{j} {bv(a,sw)}))',f'(assert (= b{j} {bv(b,sw)}))',f'(assert (= o{j} {bv(op,2)}))'])
if args.badedge:
    bad_options=[]
    for e,(left,right) in enumerate(data['bad_edges']):
        profiles=[bv(1 if i==left else 2 if i==right else 0,3) for i in range(n)]
        for j in range(size):
            sw=(n+j).bit_length()
            name=f'r{e}p{j}'
            lines.append(f'(declare-const {name} (_ BitVec 3))')
            def read_source(v):
                expr=profiles[-1]
                for k in reversed(range(len(profiles)-1)):
                    expr=f'(ite (= {v} {bv(k,sw)}) {profiles[k]} {expr})'
                return expr
            a,b=read_source(f'a{j}'),read_source(f'b{j}')
            pair='(or (and (= ((_ extract 0 0) a) #b1) (= ((_ extract 1 1) b) #b1)) (and (= ((_ extract 1 1) a) #b1) (= ((_ extract 0 0) b) #b1)))'
            lines.append(f'(assert (= {name} (let ((a {a}) (b {b})) (ite (= o{j} #b00) (ite {pair} #b100 #b000) (bvor a b)))))')
            profiles.append(name)
        bad_options.append(f'(= ((_ extract 2 2) {profiles[-1]}) #b0)')
    lines.append('(assert (or '+' '.join(bad_options)+'))')
text='\n'.join(lines)
query=base/f'theta4-dom-{args.seed}.smt2'
query.write_text(text)
if args.emit_only:
    print(str(query),flush=True)
    raise SystemExit(0)
cfg=z.mkcfg()
z.setcfg(cfg,b'model',b'true')
ctx=z.mkctx(cfg)
z.delcfg(cfg)
mk_tactic=z.bind('Z3_mk_tactic',z.P,[z.P,z.S])
from_tactic=z.bind('Z3_mk_solver_from_tactic',z.P,[z.P,z.P])
solver=from_tactic(ctx,mk_tactic(ctx,b'qfbv'))
z.inc(ctx,solver)
params=z.mkparams(ctx)
z.pinc(ctx,params)
z.puint(ctx,params,z.mkstr(ctx,b'timeout'),args.seconds*1000)
z.puint(ctx,params,z.mkstr(ctx,b'random_seed'),args.seed)
z.sparams(ctx,solver,params)
z.parse(ctx,solver,text.encode())
status=z.check(ctx,solver)
result=z.modelstr(ctx,z.getmodel(ctx,solver)).decode() if status==1 else z.reason(ctx,solver).decode() if status==0 else 'unsat'
record={'status':status,'size':size,'seed':args.seed,'rows':rows,'known':args.known,'badedge':args.badedge,'full_negatives':full_negatives,'result':result}
(base/f'theta4-dom-{args.seed}.json').write_text(json.dumps(record,indent=2))
print(json.dumps({k:record[k] for k in ['status','size','seed','known','badedge','full_negatives']})+(' '+result if status!=1 else ' SAT model saved'),flush=True)
z.delctx(ctx)
