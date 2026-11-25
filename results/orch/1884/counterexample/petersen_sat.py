import argparse, itertools, json, shutil, resource
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('--gates',type=int,default=18)
parser.add_argument('--control',action='store_true')
parser.add_argument('--monotone-internal',action='store_true')
parser.add_argument('--cofactor-rows',action='store_true')
parser.add_argument('--max-nots',type=int,choices=[0,1])
parser.add_argument('--exact-nots',type=int,choices=[1])
parser.add_argument('--deleted-zero',action='store_true')
parser.add_argument('--single-polarity-readers',action='store_true')
parser.add_argument('--rows')
parser.add_argument('--seed-gates')
parser.add_argument('--stem')
args=parser.parse_args()
base=Path('/tmp/oec/pequalnp-pilot-154/counterexample')
stem=args.stem or ('petersen-control' if args.control else 'petersen18')
k=args.gates
logical_n=9 if args.deleted_zero else 10
n=logical_n+(0 if args.deleted_zero else 1)
table_size=1<<logical_n
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
if args.deleted_zero:edges=[(a-1,b-1) for a,b in edges if a!=0 and b!=0]
edge_masks=[(1<<a)|(1<<b) for a,b in edges]
target=[any(x&e==e for e in edge_masks) for x in range(table_size)]
tests=list(range(table_size))
if args.monotone_internal or args.cofactor_rows:
    tests=[x for x in range(table_size) if
      (target[x] and all(not(x>>j&1) or not target[x^(1<<j)] for j in range(1,logical_n))) or
      (not target[x] and all((x>>j&1) or target[x|(1<<j)] for j in range(1,logical_n)))]
    for x in range(table_size):
        assert any((y&1)==(x&1) and target[y]==target[x] and
          ((y&x)==y if target[x] else (y&x)==x) for y in tests)
if args.rows:
    tests=sorted(set(json.loads(Path(args.rows).read_text())))
    assert tests and all(type(x)==int and 0<=x<table_size for x in tests)
covers=[q for q in range(table_size) if all(q&e for e in edge_masks)]
cover=min(covers,key=lambda q:(q.bit_count(),q))
assert cover.bit_count()==(5 if args.deleted_zero else 6)
parts={v:[] for v in range(logical_n) if cover>>v&1}
for a,b in edges:
    v=a if a in parts else b
    parts[v].append(b if v==a else a)
assert all(parts.values())
standard=[];terms=[]
for v,q in parts.items():
    w=q[0]
    for u in q[1:]:
        standard.append((1,w,u));w=n+len(standard)-1
    standard.append((0,v,w));terms.append(n+len(standard)-1)
w=terms[0]
for u in terms[1:]:
    standard.append((1,w,u));w=n+len(standard)-1
assert len(standard)==(16 if args.deleted_zero else 20)
standard=[(op,*sorted((a,b))) for op,a,b in standard]
seed=standard[:k]
if args.seed_gates:seed=json.loads(Path(args.seed_gates).read_text())
assert len(seed)==k
seed_values=[]
for x in range(table_size):
    vs=[bool(x>>i&1) for i in range(logical_n)]
    if not args.deleted_zero:vs.append(not bool(x&1))
    for op,a,b in seed:
        vs.append((vs[a] and vs[b]) if op==0 else (vs[a] or vs[b]) if op==1 else not vs[a])
    seed_values.append(vs)
if k==len(standard):assert all(vs[-1]==target[x] for x,vs in enumerate(seed_values))

nv=0;nc=0
body=(base/(stem+'.cnf.body')).open('w')
def new(preferred=True):
    global nv
    nv+=1
    return nv if preferred else -nv
def neg(lit):return not lit if isinstance(lit,bool) else -lit
def add(*ls):
    global nc
    out=[]
    for lit in ls:
        if isinstance(lit,bool):
            if lit:return
        elif lit not in out:
            if -lit in out:return
            out.append(lit)
    body.write(' '.join(map(str,out))+' 0\n');nc+=1
def amo(xs):
    if len(xs)<2:return
    prev=new(xs[0]>0)
    add(-xs[0],prev)
    pref=xs[0]>0
    for x in xs[1:-1]:
        pref=pref or x>0
        cur=new(pref)
        add(-x,cur);add(-prev,cur);add(-x,-prev)
        prev=cur
    add(-xs[-1],-prev)
def one(xs):add(*xs);amo(xs)
def mux_eq(sel,dst,src):add(-sel,-dst,src);add(-sel,dst,neg(src))

ops=[];sels=[];values=[]
for g in range(k):
    sop,sa,sb=seed[g]
    op=[new(t==sop) for t in range(3)];one(op);ops.append(op)
    if args.monotone_internal:add(-op[2])
    ss=[[new(w==(sa if port==0 else sb)) for w in range(n+g)] for port in range(2)]
    sels.append(ss)
    for sp in ss:one(sp)
    for a in range(n+g):
        for b in range(a):add(op[2],-ss[0][a],-ss[1][b])
    for a in range(n+g):add(-op[2],-ss[0][a],ss[1][a])
    gv={}
    for x in tests:
        ports=[new(seed_values[x][sa]),new(seed_values[x][sb])]
        for port in range(2):
            for w,sel in enumerate(ss[port]):
                src=bool((x>>w)&1) if w<logical_n else not bool(x&1) if w<n else values[w-n][x]
                mux_eq(sel,ports[port],src)
        a,b=ports;v=new(seed_values[x][n+g]);gv[x]=v
        add(-op[0],-v,a);add(-op[0],-v,b);add(-op[0],v,-a,-b)
        add(-op[1],v,-a);add(-op[1],v,-b);add(-op[1],-v,a,b)
        add(-op[2],v,a);add(-op[2],-v,-a)
    values.append(gv)
readers=None
if args.single_polarity_readers:
    assert not args.deleted_zero
    readers=[]
    for wire,operation in [(0,1),(10,0)]:
        rr=[]
        for g,ss in enumerate(sels):
            z=new(wire in seed[g][1:]);rr.append(z)
            add(-ss[0][wire],z);add(-ss[1][wire],z)
            add(-z,ss[0][wire],ss[1][wire])
            add(-z,ops[g][operation])
        one(rr);readers.append(rr)
if args.max_nots==0:
    for op in ops:add(-op[2])
elif args.max_nots==1:amo([op[2] for op in ops])
if args.exact_nots==1:one([op[2] for op in ops])
for x in tests:add(values[-1][x] if target[x] else -values[-1][x])
if args.control:
    for g,(op,a,b) in enumerate(seed):
        add(ops[g][op]);add(sels[g][0][a]);add(sels[g][1][b])
body.close()
with (base/(stem+'.cnf')).open('w') as f:
    f.write(f'p cnf {nv} {nc}\n')
    with (base/(stem+'.cnf.body')).open() as source:shutil.copyfileobj(source,f)
metadata={'gates':k,'input_count':n,'logical_input_count':logical_n,
  'extra_not_input':not args.deleted_zero,'edges':edges,'ops':ops,'selectors':sels,'output':n+k-1,
  'seed_gates':seed,'variables':nv,'clauses':nc,'control':args.control,'test_rows':tests,
  'monotone_internal':args.monotone_internal,
  'max_nots':args.max_nots,
  'exact_nots':args.exact_nots,'deleted_zero':args.deleted_zero,
  'single_polarity_readers':args.single_polarity_readers,'reader_indicators':readers,
  'minimum_vertex_cover':cover,'unary_input':None if args.deleted_zero else 'not x0','operations':['and','or','not']}
(base/(stem+'.json')).write_text(json.dumps(metadata))
print(json.dumps({'gates':k,'variables':nv,'clauses':nc,'test_rows':len(tests),'control':args.control,
 'generator_max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}),flush=True)
