"""Untrusted structured monotone-circuit search; independently check any witness."""
import argparse
import itertools
import json
import os
from pathlib import Path
import resource
import time

p = argparse.ArgumentParser()
p.add_argument('graph')
p.add_argument('--seconds', type=int, default=120)
p.add_argument('--out', required=True)
p.add_argument('--recipe-cap', type=int, default=24)
p.add_argument('--max-clean-size', type=int, default=99)
p.add_argument('--no-solve', action='store_true')
p.add_argument('--rounds', type=int, default=1)
p.add_argument('--mixed-triples', action='store_true')
p.add_argument('--mixed-guards', action='store_true')
p.add_argument('--mixed-width', type=int, default=1)
p.add_argument('--dump-library')
p.add_argument('--edge-partition', action='store_true')
p.add_argument('--allow-baseline', action='store_true')
p.add_argument('--sum-products', type=int, default=0)
p.add_argument('--extra-linear-json')
args = p.parse_args()
resource.setrlimit(resource.RLIMIT_AS, (3_000_000_000, 3_000_000_000))
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
start = time.monotonic()
graph = json.loads(Path(args.graph).read_text())
n, edges = graph['n'], [tuple(e) for e in graph['edges']]
m = len(edges)
nb = [0] * n
for a, b in edges:
    nb[a] |= 1 << b
    nb[b] |= 1 << a
mis = []
for s in range(1 << n):
    if any(s >> a & 1 and s >> b & 1 for a, b in edges):
        continue
    if all(s >> v & 1 or nb[v] & s for v in range(n)):
        mis.append(s)
rows = [(1 << a) | (1 << b) for a, b in edges] + mis
values = [sum(((s >> i) & 1) << r for r, s in enumerate(rows)) for i in range(n)]
pos = (1 << m) - 1
full = (1 << len(rows)) - 1
neg = full ^ pos

# Acyclic layers: ORs of inputs, ANDs of two ORs, then guarded/intersected products.
linear = {1 << i for i in range(n)}
for i in range(n):
    s = nb[i]
    t = s
    while t:
        linear.add(t)
        t = (t - 1) & s
for a, b in itertools.combinations(range(n), 2):
    linear.add((1 << a) | (1 << b))
if args.extra_linear_json:
    for support in json.loads(Path(args.extra_linear_json).read_text()):
        mask=sum(1<<i for i in support)
        part=mask
        while part:
            linear.add(part);part=(part-1)&mask
# Include mixed triples around an edge and the two color-class disjunctions.
if args.mixed_triples:
    for a, b in edges:
        for c in range(n):
            linear.add((1 << a) | (1 << b) | (1 << c))
color = [None] * n
for r in range(n):
    if color[r] is not None:
        continue
    color[r] = 0
    queue = [r]
    for a in queue:
        for b in range(n):
            if nb[a] >> b & 1 and color[b] is None:
                color[b] = 1 - color[a]
                queue.append(b)
for c in (0, 1):
    side = [i for i in range(n) if color[i] == c]
    # Prefixes make large disjunctions constructible without exponential data.
    s = 0
    for i in side:
        s |= 1 << i
        linear.add(s)

nodes = [{'kind': 'input', 'value': values[i], 'cost': 0, 'input': i} for i in range(n)]
recipes = [[] for _ in range(n)]
by_value = {v: i for i, v in enumerate(values)}
linear_ids = {}

def make_node(kind, value, recipe, estimate):
    if value in by_value:
        k = by_value[value]
        if nodes[k]['kind'] == 'input':
            return k
    else:
        k = len(nodes)
        by_value[value] = k
        nodes.append({'kind': kind, 'value': value, 'cost': estimate})
        recipes.append([])
    # Do not add upward/cyclic recipes after semantic deduplication.
    if (nodes[k]['kind'] in ('clean','guarded') and
        all(nodes[a]['kind'] not in ('clean','guarded') for a in recipe[1:])) or all(a < k for a in recipe[1:]):
        recipes[k].append(recipe)
        nodes[k]['cost'] = min(nodes[k]['cost'], estimate)
        if len(recipes[k]) > args.recipe_cap * 8:
            recipes[k] = sorted(set(recipes[k]), key=lambda r: (nodes[r[1]]['cost'] + nodes[r[2]]['cost'], r))[:args.recipe_cap*4]
    return k

for s in sorted(linear, key=lambda z: (z.bit_count(), z)):
    if s.bit_count() == 1:
        linear_ids[s] = s.bit_length() - 1
        continue
    val = 0
    for i in range(n):
        if s >> i & 1:
            val |= values[i]
    all_recipes = []
    t = (s - 1) & s
    while t:
        u = s ^ t
        if t < u and t in linear_ids and u in linear_ids:
            a, b = linear_ids[t], linear_ids[u]
            all_recipes.append(('or', min(a, b), max(a, b)))
        t = (t - 1) & s
    if not all_recipes:
        continue
    k = make_node('linear', val, all_recipes[0], s.bit_count() - 1)
    for r in all_recipes[1:]:
        make_node('linear', val, r, s.bit_count() - 1)
    linear_ids[s] = k
L = sorted(set(linear_ids.values()))
dirty = set()
clean = set()
for a, b in itertools.combinations(L, 2):
    val = nodes[a]['value'] & nodes[b]['value']
    if not val & pos or val in (nodes[a]['value'], nodes[b]['value']):
        continue
    if val & neg and (val & pos).bit_count() < 2:
        continue
    k = make_node('product' if val & neg else 'clean', val, ('and', a, b),
                  nodes[a]['cost'] + nodes[b]['cost'] + 1)
    (dirty if val & neg else clean).add(k)
print(json.dumps({'stage':'products','rows':len(rows),'linear':len(L),
                  'dirty':len(dirty),'clean':len(clean),'nodes':len(nodes),
                  'seconds':time.monotonic()-start}), flush=True)
if args.mixed_guards:
    extended=set(dirty)
    for a in sorted(dirty):
        if nodes[a]['cost'] > 4:
            continue
        for b in L:
            if nodes[b]['cost'] >= args.mixed_width:
                continue
            val=nodes[a]['value'] | nodes[b]['value']
            if val in (nodes[a]['value'],nodes[b]['value']):
                continue
            k=make_node('mixed',val,('or',min(a,b),max(a,b)),nodes[a]['cost']+nodes[b]['cost']+1)
            extended.add(k)
    dirty=extended
    print(json.dumps({'stage':'mixed','dirty':len(dirty),'nodes':len(nodes),
                      'seconds':time.monotonic()-start}),flush=True)

# Only retain guarded products that are semantically clean on every negative row.
def try_clean(a, b):
    va, vb = nodes[a]['value'], nodes[b]['value']
    if va & vb & neg:
        return
    val = va & vb & pos
    size = val.bit_count()
    if size < 2 or size > args.max_clean_size or val in (va, vb):
        return
    k = make_node('guarded', val, ('and', min(a,b), max(a,b)),
                  nodes[a]['cost'] + nodes[b]['cost'] + 1)
    clean.add(k)

for a in sorted(dirty):
    for b in L:
        try_clean(a, b)
D = sorted(dirty)
post = [0] * len(mis)
for j,k in enumerate(D):
    mask = nodes[k]['value'] >> m
    while mask:
        bit = mask & -mask
        post[bit.bit_length()-1] |= 1 << j
        mask ^= bit
all_dirty = (1 << len(D)) - 1
for j,a in enumerate(D):
    candidates = all_dirty ^ ((1 << (j+1))-1)
    mask = nodes[a]['value'] >> m
    while mask and candidates:
        bit = mask & -mask
        candidates &= ~post[bit.bit_length()-1]
        mask ^= bit
    while candidates:
        bit = candidates & -candidates
        try_clean(a, D[bit.bit_length()-1])
        candidates ^= bit
print(json.dumps({'stage':'guards','dirty':len(dirty),'clean':len(clean),
                  'nodes':len(nodes),'recipes':sum(map(len,recipes)),
                  'seconds':time.monotonic()-start}), flush=True)

if args.sum_products:
    old_dirty=sorted(dirty)
    def sum_node(a,b):
        val=nodes[a]['value']|nodes[b]['value']
        if val==nodes[a]['value']:return a
        if val==nodes[b]['value']:return b
        return make_node('sum',val,('or',min(a,b),max(a,b)),nodes[a]['cost']+nodes[b]['cost']+1)
    for q in L:
        if nodes[q]['cost']<2:
            continue
        qv=nodes[q]['value']
        eligible=[a for a in old_dirty if nodes[a]['cost']<=5 and
                  nodes[a]['value']&qv&pos and not(nodes[a]['value']&qv&neg)]
        cov=0
        for a in eligible:cov|=nodes[a]['value']&qv&pos
        if cov.bit_count()<6:
            continue
        for cnt in range(2,args.sum_products+1):
            for terms in itertools.combinations(eligible,cnt):
                supports=[nodes[a]['value']&qv&pos for a in terms]
                u=0
                for s in supports:u|=s
                if u.bit_count()<6:
                    continue
                redundant=False
                for i,s in enumerate(supports):
                    other=0
                    for j,x in enumerate(supports):
                        if i!=j:other|=x
                    if not(s&~other):redundant=True
                if redundant:continue
                for last in range(cnt):
                    partial=[a for i,a in enumerate(terms) if i!=last]
                    s=partial[0]
                    for a in partial[1:]:s=sum_node(s,a)
                    s=sum_node(s,terms[last])
                    k=make_node('guarded',u,('and',min(q,s),max(q,s)),
                                nodes[q]['cost']+nodes[s]['cost']+1)
                    clean.add(k)
    print(json.dumps({'stage':'factored_sums','clean':len(clean),'nodes':len(nodes),
                      'recipes':sum(map(len,recipes)),'seconds':time.monotonic()-start}),flush=True)

# Prune recipe duplicates and retain diverse inexpensive constructions per value.
for k in range(n, len(nodes)):
    rr = sorted(set(recipes[k]), key=lambda r: (nodes[r[1]]['cost'] + nodes[r[2]]['cost'], r))
    if len(rr) > args.recipe_cap:
        rr = rr[:args.recipe_cap]
    recipes[k] = rr
needed = set(clean)
todo = list(clean)
while todo:
    k = todo.pop()
    for _, a, b in recipes[k]:
        for v in (a,b):
            if v not in needed:
                needed.add(v)
                todo.append(v)
clean = sorted(k for k in clean if recipes[k])
active = sorted(k for k in needed if k >= n and recipes[k])
rs = [(k,r) for k in active for r in recipes[k]]
stats = {'graph':graph,'rows':rows,'positive_count':m,'linear_count':len(L),
         'dirty_count':len(dirty),'clean_count':len(clean),'active_nodes':len(active),
         'recipe_count':len(rs),'generation_seconds':time.monotonic()-start}
if args.dump_library:
    Path(args.dump_library).write_text(json.dumps({'graph':graph,'rows':rows,'nodes':nodes,
            'recipes':recipes,'clean':clean,'active':active}))
print(json.dumps({'stage':'pruned',**{k:v for k,v in stats.items() if k not in ('graph','rows')}}),flush=True)
if args.no_solve:
    Path(args.out).write_text(json.dumps(stats, indent=2))
    raise SystemExit

import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_array
xvars = {k:i for i,k in enumerate(active)}
ybase = len(active)
tbase = ybase + len(rs)
termvars = {k:tbase+i for i,k in enumerate(clean)}
nv = tbase + len(clean)
c = np.zeros(nv)
c[:ybase] = 1
c[tbase:] = 1
row_i, col_i, dat, lb, ub = [], [], [], [], []
def constraint(coeffs, lo, hi):
    ix = len(lb)
    for j, v in coeffs:
        row_i.append(ix); col_i.append(j); dat.append(float(v))
    lb.append(lo);ub.append(hi)
by_out = {k:[] for k in active}
for j,(k,r) in enumerate(rs):
    y = ybase+j
    by_out[k].append(y)
    for a in r[1:]:
        if a >= n:
            constraint([(y,1),(xvars[a],-1)],-np.inf,0)
for k in active:
    constraint([(j,1) for j in by_out[k]]+[(xvars[k],-1)],0,0)
for k in clean:
    constraint([(termvars[k],1),(xvars[k],-1)],-np.inf,0)
for e in range(m):
    constraint([(termvars[k],1) for k in clean if nodes[k]['value'] >> e & 1],1,1 if args.edge_partition else np.inf)
# Search only for a strict improvement; a feasible result is the useful artifact.
upper = graph['star_cover_upper']
constraint([(j,1) for j in range(ybase)] + [(j,1) for j in range(tbase,nv)],-np.inf,upper+int(args.allow_baseline))
matrix=coo_array((np.asarray(dat),(np.asarray(row_i,dtype=np.int32),np.asarray(col_i,dtype=np.int32))),shape=(len(lb),nv)).tocsc()
print(json.dumps({'stage':'milp','variables':nv,'constraints':len(lb),'nnz':len(dat),
                  'seconds':time.monotonic()-start}),flush=True)
res=milp(c,integrality=np.ones(nv),bounds=Bounds(0,1),
         constraints=LinearConstraint(matrix,np.asarray(lb),np.asarray(ub)),
         options={'time_limit':args.seconds,'mip_rel_gap':0,'presolve':True,
                  'threads':1,'disp':True})
stats['solver']={k:getattr(res,k,None) for k in ('message','status','success','fun','mip_node_count','mip_dual_bound','mip_gap')}
stats['total_seconds']=time.monotonic()-start
if res.x is not None:
    chosen={k:r for j,(k,r) in enumerate(rs) if res.x[ybase+j]>.5}
    outputs=[k for k in clean if res.x[termvars[k]]>.5]
    wire={i:i for i in range(n)}
    gates=[]
    def emit(k):
        if k in wire:
            return
        op,a,b=chosen[k]
        emit(a);emit(b)
        gates.append([op,wire[a],wire[b]])
        wire[k]=n+len(gates)-1
    for k in outputs:
        emit(k)
    out=wire[outputs[0]]
    for k in outputs[1:]:
        gates.append(['or',out,wire[k]])
        out=n+len(gates)-1
    assert len(gates)<upper+int(args.allow_baseline)
    wrong=[]
    for s in range(1<<n):
        w=[bool(s>>i&1) for i in range(n)]
        for op,a,b in gates:
            w.append((w[a] and w[b]) if op=='and' else (w[a] or w[b]))
        goal=any(s>>a&1 and s>>b&1 for a,b in edges)
        if w[out]!=goal:
            wrong.append(s)
    stats['witness']={'gates':gates,'output':out,'wrong_rows':wrong}
    assert not wrong
Path(args.out).write_text(json.dumps(stats,indent=2))
print(json.dumps(stats['solver']),flush=True)
