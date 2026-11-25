import hashlib
import itertools
import json
from pathlib import Path

B = Path('/tmp/oec/pequalnp-pilot-62')
def load(n): return json.loads((B/n).read_text())
def sha(n): return hashlib.sha256((B/n).read_bytes()).hexdigest()
def mask(xs): return sum(1 << i for i in xs)
def sub(a,b): return a & b == a
def move(q,a): return mask(a[i] for i in range(len(a)) if q >> i & 1)
lines = [mask(p for p in range(13) if (p-l)%13 in {0,1,3,9}) for l in range(13)]
pencils = [mask(l for l in range(13) if lines[l] >> p & 1) for p in range(13)]
rows = []
for s in range(8192):
    d = mask(l for l in range(13) if not s & lines[l])
    if all(s>>p&1 or d&pencils[p] for p in range(13)) and not any(sub(s,l) for l in lines) and not any(sub(d,p) for p in pencils):
        rows.append(s | (d << 13))
assert len(rows) == 468
points = [0,1,3]
vertices = points + [13+l for l in range(13) if any(lines[l] >> p & 1 for p in points)]
n = len(vertices); assert n == 13
positive = [mask([i,j]) for i,p in enumerate(points) for j,v in enumerate(vertices) if v >= 13 and lines[v-13] >> p & 1]
assert len(positive) == 12
truth = load('collinear3-full-truth.json'); sym = load('collinear3-full-first-or-symmetry.json')
assert vertices == truth['vertices'] == sym['vertices']
assert positive == truth['positive_edges'] == sym['positive_samples']
projected = [mask(i for i,v in enumerate(vertices) if q >> v & 1) for q in rows]
assert projected == truth['original_projected_negative_masks']
projected_set = set(projected)
maxima = sorted(q for q in projected_set if not any(q != r and sub(q,r) for r in projected_set))
assert len(projected_set) == 225 and len(maxima) == 81
assert maxima == truth['maximal_negative_masks'] == sym['negative_samples']
assert all(any(sub(q,r) for r in maxima) for q in projected)

global_positive = {mask([p,13+l]) for p in range(13) for l in range(13) if lines[l] >> p & 1}
group_data = load('global-first-or-symmetry.json')
generators = group_data['generators']
for a in generators:
    assert sorted(a) == list(range(26))
    assert {move(q,a) for q in global_positive} == global_positive
    assert {move(q,a) for q in rows} == set(rows)
identity = tuple(range(26)); group = {identity}; queue = [identity]
for p in queue:
    for a in generators:
        q = tuple(a[p[i]] for i in range(26))
        if q not in group: group.add(q); queue.append(q)
assert len(group) == 11232
index = {v:i for i,v in enumerate(vertices)}
actions = [[index[p[v]] for v in vertices] for p in sorted(group) if {p[v] for v in vertices} == set(vertices)]
assert actions == sym['vertex_actions'] and len(actions) == len(set(map(tuple,actions))) == 108
for a in actions:
    assert {move(q,a) for q in positive} == set(positive)
    assert {move(q,a) for q in maxima} == set(maxima)
inputs = [mask(j for j,q in enumerate(positive) if q >> i & 1) for i in range(n)]
initial = set()
for q in range(1,1 << n):
    s = (1 << 12)-1
    for i in range(n):
        if q >> i & 1: s &= inputs[i]
    if s: initial.add(s)
assert len(initial) == 16 and sorted(initial) == sym['initial_signature_masks']
pairs = {tuple(sorted((a,b))) for a,b in itertools.combinations(initial,2) if not sub(a,b) and not sub(b,a)}
assert len(pairs) == 105
edge_index = {q:i for i,q in enumerate(positive)}; seen = set()
for rec in sym['first_OR_orbits']:
    a,b = rec['representative_masks']; assert (a,b) in pairs
    orbit = set()
    for action in actions:
        perm = [edge_index[move(q,action)] for q in positive]
        trans = lambda q: mask(perm[i] for i in range(12) if q >> i & 1)
        orbit.add(tuple(sorted((trans(a),trans(b)))))
    assert len(orbit) == rec['size'] and not seen & orbit
    seen |= orbit
assert seen == pairs and len(sym['first_OR_orbits']) == 10
pos = {q for q in range(1 << n) if any(sub(p,q) for p in positive)}
neg = {q for q in range(1 << n) if any(sub(q,r) for r in maxima)}
assert not pos & neg and (len(pos),len(neg),(1<<n)-len(pos)-len(neg)) == (6951,395,846)
mins = [q for q in range(1 << n) if q not in neg and all(q^(1<<i) in neg for i in range(n) if q>>i&1)]
assert {d:sum(q.bit_count()==d for q in mins) for d in range(n+1)} == {int(k):v for k,v in load('collinear3-full-data-summary.json')['permitted_minterm_degree_counts'].items()}

source = (B/'cap4_separator_cnf.py').read_text()
replacements = [("choices=['global','cycle4','cycle5','theta4','cap4']","choices=['global','cycle4','cycle5','theta4','cap4','collinear3']"),
 ("if args.scenario in ('global','theta4','cap4'):","if args.scenario in ('global','theta4','cap4','collinear3'):"),
 ("'cap4':'cap4-full-first-or-symmetry.json'}", "'cap4':'cap4-full-first-or-symmetry.json','collinear3':'collinear3-full-first-or-symmetry.json'}")]
for a,b in replacements:
    assert source.count(a)==1; source=source.replace(a,b)
assert source == (B/'local_separator_cnf_v2.py').read_text()

def evaluate(w,q):
    bits = [bool(q >> i & 1) for i in range(w['input_count'])]
    assert len(w['operand_wire_lists']) == w['or_count']
    for a,b in w['operand_wire_lists']:
        assert all(type(i) is int and 0 <= i < len(bits) for i in a+b)
        bits.append(all(bits[i] for i in a) or all(bits[i] for i in b))
    out=w['output_wire_list']; assert all(type(i) is int and 0 <= i < len(bits) for i in out)
    return all(bits[i] for i in out)
local=load('collinear3-direct11-control.json'); global_control=load('collinear3-direct11-global51-control.json')
assert local['input_count']==13 and local['or_count']==11
for q in range(8192):
    v=evaluate(local,q)
    if q in pos: assert v
    if q in neg: assert not v
remaining=[(p,13+l) for p in range(13) for l in range(13) if lines[l]>>p&1 and not(p in vertices and 13+l in vertices)]
assert len(remaining)==40
ref=lambda i: vertices[i] if i<n else 26+i-n
ops=[[[ref(i) for i in branch] for branch in pair] for pair in local['operand_wire_lists']]
out=[ref(i) for i in local['output_wire_list']]
for p,l in remaining: ops.append([out,[p,l]]);out=[26+len(ops)-1]
assert global_control['operand_wire_lists']==ops and global_control['output_wire_list']==out and global_control['or_count']==51
for q in global_positive: assert evaluate(global_control,q)
for q in rows+[1<<i for i in range(26)]+[0]: assert not evaluate(global_control,q)
cnfs=[]
for stem,k in [('collinear3-separator10',10),('collinear3-separator11-control',11)]:
    m=load(stem+'.mapping.json');assert m['positive_samples']==positive and m['negative_samples']==maxima
    assert m['cover_prefix']==k-3 and len(m['cover_rows'])==81
    assert m['input_count']==13 and len(m['signature_variables'])==2*k
    assert m['false_OR_bounds']==[max(0,sum(not(q>>i&1) and any(sub(p,q|(1<<i)) for p in positive) for i in range(n))-1) for q in maxima]
    with (B/(stem+'.cnf')).open() as f:
        assert f.readline().split()==['p','cnf',str(m['variables']),str(m['clauses'])]
        count=0
        for line in f:
            lits=list(map(int,line.split()));assert lits[-1]==0 and all(0<abs(v)<=m['variables'] for v in lits[:-1]);count+=1
        assert count==m['clauses']
    cnfs.append({'stem':stem,'variables':m['variables'],'clauses':m['clauses'],'sha256':sha(stem+'.cnf')})
names=['collinear3_separator_data.py','collinear3-full-truth.json','collinear3-full-first-or-symmetry.json','local_separator_cnf_v2.py','embed_local_separator.py','collinear3-direct11-control.json','collinear3-direct11-global51-control.json']
report={'reviewer':'repo_audit','status':'PASS computational model and embedding audit; no solver or Lean run','scope':'13-input projected-row separator with12 incidence positives and81 maximal original-row projections, allowing22 cubic minterms. A10-OR witness embeds with40 joins to a50-OR global candidate; actual full replay and Lean certification still required.','checks':{'original_rows':len(rows),'local_projections':len(projected_set),'maximal_projections':len(maxima),'global_group':len(group),'local_actions':len(actions),'initial_signatures':len(initial),'incomparable_pairs':len(pairs),'complete_disjoint_orbits':len(sym['first_OR_orbits']),'local_control_assignments':8192,'global_control_samples':547,'adapter_exact_line_replacements':3},'cnfs':cnfs,'files':{n:sha(n) for n in names}}
(B/'collinear3-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
