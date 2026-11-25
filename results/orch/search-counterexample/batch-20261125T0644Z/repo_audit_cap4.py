import hashlib
import itertools
import json
from pathlib import Path

B = Path('/tmp/oec/pequalnp-pilot-62')
def load(name):
    return json.loads((B / name).read_text())
def sha(name):
    return hashlib.sha256((B / name).read_bytes()).hexdigest()
def mask(items):
    return sum(1 << i for i in items)
def subset(a, b):
    return a & b == a

line_points = [mask(p for p in range(13) if (p-l) % 13 in {0,1,3,9}) for l in range(13)]
pencils = [mask(l for l in range(13) if line_points[l] >> p & 1) for p in range(13)]
rows = []
for s in range(8192):
    d = mask(l for l in range(13) if not (s & line_points[l]))
    maximal = all(s >> p & 1 or (d & pencils[p]) for p in range(13))
    if maximal and not any(subset(s, l) for l in line_points) and not any(subset(d, p) for p in pencils):
        rows.append(s | (d << 13))
assert len(rows) == 468
g = load('geometry-data.json')
assert rows == [r['S'] | (r['D'] << 13) for r in g['generic']]

truth = load('cap4-full-truth.json')
sym = load('cap4-full-first-or-symmetry.json')
summary = load('cap4-full-data-summary.json')
points = [0,1,2,5]
vertices = points + [13+l for l in range(13) if any(line_points[l] >> p & 1 for p in points)]
assert len(vertices) == 14 and truth['vertices'] == sym['vertices'] == vertices
positive = [mask([i,j]) for i,p in enumerate(points) for j,v in enumerate(vertices)
            if v >= 13 and line_points[v-13] >> p & 1]
assert len(positive) == 16 and positive == truth['positive_edges'] == sym['positive_samples']
projected = [mask(i for i,v in enumerate(vertices) if q >> v & 1) for q in rows]
assert projected == truth['original_projected_negative_masks']
negset = set(projected)
maxima = sorted(q for q in negset if not any(q != r and subset(q,r) for r in negset))
assert len(negset) == 222 and len(maxima) == 83
assert maxima == truth['maximal_negative_masks'] == sym['negative_samples']
assert all(any(subset(q,r) for r in maxima) for q in projected)

actions = sym['vertex_actions']
assert len(actions) == len(set(map(tuple, actions))) == 24
assert {tuple(a[:4]) for a in actions} == set(itertools.permutations(range(4)))
def move(q, a):
    return mask(a[i] for i in range(14) if q >> i & 1)
for a in actions:
    assert sorted(a) == list(range(14))
    assert {move(q,a) for q in positive} == set(positive)
    assert {move(q,a) for q in maxima} == set(maxima)
input_sigs = [mask(j for j,q in enumerate(positive) if q >> i & 1) for i in range(14)]
initial = set()
for q in range(1, 1 << 14):
    sig = (1 << 16)-1
    for i in range(14):
        if q >> i & 1:
            sig &= input_sigs[i]
    if sig:
        initial.add(sig)
assert len(initial) == 26 and sorted(initial) == sym['initial_signature_masks']
pairs = {tuple(sorted((a,b))) for a,b in itertools.combinations(initial,2)
         if not subset(a,b) and not subset(b,a)}
assert len(pairs) == 297
positive_index = {q:i for i,q in enumerate(positive)}
seen = set()
for rec in sym['first_OR_orbits']:
    a,b = rec['representative_masks']
    assert (a,b) in pairs
    orbit = set()
    for action in actions:
        perm = [positive_index[move(q,action)] for q in positive]
        transform = lambda v: mask(perm[i] for i in range(16) if v >> i & 1)
        orbit.add(tuple(sorted((transform(a),transform(b)))))
    assert len(orbit) == rec['size'] and not (seen & orbit)
    seen |= orbit
assert seen == pairs and len(sym['first_OR_orbits']) == 22

forced_true = {q for q in range(1 << 14) if any(subset(p,q) for p in positive)}
forced_false = {q for q in range(1 << 14) if any(subset(q,r) for r in maxima)}
assert not (forced_true & forced_false)
mins = [q for q in range(1 << 14) if q not in forced_false and
        all((q ^ (1 << i)) in forced_false for i in range(14) if q >> i & 1)]
assert {d:sum(q.bit_count() == d for q in mins) for d in range(15)} == {int(k):v for k,v in summary['permitted_minterm_degree_counts'].items()}
assert (len(forced_true),len(forced_false),(1<<14)-len(forced_true)-len(forced_false)) == (15047,459,878)

old = (B/'global_or_direct_cnf_v4.py').read_text()
assert sha('global_or_direct_cnf_v4.py') == 'b7fddb4d805d73e563d3f35af0fdeae503f660b94c1d07a44815d93ca88dff20'
replacements = [
    ("choices=['global','cycle4','cycle5','theta4']", "choices=['global','cycle4','cycle5','theta4','cap4']"),
    ("if args.scenario in ('global','theta4'):", "if args.scenario in ('global','theta4','cap4'):"),
    ("name = 'global-first-or-symmetry.json' if args.scenario == 'global' else 'theta4-first-or-symmetry.json'", "name = {'global':'global-first-or-symmetry.json','theta4':'theta4-first-or-symmetry.json','cap4':'cap4-full-first-or-symmetry.json'}[args.scenario]"),
    ("nv = 26 if args.scenario == 'global' else 10", "nv = data['input_count'] if 'input_count' in data else 26"),
]
for a,b in replacements:
    assert old.count(a) == 1
    old = old.replace(a,b)
assert old == (B/'cap4_separator_cnf.py').read_text()

def eval_program(w,q):
    n = w['input_count']; ops = w['operand_wire_lists']; out = w['output_wire_list']
    assert len(ops) == w['or_count']
    bits = [bool(q >> i & 1) for i in range(n)]
    for a,b in ops:
        assert all(type(i) is int and 0 <= i < len(bits) for i in a+b)
        bits.append(all(bits[i] for i in a) or all(bits[i] for i in b))
    assert all(type(i) is int and 0 <= i < len(bits) for i in out)
    return all(bits[i] for i in out)
local = load('cap4-direct15-control.json')
assert local['input_count'] == 14 and local['or_count'] == 15
for q in range(1 << 14):
    value = eval_program(local,q)
    if q in forced_true: assert value
    if q in forced_false: assert not value
global_control = load('cap4-direct15-global51-control.json')
assert global_control['input_count'] == 26 and global_control['or_count'] == 51
remaining = [(p,13+l) for p in range(13) for l in range(13)
             if line_points[l] >> p & 1 and not (p in vertices and 13+l in vertices)]
assert len(remaining) == 36
ref = lambda i: vertices[i] if i < 14 else 26+i-14
expected_ops = [[[ref(i) for i in branch] for branch in pair] for pair in local['operand_wire_lists']]
expected_out = [ref(i) for i in local['output_wire_list']]
for p,l in remaining:
    expected_ops.append([expected_out,[p,l]])
    expected_out = [26+len(expected_ops)-1]
assert global_control['operand_wire_lists'] == expected_ops and global_control['output_wire_list'] == expected_out
global_positive = [mask([p,13+l]) for p in range(13) for l in range(13) if line_points[l] >> p & 1]
for q in global_positive: assert eval_program(global_control,q)
for q in rows + [1 << i for i in range(26)] + [0]: assert not eval_program(global_control,q)

cnf_stats = []
for stem,k in [('cap4-separator14',14),('cap4-separator15-control',15)]:
    m = load(stem+'.mapping.json')
    assert m['positive_samples'] == positive and m['negative_samples'] == maxima
    assert m['cover_prefix'] == k-3 and len(m['cover_rows']) == 83
    assert m['input_count'] == 14 and len(m['signature_variables']) == 2*k
    assert m['false_OR_bounds'] == [max(0,sum(not(q>>i&1) and any(subset(p,q|(1<<i)) for p in positive) for i in range(14))-1) for q in maxima]
    with (B/(stem+'.cnf')).open() as f:
        header = f.readline().split(); assert header == ['p','cnf',str(m['variables']),str(m['clauses'])]
        count = 0
        for line in f:
            lits = list(map(int,line.split())); assert lits and lits[-1] == 0
            assert all(0 < abs(v) <= m['variables'] for v in lits[:-1]); count += 1
        assert count == m['clauses']
    cnf_stats.append({'stem':stem,'variables':m['variables'],'clauses':m['clauses'],'sha256':sha(stem+'.cnf')})

names = ['cap4_full_data.py','cap4-full-truth.json','cap4-full-first-or-symmetry.json','cap4-full-data-summary.json','cap4_separator_cnf.py','embed_cap4_separator.py','cap4-direct15-control.json','cap4-direct15-global51-control.json']
report = {'reviewer':'repo_audit','status':'PASS computational model and embedding audit; no solver or Lean run',
 'scope':'Projected-row separator with16 forced incidence positives and83 maximal projections of all468 original negatives;22 cubic minterms allowed. A14-OR witness embeds with36 joins to a50-OR global candidate; any candidate still needs full independent replay and Lean checking.',
 'checks':{'global_rows_independently_regenerated':len(rows),'distinct_local_projections':len(negset),'negative_maxima':len(maxima),'all_vertex_actions':len(actions),'incomparable_initial_pairs':len(pairs),'disjoint_complete_orbits':len(sym['first_OR_orbits']),'local_control_assignments':1<<14,'global_control_samples':len(global_positive)+len(rows)+27,'adapter_exact_line_replacements':4},
 'cnfs':cnf_stats,'files':{n:sha(n) for n in names},
 'embedding_argument':'Local output rejects every global row projection by monotonicity below83 maxima. Add each of36 missing global edge conjunctions by one OR. Each added term is false on every generic negative and accepts its missing positive; local16 positives are retained. Backward references and gate count k+36 are preserved.'}
(B/'cap4-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
