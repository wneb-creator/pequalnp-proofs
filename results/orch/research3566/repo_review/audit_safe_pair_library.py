import hashlib
import itertools
import json
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-178/gap3566/certificate_search')
path = BASE / 'subk33-pair-library.json'
raw = path.read_bytes()
d = json.loads(raw)
n = d['graph']['n']
edges = [tuple(e) for e in d['graph']['edges']]
rows, nodes, recipes = d['rows'], d['nodes'], d['recipes']
assert len(nodes) == len(recipes)
assert rows[:len(edges)] == [(1 << a) | (1 << b) for a, b in edges]
assert len(rows) == len(set(rows))
row_index = {s: i for i, s in enumerate(rows)}
adj = [set() for _ in range(n)]
for a, b in edges:
    adj[a].add(b)
    adj[b].add(a)


def independent(s):
    return not any((s >> a) & 1 and (s >> b) & 1 for a, b in edges)


def maximal(s, allowed):
    return independent(s) and all(not ((allowed >> i) & 1) or ((s >> i) & 1)
                                  or any((s >> j) & 1 for j in adj[i]) for i in range(n))


all_inputs = (1 << n) - 1
mis = [s for s in range(1 << n) if maximal(s, all_inputs)]
assert set(mis) <= row_index.keys()
assert all(1 << i in row_index for i in range(n))
assert all(independent(s) for s in rows[len(edges):])
for i in range(n):
    assert nodes[i]['value'] == sum(((s >> i) & 1) << r for r, s in enumerate(rows))
assert len({z['value'] for z in nodes}) == len(nodes)
deps = [set() for _ in nodes]
for k, rr in enumerate(recipes):
    for op, a, b in rr:
        assert op in ('and', 'or') and 0 <= a < len(nodes) and 0 <= b < len(nodes)
        va, vb = nodes[a]['value'], nodes[b]['value']
        assert nodes[k]['value'] == (va & vb if op == 'and' else va | vb)
        deps[k].update((a, b))
marks = [0] * len(nodes)
depth = [0] * len(nodes)


def visit(k):
    assert marks[k] != 1, ('cycle', k)
    if marks[k] == 2:
        return depth[k]
    marks[k] = 1
    depth[k] = 1 + max((visit(j) for j in deps[k]), default=-1)
    marks[k] = 2
    return depth[k]


for k in range(len(nodes)):
    visit(k)
pos = (1 << len(edges)) - 1
assert all(nodes[k]['value'] & ~pos == 0 and recipes[k] for k in d['clean'])
active = set(d['active'])
assert all(j < n or j in active for k in active for j in deps[k])
groups = list(map(set, json.loads((BASE / 'subk33-safe-pair-supports.json').read_text())))
assert len(groups) == 24 and all(len(S) == 2 for S in groups)
assert all(len(A & B) <= 1 for A, B in itertools.combinations(groups, 2))
counts, candidate_sets, induced_counts = [], [], []
for S in groups:
    assert (S <= set(range(6)) or S <= set(range(6, 15)))
    assert all(len(S & a) <= 1 for a in adj)
    allowed = all_inputs ^ sum(1 << i for i in S)
    induced = [s for s in range(1 << n) if s & ~allowed == 0 and maximal(s, allowed)]
    assert set(induced) <= row_index.keys()
    induced_counts.append(len(induced))
    required = sum(1 << row_index[1 << i] for i in S)
    reject = sum(1 << r for r, s in enumerate(rows) if s & ~allowed == 0 and independent(s))
    candidates = [k for k, z in enumerate(nodes)
                  if k >= n and z['value'] & required == required and not z['value'] & reject]
    assert candidates
    for k in candidates:
        singleton_support = {i for i in range(n) if nodes[k]['value'] >> row_index[1 << i] & 1}
        assert singleton_support == S
    candidate_sets.append(set(candidates))
    counts.append(len(candidates))
assert all(not A & B for A, B in itertools.combinations(candidate_sets, 2))
controls = []
for name in ('p5-relaxed-control.json', 'p5-absorbed-control.json'):
    control = json.loads((BASE / name).read_text())
    graph, witness = control['graph'], control['witness']
    cn = graph['n']
    for s in range(1 << cn):
        vals = [bool(s >> i & 1) for i in range(cn)]
        for i, (op, a, b) in enumerate(witness['gates']):
            assert op in ('and', 'or') and 0 <= a < cn + i and 0 <= b < cn + i
            vals.append(vals[a] & vals[b] if op == 'and' else vals[a] | vals[b])
        F = any(vals[a] and vals[b] for a, b in graph['edges'])
        assert vals[witness['output']] == F
        for helper in witness['observed_helpers']:
            literal = any(vals[i] for i in helper['support'])
            actual = vals[helper['wire']]
            assert (not literal or actual) and (not actual or literal or F)
    assert witness['size'] == len(witness['gates']) <= control['budget'] - 1
    assert witness['paid_size'] == witness['size'] - control['helper_overhead']
    controls.append({'name': name, 'assignments': 1 << cn,
                     'raw': witness['size'], 'paid': witness['paid_size']})
print(json.dumps({'library_sha256': hashlib.sha256(raw).hexdigest(),
                  'nodes': len(nodes), 'recipes': sum(map(len, recipes)),
                  'rows': len(rows), 'global_maximal_independent_rows': len(mis),
                  'initial_active': len(active), 'union_dag_max_depth': max(depth),
                  'induced_maximal_independent_counts': induced_counts,
                  'candidate_counts': counts, 'candidate_count': sum(counts),
                  'candidate_sets_disjoint': True,
                  'controls': controls,
                  'source_hashes': {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest()
                                    for name in ('gadget_helper_library.py',
                                                 'gadget_absorbed_library.py', 'gadget_relaxed_sat.py')}}, indent=2))
