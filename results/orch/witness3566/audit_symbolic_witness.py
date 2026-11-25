import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-178/gap3566/lean_setup')
sys.path.insert(0, str(BASE))
from make_witness import render
from make_symbolic_witness import symbolic_render

source = BASE / 'SymbolicLargeFast.lean'
s = source.read_text()
data = json.loads((BASE / 'symbolic-large-control.json').read_text())
plan = json.loads((BASE / 'symbolic-large-simp-plan.json').read_text())
base = json.loads((BASE / 'symbolic-base-control.json').read_text())
graph_source = s.split('abbrev witnessGraph', 1)[1].split('def witnessCircuit', 1)[0]
match = re.search(r'edgeGraph (\d+) \[(.*)\]', graph_source)
n = int(match.group(1))
edges = [list(map(int, pair)) for pair in re.findall(r'\((\d+), (\d+)\)', match.group(2))]
circuit_source = s.split('def witnessCircuit', 1)[1].split('def witnessExpr', 1)[0]
gates = [[op, int(a), int(b)] for op, a, b in
         re.findall(r'⟨\.(and|or), \[(\d+), (\d+)\]⟩', circuit_source)]
out = int(re.search(r'\], (\d+)⟩', circuit_source).group(1))
assert n == data['n'] == 31 and edges == data['edges'] and gates == data['gates']
assert len(gates) == data['size'] == 63 and out == data['output'] == 93
assert not re.search(r'\bsorry\b|\baxiom\b|\bnative_decide\b|\bbv_decide\b|_root_|"|@\[', s)
assert re.findall(r'^import (.+)$', s, re.M) == ['PEqualNP.Defs']
assert set(re.findall(r'set_option (\S+)', s)) <= {'maxRecDepth', 'maxHeartbeats'}
standard = render(data, 'simp').replace('def witnessExpr ', 'noncomputable def witnessExpr ')
standard = standard.replace('def witnessGraphExpr ', 'noncomputable def witnessGraphExpr ')
options = 'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 8000000 in\n'
assert s.split(options + 'theorem witness_cut_0', 1)[0] == standard.split(options + 'theorem witness_formula', 1)[0]
assert s.split(options + 'theorem witness_eval', 1)[1] == standard.split(options + 'theorem witness_eval', 1)[1]


def normalize(terms):
    result = []
    for term in sorted(set(terms), key=lambda t: (len(t), tuple(sorted(t)))):
        if not any(old <= term for old in result):
            result.append(term)
    assert len(result) < 10000
    return frozenset(result)


dnfs = [frozenset([frozenset([i])]) for i in range(n)]
for j, (op, a, b) in enumerate(gates):
    assert 0 <= a < n + j and 0 <= b < n + j
    terms = dnfs[a] | dnfs[b] if op == 'or' else [x | y for x in dnfs[a] for y in dnfs[b]]
    dnfs.append(normalize(terms))
assert dnfs[out] == frozenset(frozenset(e) for e in edges)
assert len(dnfs[out]) == len(edges) == 50
for cut in plan['cuts']:
    assert dnfs[cut['wire']] == frozenset(frozenset(e) for e in cut['edges'])
bg, bw = base['graph'], base['witness']
for assignment in range(1 << bg['n']):
    values = [bool(assignment >> i & 1) for i in range(bg['n'])]
    for op, a, b in bw['gates']:
        values.append(values[a] & values[b] if op == 'and' else values[a] | values[b])
    assert values[bw['output']] == any(values[a] and values[b] for a, b in bg['edges'])
    for helper in bw['observed_helpers']:
        assert values[helper['wire']] == any(values[i] for i in helper['support'])
adj = [set() for _ in range(n)]
for a, b in edges:
    assert 0 <= a < n and 0 <= b < n and a != b
    adj[a].add(b)
    adj[b].add(a)
assert all(len(adj[a] & adj[b]) <= 1 for a in range(n) for b in range(a))
colors = {}
for seed in range(n):
    if seed in colors:
        continue
    colors[seed] = 0
    queue = [seed]
    for a in queue:
        for b in adj[a]:
            if b not in colors:
                colors[b] = 1 - colors[a]
                queue.append(b)
            assert colors[b] != colors[a]
centers = set(range(15, 31, 2))
cover = set(range(6)) | centers
matching = [tuple(e) for e in bg['matching']] + [(c, c + 1) for c in centers]
edge_set = {frozenset(e) for e in edges}
assert len(cover) == len(matching) == 14
assert all(a in cover or b in cover for a, b in edges)
assert all(frozenset(e) in edge_set for e in matching)
assert len({v for e in matching for v in e}) == 28
log = (BASE / 'symbolic-large-fast-build.log').read_text()
assert 'RESULT exit=0 elapsed_seconds=16.136 max_rss_kib=3095680' in log
assert not re.search(r'\berror:', log)
result = {'verdict': 'PASS: checked upper control, not a counterexample',
          'n': n, 'gates': len(gates), 'edges': len(edges), 'output': out,
          'minimum_cover': len(cover), 'standard_upper': len(edges) + len(cover) - 1,
          'symbolic_minimal_monomials': len(dnfs[out]), 'base_truth_rows': 1 << bg['n'],
          'exact_lean_json_match': True, 'unchanged_circuit_and_graph_bridges': True,
          'generator_byte_reproduction': symbolic_render(data, plan) == s,
          'source_lines': len(s.splitlines()), 'source_bytes': source.stat().st_size,
          'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'generator_sha256': hashlib.sha256((BASE / 'make_symbolic_witness.py').read_bytes()).hexdigest(),
          'amplifier_sha256': hashlib.sha256((BASE / 'amplify_symbolic.py').read_bytes()).hexdigest(),
          'build_warning_count': log.count('warning:'), 'elapsed_seconds': 16.136,
          'max_rss_kib': 3095680}
print(json.dumps(result, indent=2))
