"""Read-only audit of generated monotone gadget libraries; no solver calls."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

results = []
for filename in sys.argv[2:]:
    path = Path(filename)
    data = json.loads(path.read_text())
    graph = data['graph']
    n, edges = graph['n'], graph['edges']
    rows, nodes, recipes = data['rows'], data['nodes'], data['recipes']
    m = len(edges)
    assert len(nodes) == len(recipes)
    expected_positive = [(1 << a) | (1 << b) for a, b in edges]
    adjacency = [set() for _ in range(n)]
    for a, b in edges:
        adjacency[a].add(b)
        adjacency[b].add(a)
    expected_negative = []
    for s in range(1 << n):
        if any(s >> a & 1 and s >> b & 1 for a, b in edges):
            continue
        if all(s >> a & 1 or any(s >> b & 1 for b in adjacency[a]) for a in range(n)):
            expected_negative.append(s)
    assert rows == expected_positive + expected_negative
    mask = (1 << len(rows)) - 1
    positive = (1 << m) - 1
    negative = mask ^ positive
    for i in range(n):
        assert nodes[i]['kind'] == 'input' and nodes[i]['input'] == i
        assert not recipes[i]
        assert nodes[i]['value'] == sum(((s >> i) & 1) << r for r, s in enumerate(rows))
    backward = 0
    edges_union = [[] for _ in nodes]
    for k in range(n, len(nodes)):
        assert recipes[k]
        assert 0 <= nodes[k]['value'] <= mask
        for op, a, b in recipes[k]:
            assert op in ['and', 'or'] and 0 <= a < len(nodes) and 0 <= b < len(nodes)
            va, vb = nodes[a]['value'], nodes[b]['value']
            assert nodes[k]['value'] == (va & vb if op == 'and' else va | vb)
            clean = nodes[k]['kind'] in ['clean', 'guarded']
            if not clean:
                assert a < k and b < k
                assert nodes[a]['kind'] not in ['clean', 'guarded']
                assert nodes[b]['kind'] not in ['clean', 'guarded']
            if a >= k or b >= k:
                backward += 1
                assert clean
                assert nodes[a]['kind'] not in ['clean', 'guarded']
                assert nodes[b]['kind'] not in ['clean', 'guarded']
            edges_union[k].extend([a, b])
    # Stronger than checking any single selected recipe: the union is acyclic.
    colors = [0] * len(nodes)
    depth = [0] * len(nodes)
    def visit(k):
        assert colors[k] != 1, 'cycle in union of possible recipes'
        if colors[k] == 2:
            return depth[k]
        colors[k] = 1
        depth[k] = 0 if not edges_union[k] else 1 + max(visit(a) for a in edges_union[k])
        colors[k] = 2
        return depth[k]
    for k in range(len(nodes)):
        visit(k)
    for k in data['clean']:
        assert nodes[k]['value'] & positive
        assert not nodes[k]['value'] & negative
        assert k in data['active']
    active = set(data['active'])
    for k in active:
        for _, a, b in recipes[k]:
            assert a < n or a in active
            assert b < n or b in active
    result = dict(file=path.name, sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  n=n, edges=m, rows=len(rows), nodes=len(nodes),
                  recipes=sum(map(len, recipes)), active=len(active),
                  clean_outputs=len(data['clean']), node_kinds=dict(Counter(v['kind'] for v in nodes)),
                  backward_id_recipes=backward, maximum_union_depth=max(depth),
                  verdict='PASS: exact boundary values, closed dependencies, union of recipes acyclic')
    results.append(result)
    print(json.dumps(result, sort_keys=True))
Path(sys.argv[1]).write_text(json.dumps(results, indent=2) + '\n')
