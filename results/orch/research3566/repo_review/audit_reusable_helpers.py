"""Small independent controls for helper amplification; no search/solver runs."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

module_path, positive_path, output_path = map(Path, sys.argv[1:])
spec = importlib.util.spec_from_file_location('reviewed_helpers', module_path)
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)

for n in range(1, 9):
    actual = helpers.inputs(n)
    expected = tuple(sum(((x >> i) & 1) << x for x in range(1 << n)) for i in range(n))
    assert actual == expected

values, aliases, records, cones = helpers.normalize(3, [('or', 0, 1), ('or', 3, 2)], 4)
assert cones[3].bit_count() == 1 and cones[4].bit_count() == 2
assert (cones[3] | cones[4]).bit_count() == 2

positive = json.loads(positive_path.read_text())['witness']
n, N = 8, positive['n']
assert N == 10
base_edges = [e for e in positive['edges'] if all(v < n for v in e)]
def old_wire(w):
    return w if w < n else n + w - N
base_gates = [[op, old_wire(a), old_wire(b)] for op, a, b in positive['gates'][:-3]]
assert all(0 <= a < n + j and 0 <= b < n + j
           for j, (_, a, b) in enumerate(base_gates))
base_out = n + len(base_gates) - 1
values, aliases, records, cones = helpers.normalize(n, base_gates, base_out)
helper = {'wire': n, 'support': [0, 1]}
assert cones[aliases[base_out]].bit_count() == 11
assert (cones[aliases[base_out]] | cones[helper['wire']]).bit_count() == 12
extension = helpers.construct_extension(n, base_edges, base_gates, base_out, [helper])
assert extension['n'] == 10 and len(extension['gates']) == 15
assert {tuple(sorted(e)) for e in extension['edges']} == {
    tuple(sorted(e)) for e in positive['edges']}
for j, (_, a, b) in enumerate(extension['gates']):
    assert 0 <= a < N + j and 0 <= b < N + j
tau = N
for x in range(1 << N):
    wires = [bool(x >> i & 1) for i in range(N)]
    for op, a, b in extension['gates']:
        wires.append(wires[a] and wires[b] if op == 0 else wires[a] or wires[b])
    assert wires[extension['output']] == any(x >> a & 1 and x >> b & 1
                                            for a, b in extension['edges'])
    if all(x >> a & 1 or x >> b & 1 for a, b in extension['edges']):
        tau = min(tau, x.bit_count())
assert tau == 5
adj = [set() for _ in range(N)]
for a, b in extension['edges']:
    adj[a].add(b)
    adj[b].add(a)
assert all(len(adj[a] & adj[b]) <= 1 for a in range(N) for b in range(a))

# Each support separately admits a component flip, but the three together close
# an odd cycle across disconnected old edges. Joint coloring must reject it.
edges = [(0, 1), (2, 3), (4, 5)]
choices = [{'support': s} for s in [[0, 2], [3, 4], [5, 1]]]
assert all(helpers.color_graph(8, helpers.extended_edges(6, edges, [h])) is not None
           for h in choices)
assert helpers.color_graph(12, helpers.extended_edges(6, edges, choices)) is None

result = dict(verdict='PASS: independent bounded controls',
              source_sha256=hashlib.sha256(module_path.read_bytes()).hexdigest(),
              input_masks_checked_through_n=8, shared_cones_charged_once=True,
              old_output_cone_gates=11, helper_union_gates=12,
              extension_inputs=N, extension_edges=len(extension['edges']),
              extension_gates=len(extension['gates']), extension_cover=tau,
              exhaustive_extension_assignments=1 << N,
              joint_coloring_negative_control=True)
output_path.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
