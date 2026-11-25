from collections import Counter
from pathlib import Path
import json
import sys

path = Path(sys.argv[1])
signals = {}
header = None
with path.open() as stream:
    for line in stream:
        x = json.loads(line)
        if x['event'] == 'signal':
            signals[x['id']] = int(x['hex'], 16)
        elif x['event'] == 'header':
            header = x
assert header and header['mode'] == 1 and header['cap'] == 18
assert header['first'] == 'andedge'
full = (1 << 1024) - 1
inputs = [sum(1 << r for r in range(1024) if (r >> i) & 1) for i in range(10)]
edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
         (5,7),(7,9),(9,6),(6,8),(8,5)]
target = 0
for a, b in edges:
    target |= inputs[a] & inputs[b]
assert signals[header['target']] == target
assert all(signals[i + 1] == value for i, value in enumerate(inputs))
stack = []
completed = {}
counts = Counter()
depths = Counter()
open_nodes = []
root_children = Counter()
nodes = 0
with path.open() as stream:
    for line in stream:
        x = json.loads(line)
        if x['event'] == 'node':
            nodes += 1
            assert x['id'] == nodes
            d, a, b, z, keep = x['step']
            assert d in range(4) and keep in range(4)
            aa, bb = signals[a], signals[b]
            expected_value = [aa & bb, aa | bb, aa & (full ^ bb), (full ^ aa) & bb][d]
            assert signals[z] == expected_value
            assert x['state'] == sorted(set(x['state']))
            if stack:
                parent = stack[-1]
                assert x['parent'] == parent['id']
                assert x['remaining'] == parent['remaining'] - 1
                assert a != b and a in parent['state'] and b in parent['state']
                assert z not in parent['state']
                expected = [v for v in parent['state']
                            if (v != a or keep & 1) and (v != b or keep & 2)] + [z]
                assert x['state'] == sorted(expected)
            else:
                assert x['id'] == 1 and x['parent'] == 0 and x['remaining'] == 17
                assert (d, a, b, keep) == (0, 1, 2, 3)
                assert x['state'] == sorted(list(range(1, 11)) + [z])
            depths[18 - x['remaining']] += 1
            stack.append(x)
        elif x['event'] == 'done':
            node = stack.pop()
            assert x['id'] == node['id']
            kind = x['kind']
            counts[kind] += 1
            if kind == 'row':
                p, n = x['a'], x['b']
                assert (target >> p) & 1 and not ((target >> n) & 1)
                assert all(((signals[v] >> p) & 1) == ((signals[v] >> n) & 1)
                           for v in node['state'])
            elif kind == 'memo':
                assert x['a'] in completed
                prior = completed[x['a']]
                assert prior[0] == node['remaining'] and prior[1] != 'open'
            if kind == 'open':
                open_nodes.append({'id': node['id'], 'remaining': node['remaining'],
                                   'roots': len(node['state'])})
            completed[node['id']] = (node['remaining'], kind)
            if node['parent'] == 1:
                root_children[kind] += 1
assert not stack and len(completed) == nodes
print(json.dumps({'header': header, 'nodes': nodes, 'signals': len(signals),
                  'terminal_kinds': dict(counts), 'depths': dict(depths),
                  'root_status': completed[1][1], 'open_nodes': open_nodes,
                  'visited_root_children': dict(root_children),
                  'all_transitions_and_signed_row_witnesses_checked': True,
                  'memo_remaining_budgets_match': True,
                  'not_rechecked': ['cofactor lower bounds and supply certificates',
                                    'formula closure exclusions', 'memo automorphism witnesses',
                                    'complete successor coverage'],
                  'verdict': 'Bounded computational evidence only; no UNSAT or Lean theorem.'}, indent=2))
