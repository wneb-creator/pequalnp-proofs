import itertools
import json
from pathlib import Path

out = Path(__file__).resolve().parent
n = 4
inputs = [sum(1 << mask for mask in range(16) if mask >> i & 1) for i in range(n)]
truth = (1 << 16) - 1
edges = [(0, 1), (1, 2), (2, 3)]
edge_rows = [(1 << a) | (1 << b) for a, b in edges]
target = (inputs[0] & inputs[1]) | (inputs[1] & inputs[2]) | (inputs[2] & inputs[3])
prefix = [('or', (0, 2)), ('or', (1, 3)), ('or', (1, 2))]

def evaluation(gates):
    values = inputs[:]
    cones = []
    for j, (op, refs) in enumerate(gates):
        value = truth if op == 'and' else 0
        cone = set()
        for ref in refs:
            operand = values[ref] if ref < len(values) else 0
            value = value & operand if op == 'and' else value | operand
            if n <= ref < n + j:
                cone.add(ref - n)
                cone |= cones[ref - n]
        values.append(value)
        cones.append(cone)
    return values, cones

def star_profile(gates, values, cones):
    owners = []
    for j, (op, _) in enumerate(gates):
        if op != 'and':
            owners.append([])
            continue
        owned = [e for e, row in enumerate(edge_rows) if values[n + j] >> row & 1
                 and all(gates[i][0] != 'and' or not (values[n + i] >> row & 1) for i in cones[j])]
        owners.append(owned)
        if owned and not any(all(v in edges[e] for e in owned) for v in range(n)):
            return False, owners
    return True, owners

def choices(wires):
    refs = list(range(wires)) + [1000]
    lists = [()] + [(i,) for i in refs] + list(itertools.combinations_with_replacement(refs, 2))
    return [(op, refs) for op in ['and', 'or'] for refs in lists]

matches = []
total = 0
for first in choices(7):
    for second in choices(8):
        total += 1
        gates = prefix + [first, second]
        values, cones = evaluation(gates)
        if values[-1] != target:
            continue
        star, owners = star_profile(gates, values, cones)
        assert not star
        matches.append({'extension': [first, second], 'owned_edge_indices': owners})
assert matches

generic_checks = 0
for a, b, A, B in itertools.product([False, True], repeat=4):
    if (not a or A) and (not b or B):
        assert ((A and B) and (a or b)) == ((a and B) or (b and A))
        generic_checks += 1

original = [('or', (0, 2)), ('or', (1, 3)), ('and', (4, 5)),
            ('or', (1, 2)), ('and', (6, 7))]
replacement = [('or', (0, 2)), ('or', (1, 3)), ('and', (1, 4)),
               ('and', (2, 5)), ('or', (6, 7))]
old_values, old_cones = evaluation(original)
new_values, new_cones = evaluation(replacement)
assert old_values[-1] == new_values[-1] == target
assert old_values[:6] == new_values[:6]
assert not star_profile(original, old_values, old_cones)[0]
assert star_profile(replacement, new_values, new_cones)[0]
report = {
    'status': 'PASS Python exhaustive checks only; no Lean claim',
    'generic_absorption_identity_cases': generic_checks,
    'same_size_private_product_and_cleanup_repair': {
        'old': original, 'new': replacement, 'gate_count_each': 5,
        'preserved_shared_wires': ['a', 'b', 'c', 'd', 'a OR c', 'b OR d'],
        'old_star_profile': False, 'new_star_profile': True,
    },
    'fixed_three_OR_interface_obstruction': {
        'prefix': prefix, 'extension_candidates': total,
        'truth_correct_two_gate_extensions': len(matches),
        'star_profile_two_gate_extensions': 0,
        'all_truth_correct_extensions': matches,
        'coverage': 'Every pair of AND/OR gates with fanin0,1,2; repeated operands; earlier wires or a canonical invalid false reference; operand order quotiented by commutativity.',
        'scope': 'The three existing OR wires must remain fixed. This disproves only a local two-gate star repair at that interface, not a whole-circuit or minimum-circuit theorem.',
    },
}
(out / 'private-exchange-audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
