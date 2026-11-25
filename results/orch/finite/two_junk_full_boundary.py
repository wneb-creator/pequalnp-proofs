from pathlib import Path
import json
import time

started = time.monotonic()
n = 6
mask = (1 << (1 << n)) - 1
inputs = [sum(1 << x for x in range(1 << n) if x & (1 << i)) for i in range(n)]
edges = [(0, 4), (0, 5), (1, 2), (1, 3)]
edge_indices = [(1 << a) | (1 << b) for a, b in edges]
target = (inputs[0] & (inputs[4] | inputs[5])) | (inputs[1] & (inputs[2] | inputs[3]))
P = inputs[0] | inputs[1]
Q = inputs[2] | inputs[3] | inputs[4] | inputs[5]
R = inputs[0] | inputs[2] | inputs[3]
S = inputs[1] | inputs[4] | inputs[5]
assert (P & Q) & (R & S) == target
initial_values = inputs + [P, inputs[2] | inputs[4], inputs[2] | inputs[3] | inputs[4], Q,
    inputs[0] | inputs[2], R, inputs[1] | inputs[4], S, 0, mask]
initial_names = ['a', 'b', 'c0', 'c1', 'd0', 'd1', 'P', 'c0|d0', 'c0|c1|d0', 'Q', 'a|c0', 'R', 'b|d0', 'S', 'false', 'true']
def edge_mask(value):
    return sum(1 << i for i, x in enumerate(edge_indices) if value & (1 << x))
star_ok = []
for chosen in range(1 << len(edges)):
    common = set(range(n))
    for i, edge in enumerate(edges):
        if chosen & (1 << i):
            common.intersection_update(edge)
    star_ok.append(chosen == 0 or bool(common))
count = [0, 0, 0, 0]
rejected = [0, 0, 0, 0]
solutions = []

def search(values, inherited, expressions, depth):
    if depth == 3:
        return
    for i in range(len(values)):
        for j in range(i, len(values)):
            ancestors = inherited[i] | inherited[j]
            for op in ('AND', 'OR'):
                val = values[i] & values[j] if op == 'AND' else values[i] | values[j]
                count[depth + 1] += 1
                own = edge_mask(val) & ~ancestors if op == 'AND' else 0
                if op == 'AND' and not star_ok[own]:
                    rejected[depth + 1] += 1
                    continue
                expr = [op, i, j, own]
                if val == target:
                    solutions.append(expressions + [expr])
                if depth < 2:
                    next_ancestors = ancestors | edge_mask(val) if op == 'AND' else ancestors
                    search(values + [val], inherited + [next_ancestors], expressions + [expr], depth + 1)

assert target not in initial_values
search(initial_values, [0] * len(initial_values), [], 0)
result = {
    'n': n,
    'edges': edges,
    'initial_wires': initial_names,
    'old_extension': [['AND', 6, 9], ['AND', 11, 13], ['AND', 16, 17]],
    'old_extension_equals_target_on_all_64_inputs': True,
    'free_constants_allowed': True,
    'commutative_gate_choices_with_repeated_inputs': True,
    'candidate_gate_count_by_depth': count,
    'nonstar_gate_rejections_by_depth': rejected,
    'star_profile_solutions_with_at_most_three_gates': solutions,
    'seconds': time.monotonic() - started,
}
print(json.dumps(result, indent=2))
Path('/tmp/oec/pequalnp-pilot-75/library/two-junk-full-boundary-result.json').write_text(json.dumps(result, indent=2) + '\n')
