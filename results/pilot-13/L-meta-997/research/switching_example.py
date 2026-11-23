import json
from pathlib import Path

n = 8
y = {0, 1, 2}
target = {3, 4, 5, 6, 7}
meeting = {0, 1, 3}
gates = []


def add(label, op, a, b=None):
    gates.append({'label': label, 'op': op, 'inputs': [a] if b is None else [a, b]})
    return n + len(gates) - 1


ab = add('ab', 'and', 0, 1)
h = add('H', 'and', ab, 2)
z = add('z', 'not', h)
p = add('P', 'or', 0, 1)
w = add('zP', 'and', z, p)
for t in sorted(target):
    q = add(f'c_t{t}', 'and', 2, t)
    w = add(f'W{t}', 'or', w, q)
terms = [add(f'z_t{t}', 'and', z, t) for t in sorted(target)]
l = terms[0]
for j, term in enumerate(terms[1:], start=1):
    l = add(f'L{j}', 'or', l, term)
g = add('G', 'or', h, l)
v = add('V', 'and', w, g)
out_t = add('O_T', 'or', v, l)
out_a = add('O_A', 'or', p, 3)


def run(x):
    values = [i in x for i in range(n)]
    for gate in gates:
        args = [values[j] for j in gate['inputs']]
        if gate['op'] == 'and':
            values.append(all(args))
        elif gate['op'] == 'or':
            values.append(any(args))
        else:
            values.append(not args[0])
    return values


for mask in range(1 << n):
    x = {p for p in range(n) if mask & (1 << p)}
    values = run(x)
    assert values[out_t] == bool(x & target)
    assert values[out_a] == bool(x & meeting)
    assert len(x) >= len(y) or values[z]
assert not run(y)[z]
assert len(target & meeting) <= 1

base = run(y)
singles = [run({p}) for p in range(n)]
heavies = [run(y | {p}) for p in range(n)]
counted = []
light_target = []
for j, gate in enumerate(gates):
    wire = n + j
    a = {p for p in range(n) if singles[p][wire]}
    b = {p for p in range(n) if p not in y and heavies[p][wire]}
    meeting_charge = len(a) >= 2 and a <= meeting
    heavy_charge = not base[wire] and len(b) >= 2 and b <= target
    light_t_charge = len(a) >= 2 and a <= target
    gate.update({'index': j, 'wire': wire, 'light_support': sorted(a),
                 'heavy_support': sorted(b), 'heavy_base': base[wire],
                 'meeting_charge': meeting_charge, 'heavy_charge': heavy_charge,
                 'light_target_charge': light_t_charge})
    if heavy_charge and not meeting_charge:
        counted.append(gate['label'])
    if light_t_charge:
        light_target.append(gate['label'])
assert counted == ['V', 'O_T']
answer = {'all_256_assignments_pass': True, 'gate_count': len(gates),
          'y': sorted(y), 'target': sorted(target), 'meeting': sorted(meeting),
          'output_t': out_t, 'output_a': out_a,
          'selected_heavy_outside_meeting': counted,
          'light_target_charge': light_target, 'gates': gates}
Path('/tmp/oec/pequalnp-pilot-13/status_review/switching_example.json').write_text(
    json.dumps(answer, indent=2))
print(json.dumps(answer, indent=2))
