import json
from pathlib import Path

n = 12
y = {0, 1, 2}
target = set(range(3, 11))
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
polluted = []
for a in sorted(y):
    f = a
    for t in sorted(target):
        f = add(f'F{a}_{t}', 'or', f, t)
    polluted.append(f)
f = add('F_ab', 'and', polluted[0], polluted[1])
f = add('F_abc', 'and', f, polluted[2])
l = add('L', 'and', z, f)
v = add('V', 'and', h, w)
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
heavy_target = []
refunds = []
family = [meeting, target]
for j, gate in enumerate(gates):
    wire = n + j
    a = {p for p in range(n) if singles[p][wire]}
    b = {p for p in range(n) if p not in y and heavies[p][wire]}
    meeting_charge = len(a) >= 2 and a <= meeting
    heavy_charge = not base[wire] and len(b) >= 2 and b <= target
    light_t_charge = len(a) >= 2 and a <= target
    refund = any(a == s for s in family) and b == target
    gate.update({'index': j, 'wire': wire, 'light_support': sorted(a),
                 'heavy_support': sorted(b), 'heavy_base': base[wire],
                 'meeting_charge': meeting_charge, 'heavy_charge': heavy_charge,
                 'light_target_charge': light_t_charge, 'refund': refund})
    if (light_t_charge or heavy_charge) and not meeting_charge:
        counted.append(gate['label'])
    if light_t_charge:
        light_target.append(gate['label'])
    if heavy_charge:
        heavy_target.append(gate['label'])
    if refund:
        refunds.append(gate['label'])
assert counted == ['F_ab', 'F_abc', 'L', 'V', 'O_T']
assert len(counted) < len(target) - 2
answer = {'all_assignments_pass': 1 << n, 'gate_count': len(gates),
          'y': sorted(y), 'target': sorted(target), 'meeting': sorted(meeting),
          'output_t': out_t, 'output_a': out_a,
          'selected_union_outside_meeting': counted,
          'light_target_charge': light_target, 'heavy_target_charge': heavy_target,
          'posted_refund_gates': refunds, 'gates': gates}
Path('/tmp/oec/pequalnp-pilot-13/status_review/union_switching_example.json').write_text(
    json.dumps(answer, indent=2))
print(json.dumps(answer, indent=2))
