import json
from pathlib import Path

n = 10
y, a_set, t_set = {0, 1, 2}, {2, 3, 4}, {5, 6, 7, 8, 9}
gates = []

def add(label, op, a, b=None):
    gates.append({'label': label, 'op': op, 'inputs': [a] if b is None else [a,b]})
    return n+len(gates)-1

h = add('ab', 'and', 0, 1)
h = add('H', 'and', h, 2)
z = add('z', 'not', h)
fs = []
for u,t in [(3,5),(4,6)]:
    left = add(f'z_u{u}', 'and', z, u)
    right = add(f'c_t{t}', 'and', 2, t)
    fs.append(add(f'f{u}', 'or', left, right))
w = add('overlap', 'or', fs[0], fs[1])
out_a = add('out_A', 'or', 2, w)
out_t = 5
for t in [6,7,8,9]:
    out_t = add(f'out_T_{t}', 'or', out_t, t)

def run(x):
    values = [p in x for p in range(n)]
    for gate in gates:
        ins = [values[i] for i in gate['inputs']]
        values.append(not ins[0] if gate['op']=='not' else all(ins) if gate['op']=='and' else any(ins))
    return values

for mask in range(1<<n):
    x = {p for p in range(n) if mask & (1<<p)}
    values = run(x)
    assert values[out_a] == bool(x & a_set)
    assert values[out_t] == bool(x & t_set)
    assert not values[w] or bool(x & a_set)
    if y <= x:
        assert not values[w] or bool(x & t_set)
    if len(x)<3:
        assert values[z]
assert not run(y)[z]
light = lambda wire: {p for p in range(n) if run({p})[wire]}
heavy = lambda wire: {p for p in range(n) if p not in y and run(y|{p})[wire]}
assert light(w) == {3,4} and heavy(w)=={5,6}
assert all(light(f) < light(w) and heavy(f) < heavy(w) for f in fs)
assert light(w) != a_set and light(w) != t_set
assert not run(set(range(n))-a_set)[w]
assert not run(set(range(n))-t_set)[w]
answer = {'n':n, 'Y':sorted(y), 'A':sorted(a_set), 'T':sorted(t_set),
          'all_inputs_checked':1<<n, 'gates':gates, 'overlap_wire':w,
          'overlap_singleton_support':sorted(light(w)), 'overlap_heavy_support':sorted(heavy(w)),
          'children_singleton_supports':[sorted(light(f)) for f in fs],
          'children_heavy_supports':[sorted(heavy(f)) for f in fs],
          'global_A_sound':True, 'heavy_T_sound':True,
          'not_refunded':True, 'output_A':out_a, 'output_T':out_t}
Path('/tmp/oec/pequalnp-pilot-13/status_review/refined_overlap_example.json').write_text(json.dumps(answer,indent=2))
print(json.dumps(answer,indent=2))
