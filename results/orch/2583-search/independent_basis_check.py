import json
from pathlib import Path

base = Path(__file__).resolve().parent
d = json.loads((base / 'plane3.json').read_text())
n = 13
edges = set(map(tuple, d['edges']))
assert len(edges) == 52
assert all(0 <= p < n and n <= l < 2*n for p,l in edges)
assert all(sum((p,l+n) in edges for p in range(n)) == 4 for l in range(n))
assert all(sum((p,l+n) in edges for l in range(n)) == 4 for p in range(n))
assert all(sum((p,l+n) in edges and (q,l+n) in edges for l in range(n)) == 1
           for p in range(n) for q in range(p+1,n))
true_rows = {(1 << p) | (1 << l) for p,l in edges}
assert true_rows == set(d['minimal_true']) and len(d['minimal_true']) == 52
max_false = set()
for s in range(1 << n):
    b = sum(1 << l for l in range(n)
            if not any((s >> p)&1 and (p,l+n) in edges for p in range(n)))
    closure = sum(1 << p for p in range(n)
                  if not any((b >> l)&1 and (p,l+n) in edges for l in range(n)))
    assert s & closure == s
    assert all(not ((closure >> p)&1 and (b >> (l-n))&1) for p,l in edges)
    max_false.add(closure | (b << n))
assert max_false == set(d['maximal_false']) and len(d['maximal_false']) == 704
for z in max_false:
    assert not any((z >> p)&1 and (z >> l)&1 for p,l in edges)
    for i in range(2*n):
        if not ((z >> i)&1):
            zz = z | (1 << i)
            assert any((zz >> p)&1 and (zz >> l)&1 for p,l in edges)

def evaluate(candidate, z):
    vals = [bool((z >> i)&1) for i in range(2*n)]
    for g in candidate['gates']:
        assert g['op'] in ('and','or')
        assert 0 <= g['a'] < len(vals) and 0 <= g['b'] < len(vals)
        vals.append(vals[g['a']] and vals[g['b']] if g['op']=='and'
                    else vals[g['a']] or vals[g['b']])
    return vals[candidate['output']]
assert all(evaluate(d,z) for z in true_rows)
assert all(not evaluate(d,z) for z in max_false)
print('PASS: q=3 plane axioms, 52 edges, all 8192 point subsets checked.')
print('PASS: 704 maximal false rows form a complete false boundary by Galois closure.')
print('PASS: 64-gate AO2 control evaluates correctly on all 756 boundary rows.')
print('For any monotone candidate, agreement on these minimal true and maximal false rows implies agreement on all inputs.')
print('This Python check is independent search validation, not a Lean certificate or circuit lower bound.')
