import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def incident(p, line, q):
    a, b = p
    s, t = line
    return b == (s*a+t) % q

def marginal(P, L, q, c=0):
    aa = {(a+c) % q for a, b in P}
    bb = {(b+c*a) % q for a, b in P}
    ss = {(s+c) % q for s, t in L}
    tt = {(t-(s+c)*c) % q for s, t in L}
    return any(b == (s*a+t) % q for a in aa for b in bb for s in ss for t in tt)

def split_row(row, q):
    return ([divmod(i, q) for i in row if i < q*q],
            [divmod(i-q*q, q) for i in row if i >= q*q])

q = 7
circuit = json.loads((ROOT/'quadratic-shadow-f7-circuit.json').read_text())
assert circuit['inputs'] == 98
rows = list(itertools.combinations(range(98), 3))
byte_count = (len(rows)+7)//8
buffers = [bytearray(byte_count) for _ in range(98)]
expected_buffer = bytearray(byte_count)
counts = {'2P1L': 0, '1P2L': 0, 'same_side': 0}
examples = {}
for bit, row in enumerate(rows):
    byte, shift = divmod(bit, 8)
    bit_value = 1 << shift
    for i in row:
        buffers[i][byte] |= bit_value
    P, L = split_row(row, q)
    actual = marginal(P, L, q)
    expected = any(incident(p, line, q) for p in P for line in L)
    if actual:
        expected_buffer[byte] |= bit_value
    if actual and not expected:
        kind = '2P1L' if len(P)==2 else '1P2L' if len(P)==1 else 'same_side'
        counts[kind] += 1
        examples.setdefault(kind, {'input_indices': row, 'points': P, 'lines': L})
values = [int.from_bytes(buf, 'little') for buf in buffers]
for op, a, b in circuit['gates']:
    values.append(values[a] & values[b] if op=='and' else values[a] | values[b])
assert values[circuit['output']] == int.from_bytes(expected_buffer, 'little')
assert counts == {'2P1L': 9702, '1P2L': 9702, 'same_side': 0}
base = {'q': q, 'all_triples_checked_against_explicit_circuit': len(rows),
        'minimal_false_positive_counts': counts, 'lexicographic_examples': examples,
        'smallest_false_positive_weight': 3}
print(json.dumps(base, sort_keys=True))

three_copy = []
for q in [3, 5, 7]:
    points = list(itertools.product(range(q), repeat=2))
    tested = 0
    for pair in itertools.combinations(points, 2):
        for single in points:
            for P, L in [(pair, [single]), ([single], pair)]:
                expected = any(incident(p, line, q) for p in P for line in L)
                actual = all(marginal(P, L, q, c) for c in [0, 1, 2])
                assert actual == expected, (q, P, L)
                tested += 1
    assert not marginal(points, [], q) and not marginal([], points, q)
    three_copy.append({'q':q, 'mixed_triples_checked':tested,
                       'all_triples_count': (2*q*q)*(2*q*q-1)*(2*q*q-2)//6,
                       'false_positive_triples':0})
print(json.dumps({'three_copy_controls': three_copy}, sort_keys=True))

quartet = {'points': [(0,1), (1,0)], 'lines': [(1,0), (2,0)]}
for q in [3, 5, 7, 17, 19]:
    P, L = quartet['points'], quartet['lines']
    assert not any(incident(p, line, q) for p in P for line in L)
    assert all(marginal(P, L, q, c) for c in range(q))
    tagged = [(0,p) for p in P]+[(1,line) for line in L]
    for sub in itertools.combinations(tagged, 3):
        PP = [v for side,v in sub if side==0]
        LL = [v for side,v in sub if side==1]
        assert not all(marginal(PP, LL, q, c) for c in [0,1,2])
print(json.dumps({'smallest_three_copy_false_positive_weight':4,
                  'quartet_passes_every_shear':quartet,
                  'verified_fields':[3,5,7,17,19],
                  'optimized_q17_OR_gates':3*(6*17*17-7*17+2),
                  'q17_edges':17**3,
                  'optimized_q19_OR_gates':3*(6*19*19-7*19+2),
                  'q19_OR_gates':3*(6*19*19-5*19-1),
                  'q19_edges':19**3}, sort_keys=True))

q = 3

def normalize(v):
    for x in v:
        if x:
            inv = pow(x, -1, q)
            return tuple(y*inv % q for y in v)
    raise ValueError('zero vector')
plane = sorted({normalize(v) for v in itertools.product(range(q), repeat=3) if any(v)})
inc = lambda p,l: sum(a*b for a,b in zip(p,l)) % q == 0
P = {normalize((a,b,1)) for a,b in [(0,1),(0,2),(1,0)]}
L = {normalize(v) for v in [(1,0,1),(1,2,0),(2,2,0),(0,0,1)]}
assert L == {l for l in plane if not any(inc(p,l) for p in P)}
assert P == {p for p in plane if not any(inc(p,l) for l in L)}
assert not any(all(inc(p,l) for p in P) for l in plane)
assert not any(all(inc(p,l) for l in L) for p in plane)
print(json.dumps({'q3_generic_extension_points_affine':[[0,1],[0,2],[1,0]],
                  'q3_generic_extension_lines':['x=2','y=x','y=2x','infinity'],
                  'maximal_and_generic':True}, sort_keys=True))
