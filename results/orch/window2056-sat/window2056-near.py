import argparse
import json
import random
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--data', required=True)
parser.add_argument('--seeds', required=True)
parser.add_argument('--seed-index', type=int, default=0)
parser.add_argument('--window', type=int, required=True)
parser.add_argument('--remove', type=int, default=1)
parser.add_argument('--order', choices=['original', 'delay-bad', 'random'], default='delay-bad')
parser.add_argument('--order-seed', type=int, default=0)
parser.add_argument('--allow-read1', action='store_true')
parser.add_argument('--known', action='store_true')
parser.add_argument('--allow-near', action='store_true')
parser.add_argument('--output', required=True)
args = parser.parse_args()
data = json.loads(Path(args.data).read_text())
seeds = json.loads(Path(args.seeds).read_text())
seed = seeds[args.seed_index]
n = data.get('n', data.get('inputs'))
rows = data['rows']
edges = data['edges']
gates = seed['gates']
output = seed.get('output', n + len(gates) - 1)
assert len(rows) == len(set(rows))
assert output == n + len(gates) - 1
assert all(op in (0, 1) and 0 <= a < n+j and 0 <= b < n+j for j, (op, a, b) in enumerate(gates))
width = len(rows)
target = sum(int(any((row >> a) & (row >> b) & 1 for a, b in edges)) << k for k, row in enumerate(rows))
negative = ((1 << width) - 1) ^ target
inputs = [sum(((row >> i) & 1) << k for k, row in enumerate(rows)) for i in range(n)]

def evaluate(net):
    values = inputs.copy()
    for op, a, b in net:
        values.append(values[a] & values[b] if op == 0 else values[a] | values[b])
    return values

def read_profiles(net, edge):
    left, right = edge
    profiles = [1 if i == left else 2 if i == right else 0 for i in range(n)]
    for op, a, b in net:
        if op == 1:
            value = profiles[a] | profiles[b]
        else:
            value = 4 if ((profiles[a] & 1 and profiles[b] & 2) or (profiles[a] & 2 and profiles[b] & 1)) else 0
        profiles.append(value)
    return profiles

values = evaluate(gates)
seed_output = values[output]
assert args.allow_near or seed_output == target
bad_edges = [edge for edge in edges if (seed_output >> rows.index((1 << edge[0]) | (1 << edge[1]))) & 1 and not read_profiles(gates, edge)[output] & 4]
assert args.allow_read1 or bad_edges
marked = bad_edges[0] if bad_edges else edges[0]
if args.order != 'original':
    clean = [(value & negative) == 0 for value in values]
    removed = set()
    def flatten(wire):
        if wire >= n and clean[wire] and gates[wire-n][0] == 1:
            removed.add(wire)
            _, a, b = gates[wire-n]
            return flatten(a) + flatten(b)
        return [wire]
    terms = flatten(output)
    for wire in removed:
        readers = {j for j, (_, a, b) in enumerate(gates) if wire in (a, b)}
        assert len(readers) <= 1
    if args.order == 'random':
        random.Random(args.order_seed).shuffle(terms)
    else:
        row = rows.index((1 << marked[0]) | (1 << marked[1]))
        profiles = read_profiles(gates, marked)
        candidates = [wire for wire in terms if (values[wire] >> row) & 1 and not profiles[wire] & 4]
        chosen = max(candidates) if candidates else terms[-1]
        terms = [wire for wire in terms if wire != chosen] + [chosen]
    reordered = []
    mapping = {i: i for i in range(n)}
    def emit(wire):
        if wire in mapping:
            return mapping[wire]
        assert wire not in removed
        op, a, b = gates[wire-n]
        a, b = sorted((emit(a), emit(b)))
        result = n + len(reordered)
        reordered.append([op, a, b])
        mapping[wire] = result
        return result
    accumulated = emit(terms[0])
    for term in terms[1:]:
        term = emit(term)
        result = n + len(reordered)
        reordered.append([1, min(accumulated, term), max(accumulated, term)])
        accumulated = result
    assert len(reordered) == len(gates)
    gates = reordered
    output = accumulated
    values = evaluate(gates)
    assert output == n + len(gates) - 1 and values[output] == seed_output
    assert args.allow_read1 or not read_profiles(gates, marked)[output] & 4
else:
    gates = [[op, min(a, b), max(a, b)] for op, a, b in gates]

assert 1 <= args.window <= len(gates)
assert 0 <= args.remove < args.window
assert not args.known or args.remove == 0
prefix = len(gates) - args.window
size = len(gates) - args.remove
output_path = Path(args.output)
output_path.parent.mkdir(exist_ok=True)

def bv(value, bits):
    return f'(_ bv{value} {bits})'

lines = ['(set-logic QF_BV)']
for j in range(size):
    bits = (n+j).bit_length()
    for name, count in [(f'a{j}', bits), (f'b{j}', bits), (f'o{j}', 2)]:
        lines.append(f'(declare-const {name} (_ BitVec {count}))')
    if j < prefix or args.known:
        op, a, b = gates[j]
        lines.extend([f'(assert (= a{j} {bv(a, bits)}))', f'(assert (= b{j} {bv(b, bits)}))', f'(assert (= o{j} {bv(op, 2)}))'])
    if j >= prefix:
        lines.extend([f'(assert (bvult a{j} {bv(n+j, bits)}))', f'(assert (bvult b{j} {bv(n+j, bits)}))', f'(assert (bvule a{j} b{j}))', f'(assert (bvult o{j} #b10))'])

value_terms = [bv(v, width) for v in values[:n+prefix]]
profile_terms = [bv(v, 3) for v in read_profiles(gates, marked)[:n+prefix]]
for j in range(prefix, size):
    bits = (n+j).bit_length()
    def source(name, available):
        expression = available[-1]
        for i in reversed(range(len(available)-1)):
            expression = f'(ite (= {name} {bv(i, bits)}) {available[i]} {expression})'
        return expression
    a, b = source(f'a{j}', value_terms), source(f'b{j}', value_terms)
    lines.append(f'(declare-const v{j} (_ BitVec {width}))')
    lines.append(f'(assert (= v{j} (let ((a {a}) (b {b})) (ite (= o{j} #b00) (bvand a b) (bvor a b)))))')
    value_terms.append(f'v{j}')
    if not args.allow_read1:
        a, b = source(f'a{j}', profile_terms), source(f'b{j}', profile_terms)
        lines.append(f'(declare-const rp{j} (_ BitVec 3))')
        cross = '(or (and (= ((_ extract 0 0) a) #b1) (= ((_ extract 1 1) b) #b1)) (and (= ((_ extract 1 1) a) #b1) (= ((_ extract 0 0) b) #b1)))'
        lines.append(f'(assert (= rp{j} (let ((a {a}) (b {b})) (ite (= o{j} #b00) (ite {cross} #b100 #b000) (bvor a b)))))')
        profile_terms.append(f'rp{j}')
lines.append(f'(assert (= v{size-1} {bv(target, width)}))')
if not args.allow_read1:
    lines.append(f'(assert (= ((_ extract 2 2) rp{size-1}) #b0))')
for j in range(prefix, size-1):
    uses = []
    for k in range(j+1, size):
        bits = (n+k).bit_length()
        uses.append(f'(or (= a{k} {bv(n+j, bits)}) (= b{k} {bv(n+j, bits)}))')
    lines.append('(assert (or ' + ' '.join(uses) + '))')
    old_width, new_width = (n+j).bit_length(), (n+j+1).bit_length()
    def extend(name):
        return name if old_width == new_width else f'((_ zero_extend {new_width-old_width}) {name})'
    a, b = extend(f'a{j}'), extend(f'b{j}')
    order = f'(or (bvult {a} a{j+1}) (and (= {a} a{j+1}) (bvult {b} b{j+1})) (and (= {a} a{j+1}) (= {b} b{j+1}) (bvule o{j} o{j+1})))'
    dependency = f'(or (= a{j+1} {bv(n+j, new_width)}) (= b{j+1} {bv(n+j, new_width)}))'
    if not args.known:
        lines.append(f'(assert (or {dependency} {order}))')
output_path.write_text('\n'.join(lines))
record = {'n': n, 'rows': rows, 'edges': edges, 'seed_index': args.seed_index, 'original_gates': seed['gates'], 'ordered_gates': gates, 'prefix_size': prefix, 'window_before': args.window, 'window_after': args.window-args.remove, 'size': size, 'marked_bad_edge': marked, 'preserve_bad_edge': not args.allow_read1, 'order': args.order, 'known': args.known, 'allow_near': args.allow_near, 'seed_boundary_mismatches': (seed_output ^ target).bit_count()}
output_path.with_suffix('.data.json').write_text(json.dumps(record, indent=2))
print(json.dumps({k: record[k] for k in ['seed_index', 'prefix_size', 'window_before', 'window_after', 'size', 'marked_bad_edge', 'preserve_bad_edge', 'order', 'known']}))
