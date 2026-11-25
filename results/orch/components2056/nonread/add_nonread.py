import argparse
import hashlib
import itertools
import json
from pathlib import Path
import shutil


parser = argparse.ArgumentParser(description='Append to an original, unrenamed component CNF.')
parser.add_argument('--cnf', required=True)
parser.add_argument('--mapping', required=True)
parser.add_argument('--library', required=True)
parser.add_argument('--data', required=True)
parser.add_argument('--prefix', required=True)
parser.add_argument('--pin-circuit')
args = parser.parse_args()
digest = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
lib = json.loads(Path(args.library).read_text())
mapping = json.loads(Path(args.mapping).read_text())
data = json.loads(Path(args.data).read_text())
assert mapping['library_sha256'] == digest(args.library)
assert lib['data_sha256'] == digest(args.data)
n = lib['inputs']
assert n == 26 and lib['row_count'] == 756 and lib['positive_count'] == 52
edges = [(p, 13 + l) for p in range(13) for l in range(13)
         if (p + l) % 13 in (0, 1, 3, 9)]
positive_rows = {(1 << p) | (1 << l) for p, l in edges}
neighbors = [sum(1 << (l - 13) for p, l in edges if p == point)
             for point in range(13)]
negative_rows = set()
for points in range(1 << 13):
    covered = 0
    for point in range(13):
        if points >> point & 1:
            covered |= neighbors[point]
    lines = ((1 << 13) - 1) ^ covered
    closed = sum(1 << point for point in range(13) if not (neighbors[point] & lines))
    if closed == points:
        negative_rows.add(points | (lines << 13))
rows = data['rows']
assert len(edges) == 52 and len(negative_rows) == 704
assert len(rows) == len(set(rows)) == 756
assert set(rows[:52]) == positive_rows and set(rows[52:]) == negative_rows
values = [int(s, 16) for s in lib['profiles']]
primary = [sum(((r >> i) & 1) << j for j, r in enumerate(rows)) for i in range(n)]
assert values[:n] == primary and values[lib['goal']] == (1 << 52) - 1
N = len(values)
assert len(mapping['selected']) == N and len(mapping['chosen']) == len(lib['productions'])
variables = mapping['variables']
base_variables = variables
base_clauses = mapping['clauses']
prefix = Path(args.prefix)
prefix.parent.mkdir(parents=True, exist_ok=True)
extra_path = prefix.with_suffix('.extra.cnf')
extra = extra_path.open('w')
extra_count = 0


def fresh():
    global variables
    variables += 1
    return variables


def neg(x):
    return not x if type(x) is bool else -x


def add(*literals):
    global extra_count
    if any(x is True for x in literals):
        return
    xs = [x for x in literals if x is not False]
    assert all(type(x) is int and x != 0 for x in xs)
    extra.write(' '.join(map(str, xs)) + ' 0\n')
    extra_count += 1


edge_choice = [fresh() for _ in edges]
add(*edge_choice)
for a, b in itertools.combinations(edge_choice, 2):
    add(-a, -b)
point_flags = [fresh() for _ in range(13)]
line_flags = [fresh() for _ in range(13)]
for point, flag in enumerate(point_flags):
    choices = [v for (p, l), v in zip(edges, edge_choice) if p == point]
    for v in choices:
        add(-v, flag)
    add(-flag, *choices)
for line, flag in enumerate(line_flags):
    choices = [v for (p, l), v in zip(edges, edge_choice) if l == 13 + line]
    for v in choices:
        add(-v, flag)
    add(-flag, *choices)
states = [(point_flags[i], False, False) if i < 13
          else (False, line_flags[i - 13], False) for i in range(n)]
states += [tuple(fresh() for _ in range(3)) for _ in range(n, N)]
for index, (parent, op, left, right) in enumerate(lib['productions']):
    z = mapping['chosen'][index]
    out, a, b = states[parent], states[left], states[right]
    if op == 1:
        for k in range(3):
            add(-z, -out[k], a[k], b[k])
            add(-z, out[k], neg(a[k]))
            add(-z, out[k], neg(b[k]))
    else:
        assert op == 0
        add(-z, -out[0])
        add(-z, -out[1])
        # out[2] iff (a[0] AND b[1]) OR (a[1] AND b[0]).
        # Distribute the two-term DNF, avoiding any new producer auxiliaries.
        for x in (a[0], b[1]):
            for y in (a[1], b[0]):
                add(-z, -out[2], x, y)
        add(-z, out[2], neg(a[0]), neg(b[1]))
        add(-z, out[2], neg(a[1]), neg(b[0]))
add(-states[lib['goal']][2])

pin_summary = None
if args.pin_circuit:
    circuit = json.loads(Path(args.pin_circuit).read_text())
    ids = {v: i for i, v in enumerate(values)}
    production_ids = {tuple(p): i for i, p in enumerate(lib['productions'])}
    bits = primary[:]
    wire_profiles = list(range(n))
    first_producer = {}
    for j, (op, a, b) in enumerate(circuit['gates']):
        assert op in (0, 1) and 0 <= a < n + j and 0 <= b < n + j
        v = (bits[a] | bits[b]) if op else (bits[a] & bits[b])
        assert v in ids
        parent = ids[v]
        left, right = sorted((wire_profiles[a], wire_profiles[b]))
        if parent >= n and parent not in (left, right):
            first_producer.setdefault(parent, production_ids[(parent, op, left, right)])
        bits.append(v)
        wire_profiles.append(parent)
    assert wire_profiles[circuit['output']] == lib['goal']
    order, visiting, visited = [], set(), set(range(n))

    def visit(q):
        if q in visited:
            return
        assert q not in visiting and q in first_producer
        visiting.add(q)
        _, _, left, right = lib['productions'][first_producer[q]]
        visit(left)
        visit(right)
        visiting.remove(q)
        visited.add(q)
        order.append(q)

    visit(lib['goal'])
    chosen_indices = {first_producer[q] for q in order}
    depths = {i: 0 for i in range(n)}
    for q in order:
        _, _, left, right = lib['productions'][first_producer[q]]
        depths[q] = max(depths[left], depths[right]) + 1
    depths[lib['goal']] = mapping['bound']
    for q in range(n, N):
        add(mapping['selected'][q] if q in visited else -mapping['selected'][q])
        rank = depths.get(q, 0)
        assert rank <= mapping['bound']
        for j, variable in enumerate(mapping['ranks'][q]):
            add(variable if rank >> j & 1 else -variable)
    for i, variable in enumerate(mapping['chosen']):
        add(variable if i in chosen_indices else -variable)
    pin_summary = {'circuit_sha256': digest(args.pin_circuit),
                   'selected_noninputs': len(order)}

extra.close()
with Path(args.cnf).open() as original, prefix.with_suffix('.cnf').open('w') as out:
    header = original.readline().split()
    assert header == ['p', 'cnf', str(base_variables), str(base_clauses)]
    out.write(f'p cnf {variables} {base_clauses + extra_count}\n')
    shutil.copyfileobj(original, out)
    with extra_path.open() as tail:
        shutil.copyfileobj(tail, out)
mapping.update({'variables': variables, 'clauses': base_clauses + extra_count,
                'base_cnf_sha256': digest(args.cnf),
                'base_mapping_sha256': digest(args.mapping),
                'base_variables': base_variables, 'base_clauses': base_clauses,
                'joint_edges': edges, 'joint_edge_selectors': edge_choice,
                'joint_states': states, 'require_nonread_edge': True,
                'nonread_necessary_for_bound': mapping['bound'] <= 63,
                'pin_circuit': pin_summary})
prefix.with_suffix('.mapping.json').write_text(json.dumps(mapping, separators=(',', ':')) + '\n')
summary = {'scope': 'Restricted component grammar; non-read1 is necessary for this plane only at bound<=63',
           'library_sha256': digest(args.library), 'base_cnf_sha256': digest(args.cnf),
           'base_variables': base_variables, 'new_variables': variables - base_variables,
           'variables': variables, 'base_clauses': base_clauses,
           'new_clauses': extra_count, 'clauses': base_clauses + extra_count,
           'cnf_sha256': digest(prefix.with_suffix('.cnf')), 'pin_circuit': pin_summary}
prefix.with_suffix('.summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary))
