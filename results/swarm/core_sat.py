import argparse
import itertools
import json
from pathlib import Path


class CNF:
    def __init__(self):
        self.names = {}
        self.clauses = []

    def var(self, *name):
        if name not in self.names:
            self.names[name] = len(self.names) + 1
        return self.names[name]

    def add(self, *lits):
        self.clauses.append(lits)

    def exactly_one(self, xs):
        self.add(*xs)
        for a, b in itertools.combinations(xs, 2):
            self.add(-a, -b)


def model(order, line_ids):
    if order == 2:
        full = list(range(1, 8))
        incident = lambda p, l: (p & l).bit_count() % 2 == 0
    else:
        full = [v for v in itertools.product(range(order), repeat=3)
                if any(v) and next(a for a in v if a) == 1]
        incident = lambda p, l: sum(a * b for a, b in zip(p, l)) % order == 0
    assert len(full) == order * order + order + 1
    assert all(sum(incident(p, l) for p in full) == order + 1 for l in full)
    assert all(sum(incident(p, l) and incident(r, l) for l in full) == 1
               for p, r in itertools.combinations(full, 2))
    assert len(set(line_ids)) == len(line_ids)
    assert all(0 <= i < len(full) for i in line_ids)
    lines = [full[i] for i in line_ids]
    point_ids = [i for i, p in enumerate(full) if any(incident(p, l) for l in lines)]
    points = [full[i] for i in point_ids]
    n = len(points) + len(lines)
    edges = [(p, len(points) + l) for p, pv in enumerate(points)
             for l, lv in enumerate(lines) if incident(pv, lv)]
    return n, points, lines, edges, point_ids


def function(x, edges):
    return any((x >> a) & 1 and (x >> b) & 1 for a, b in edges)


def boundary(n, edges):
    positive = [(1 << a) | (1 << b) for a, b in edges]
    negative = [x for x in range(1 << n) if not function(x, edges)
                and all((x >> i) & 1 or function(x | (1 << i), edges)
                        for i in range(n))]
    for x in range(1 << n):
        if function(x, edges):
            assert any(y & x == y for y in positive)
        else:
            assert any(y | x == y for y in negative)
    return positive + negative, [True] * len(positive) + [False] * len(negative)


def canonical(n, point_count, edges):
    gates = []
    tops = []
    for line in range(point_count, n):
        points = [a for a, b in edges if b == line]
        w = points[0]
        for p in points[1:]:
            gates.append((1, min(w, p), max(w, p)))
            w = n + len(gates) - 1
        gates.append((0, min(line, w), max(line, w)))
        tops.append(n + len(gates) - 1)
    w = tops[0]
    for t in tops[1:]:
        gates.append((1, min(w, t), max(w, t)))
        w = n + len(gates) - 1
    return gates


def ordered_topology(n, gates):
    pending = set(range(len(gates)))
    rename = {}
    result = []
    while pending:
        available = []
        for j in pending:
            op, a, b = gates[j]
            if all(w < n or w - n in rename for w in [a, b]):
                a = a if a < n else n + rename[a - n]
                b = b if b < n else n + rename[b - n]
                available.append(((op, min(a, b), max(a, b)), j))
        assert available, 'Expected an acyclic circuit'
        key, j = min(available)
        rename[j] = len(result)
        result.append(key)
        pending.remove(j)
    assert rename[len(gates) - 1] == len(gates) - 1, 'Canonical output must remain last'
    return result


def input_automorphisms(n, point_count, edges, line_count):
    if line_count > 6:
        raise ValueError('--first-input-orbit permits at most six line vertices')
    assert n == point_count + line_count
    edge_set = set(map(tuple, edges))
    classes = {}
    for p in range(point_count):
        neighbors = tuple(sorted(l - point_count for a, l in edges if a == p))
        classes.setdefault(neighbors, []).append(p)
    automorphisms = []
    for line_perm in itertools.permutations(range(line_count)):
        image_classes = {ns: tuple(sorted(line_perm[l] for l in ns)) for ns in classes}
        if not all(len(classes.get(image, [])) == len(classes[ns])
                   for ns, image in image_classes.items()):
            continue
        perm = list(range(n))
        for ns, ps in classes.items():
            for rank, p in enumerate(ps):
                perm[p] = classes[image_classes[ns]][rank]
        for l in range(line_count):
            perm[point_count + l] = point_count + line_perm[l]
        assert sorted(perm) == list(range(n))
        assert {(perm[a], perm[b]) for a, b in edges} == edge_set
        automorphisms.append(tuple(perm))
    assert tuple(range(n)) in automorphisms
    return sorted(set(automorphisms))


def canonical_in_input_orbit(n, gates, automorphisms):
    candidates = []
    for perm in automorphisms:
        renamed = []
        for op, a, b in gates:
            a = perm[a] if a < n else a
            b = perm[b] if b < n else b
            renamed.append((op, min(a, b), max(a, b)))
        candidates.append(ordered_topology(n, renamed))
    return min(candidates)


def evaluate(n, gates, x):
    values = [bool((x >> i) & 1) for i in range(n)]
    for op, a, b in gates:
        assert 0 <= a <= b < len(values)
        values.append(values[a] or values[b] if op else values[a] and values[b])
    return values[-1]


def check(n, gates, edges):
    for x in range(1 << n):
        assert evaluate(n, gates, x) == function(x, edges), x
    return 1 << n


def generate(args):
    if args.gates < 1:
        raise ValueError('Gate budget must be positive')
    if args.at_most and args.all_gates_used:
        raise ValueError('--at-most cannot be combined with --all-gates-used')
    if args.incomparable_operands and not args.at_most:
        raise ValueError('--incomparable-operands requires --at-most')
    if args.all_active_gates_used and not args.at_most:
        raise ValueError('--all-active-gates-used requires --at-most')
    if args.essential_inputs_used and not args.at_most:
        raise ValueError('--essential-inputs-used requires --at-most')
    if args.order_independent_gates and not args.at_most:
        raise ValueError('--order-independent-gates requires --at-most')
    if args.op_critical_domains and not args.at_most:
        raise ValueError('--op-critical-domains requires --at-most')
    if args.critical_output_witnesses and not args.at_most:
        raise ValueError('--critical-output-witnesses requires --at-most')
    line_ids = list(map(int, args.line_ids.split(',')))
    if args.first_input_orbit and len(line_ids) > 6:
        raise ValueError('--first-input-orbit permits at most six line vertices')
    n, points, lines, edges, point_ids = model(args.order, line_ids)
    if args.strip_point_leaves:
        old_point_count = len(points)
        keep = [p for p in range(old_point_count)
                if sum(a == p for a, _ in edges) > 1]
        remap = {p: i for i, p in enumerate(keep)}
        edges = [(remap[p], len(keep) + l - old_point_count)
                 for p, l in edges if p in remap]
        points = [points[p] for p in keep]
        point_ids = [point_ids[p] for p in keep]
        n = len(points) + len(lines)
    automorphisms = (input_automorphisms(n, len(points), edges, len(lines))
                     if args.first_input_orbit else None)
    rows, labels = boundary(n, edges)
    essential_inputs = None
    essential_witnesses = None
    if args.essential_inputs_used:
        target = [function(x, edges) for x in range(1 << n)]
        essential_inputs, essential_witnesses = [], []
        for i in range(n):
            first_witness, count = None, 0
            for x in range(1 << n):
                if not (x & (1 << i)) and target[x] != target[x | (1 << i)]:
                    count += 1
                    if first_witness is None:
                        first_witness = x
            if count:
                essential_inputs.append(i)
                essential_witnesses.append(dict(input=i, without=first_witness,
                                                with_input=first_witness | (1 << i),
                                                witness_count=count))
    can = canonical(n, len(points), edges)
    if args.first_input_orbit:
        can = canonical_in_input_orbit(n, can, automorphisms)
    elif args.order_independent_gates:
        can = ordered_topology(n, can)
    check(n, can, edges)
    if args.pin_canonical:
        assert args.gates >= len(can) if args.at_most else args.gates == len(can)
    c = CNF()
    for j in range(args.gates):
        limit = n + j
        av = [c.var('a', j, k) for k in range(limit)]
        bv = [c.var('b', j, k) for k in range(limit)]
        c.exactly_one(av)
        c.exactly_one(bv)
        for a in range(limit):
            for b in range(a):
                c.add(-av[a], -bv[b])
        if args.first_input_orbit and j == 0:
            for a in range(n):
                for b in range(a, n):
                    if any(tuple(sorted((perm[a], perm[b]))) < (a, b)
                           for perm in automorphisms):
                        c.add(-av[a], -bv[b])
        op = c.var('op', j)
        for r, x in enumerate(rows):
            u, v, w = (c.var(name, j, r) for name in ['u', 'v', 'w'])
            for selectors, value in [(av, u), (bv, v)]:
                for k, select in enumerate(selectors):
                    if k < n:
                        c.add(-select, value if (x >> k) & 1 else -value)
                    else:
                        earlier = c.var('w', k - n, r)
                        c.add(-select, -value, earlier)
                        c.add(-select, value, -earlier)
            c.add(op, -w, u)
            c.add(op, -w, v)
            c.add(op, w, -u, -v)
            c.add(-op, w, -u)
            c.add(-op, w, -v)
            c.add(-op, -w, u, v)
        if args.pin_canonical and j < len(can):
            kind, a, b = can[j]
            c.add(op if kind else -op)
            c.add(av[a])
            c.add(bv[b])
    if args.at_most:
        outputs = [c.var('output', j) for j in range(args.gates)]
        c.exactly_one(outputs)
        for j in range(args.gates):
            active = c.var('active', j)
            # active_j iff the selected output lies at j or later.
            c.add(-active, *outputs[j:])
            for output in outputs[j:]:
                c.add(-output, active)
            for r, label in enumerate(labels):
                w = c.var('w', j, r)
                c.add(-outputs[j], w if label else -w)
        if args.pin_canonical:
            c.add(outputs[len(can) - 1])
        if args.all_active_gates_used:
            for j, output in enumerate(outputs):
                for k in range(j):
                    c.add(-output, *(c.var(side, later, n + k)
                                    for later in range(k + 1, j + 1)
                                    for side in ['a', 'b']))
        if args.essential_inputs_used:
            for j, output in enumerate(outputs):
                for i in essential_inputs:
                    c.add(-output, *(c.var(side, k, i)
                                    for k in range(j + 1) for side in ['a', 'b']))
    else:
        for r, label in enumerate(labels):
            w = c.var('w', args.gates - 1, r)
            c.add(w if label else -w)
    if args.all_gates_used:
        for j in range(args.gates - 1):
            c.add(*(c.var(side, k, n + j)
                    for k in range(j + 1, args.gates) for side in ['a', 'b']))
    if args.all_gates_pair_active:
        for j in range(args.gates):
            gate_condition = [-c.var('active', j)] if args.at_most else []
            c.add(*gate_condition,
                  *(c.var('w', j, r) for r, label in enumerate(labels) if label))
    if (args.incomparable_operands or args.op_critical_domains
            or args.critical_output_witnesses):
        for j in range(args.gates):
            ab_witnesses, ba_witnesses = [], []
            for r in range(len(rows)):
                u, v = c.var('u', j, r), c.var('v', j, r)
                ab = c.var('incomparable_ab', j, r)
                ba = c.var('incomparable_ba', j, r)
                # ab iff u and not v; ba iff not u and v.
                c.add(-ab, u)
                c.add(-ab, -v)
                c.add(ab, -u, v)
                c.add(-ba, -u)
                c.add(-ba, v)
                c.add(ba, u, -v)
                ab_witnesses.append(ab)
                ba_witnesses.append(ba)
            c.add(-c.var('active', j), *ab_witnesses)
            c.add(-c.var('active', j), *ba_witnesses)
            if args.op_critical_domains:
                # A minimum circuit needs AND port witnesses on false boundary
                # rows, and OR port witnesses on true boundary rows.
                active, op = c.var('active', j), c.var('op', j)
                for witnesses in [ab_witnesses, ba_witnesses]:
                    c.add(-active, op, *(w for w, label in zip(witnesses, labels)
                                        if not label))
                    c.add(-active, -op, *(w for w, label in zip(witnesses, labels)
                                         if label))
    if args.critical_output_witnesses:
        for j in range(args.gates):
            active, op = c.var('active', j), c.var('op', j)
            for direction in ['ab', 'ba']:
                choices = [c.var('critical_row', j, direction, r)
                           for r in range(len(rows))]
                # Exactly one boundary row for an active gate; none otherwise.
                c.add(-active, *choices)
                for left, right in itertools.combinations(choices, 2):
                    c.add(-left, -right)
                for r, choice in enumerate(choices):
                    c.add(-choice, active)
                    c.add(-choice, op if labels[r] else -op)
                    c.add(-choice, c.var('incomparable_' + direction, j, r))
                counter = [c.var('critical_value', j, direction, k)
                           for k in range(n + args.gates)]
                # Select original wire values strictly before the changed gate.
                for r, choice in enumerate(choices):
                    for k in range(n + j):
                        if k < n:
                            c.add(-choice, counter[k] if (rows[r] >> k) & 1
                                  else -counter[k])
                        else:
                            original = c.var('w', k - n, r)
                            c.add(-choice, -counter[k], original)
                            c.add(-choice, counter[k], -original)
                # AND is replaced by its true port; OR by its false port.
                # The selected port pattern and row domain make this NOT op.
                c.add(op, counter[n + j])
                c.add(-op, -counter[n + j])
                for later in range(j + 1, args.gates):
                    u, v = [c.var('critical_' + side, j, direction, later)
                            for side in ['u', 'v']]
                    for side, value in [('a', u), ('b', v)]:
                        for k in range(n + later):
                            select = c.var(side, later, k)
                            c.add(-select, -value, counter[k])
                            c.add(-select, value, -counter[k])
                    w, later_op = counter[n + later], c.var('op', later)
                    c.add(later_op, -w, u)
                    c.add(later_op, -w, v)
                    c.add(later_op, w, -u, -v)
                    c.add(-later_op, w, -u)
                    c.add(-later_op, w, -v)
                    c.add(-later_op, -w, u, v)
                # The original global output selector also chooses the
                # counterfactual output, which must flip the target label.
                for output_at in range(j, args.gates):
                    output = c.var('output', output_at)
                    w = counter[n + output_at]
                    c.add(-active, -output, op, w)
                    c.add(-active, -output, -op, -w)
    key_bits = None
    if args.order_independent_gates:
        key_bits = max(1, (n + args.gates - 2).bit_length())
        keys = []
        for j in range(args.gates):
            key = [c.var('op', j)]
            for side in ['a', 'b']:
                bits = [c.var('key_' + side, j, bit)
                        for bit in range(key_bits - 1, -1, -1)]
                for k in range(n + j):
                    select = c.var(side, j, k)
                    for bit, value in zip(range(key_bits - 1, -1, -1), bits):
                        c.add(-select, value if (k >> bit) & 1 else -value)
                key.extend(bits)
            keys.append(key)
        for j in range(args.gates - 1):
            # Order only when the later gate is active and does not read the earlier one.
            guard = [-c.var('active', j + 1), c.var('a', j + 1, n + j),
                     c.var('b', j + 1, n + j)]
            prefix = c.var('lex_prefix', j, 0)
            c.add(prefix)
            for i, (left, right) in enumerate(zip(keys[j], keys[j + 1])):
                c.add(*guard, -prefix, -left, right)
                if i + 1 < len(keys[j]):
                    following = c.var('lex_prefix', j, i + 1)
                    # following iff prefix and (left iff right).
                    c.add(-following, prefix)
                    c.add(-following, -left, right)
                    c.add(-following, left, -right)
                    c.add(-prefix, -left, -right, following)
                    c.add(-prefix, left, right, following)
                    prefix = following
    path = Path(args.output)
    with path.with_suffix('.cnf').open('w') as f:
        f.write(f'p cnf {len(c.names)} {len(c.clauses)}\n')
        for clause in c.clauses:
            f.write(' '.join(map(str, clause)) + ' 0\n')
    data = dict(n=n, points=points, lines=lines, edges=edges, rows=rows,
                order=args.order, point_ids=point_ids, line_ids=line_ids,
                stripped_point_leaves=args.strip_point_leaves,
                all_gates_used=args.all_gates_used,
                all_gates_pair_active=args.all_gates_pair_active,
                at_most=args.at_most,
                incomparable_operands=args.incomparable_operands,
                all_active_gates_used=args.all_active_gates_used,
                essential_inputs_used=args.essential_inputs_used,
                essential_inputs=essential_inputs,
                essential_input_witnesses=essential_witnesses,
                essentiality_assignments_checked=(1 << n) if args.essential_inputs_used else 0,
                order_independent_gates=args.order_independent_gates,
                key_bits=key_bits,
                labels=labels, gates=args.gates,
                names=[[list(k), v] for k, v in c.names.items()],
                **({'op_critical_domains': True} if args.op_critical_domains else {}),
                **({'critical_output_witnesses': True} if args.critical_output_witnesses else {}),
                **({'first_input_orbit': True, 'input_automorphisms': automorphisms}
                   if args.first_input_orbit else {}))
    path.with_suffix('.json').write_text(json.dumps(data))
    print(json.dumps(dict(inputs=n, edges=len(edges), positive=sum(labels),
                         negative=len(labels)-sum(labels), gates=args.gates,
                         canonical_gates=len(can), variables=len(c.names),
                         clauses=len(c.clauses), allow_repeated_operands=True,
                         at_most=args.at_most,
                         incomparable_operands=args.incomparable_operands,
                         all_active_gates_used=args.all_active_gates_used,
                         essential_inputs_used=args.essential_inputs_used,
                         essential_inputs=essential_inputs,
                         order_independent_gates=args.order_independent_gates,
                         no_minimality_pruning=not (
                             args.all_gates_pair_active or args.incomparable_operands
                             or args.op_critical_domains or args.critical_output_witnesses),
                         **({'op_critical_domains': True} if args.op_critical_domains else {}),
                         **({'critical_output_witnesses': True} if args.critical_output_witnesses else {}),
                         **({'first_input_orbit': True, 'input_automorphisms': len(automorphisms)}
                            if args.first_input_orbit else {}))))


def decode(args):
    d = json.loads(Path(args.metadata).read_text())
    values = {}
    for line in Path(args.solver_output).read_text().splitlines():
        if line.startswith('v '):
            for literal in map(int, line.split()[1:]):
                if literal:
                    values[abs(literal)] = literal > 0
    assert values, 'No SAT assignment found'
    names = {tuple(k): v for k, v in d['names']}
    gate_count = d['gates']
    if d.get('at_most', False):
        outputs = [j for j in range(gate_count) if values[names[('output', j)]]]
        assert len(outputs) == 1, 'Expected exactly one selected output'
        selected = outputs[0]
        for j in range(gate_count):
            assert values[names[('active', j)]] == (j <= selected)
        gate_count = selected + 1
    gates = []
    for j in range(gate_count):
        a = [k for k in range(d['n'] + j) if values[names[('a', j, k)]]]
        b = [k for k in range(d['n'] + j) if values[names[('b', j, k)]]]
        assert len(a) == len(b) == 1
        gates.append((int(values[names[('op', j)]]), a[0], b[0]))
    count = check(d['n'], gates, d['edges'])
    result = dict(inputs=d['n'], gates=gates, output=d['n']+len(gates)-1,
                  assignments_checked=count, edges=d['edges'])
    Path(args.output).write_text(json.dumps(result, indent=2))
    print(json.dumps(dict(gates=len(gates), assignments_checked=count,
                         circuit_file=args.output)))


def extend(args):
    d = json.loads(Path(args.metadata).read_text())
    circuit = json.loads(Path(args.circuit).read_text())
    assert not d.get('stripped_point_leaves', False), 'Leaf-stripped cores need a separate extension proof'
    q = d['order']
    full_n = q * q + q + 1
    _, full_points, _, full_edges, _ = model(q, list(range(full_n)))
    adjacency = {(p, l - full_n) for p, l in full_edges}
    point_count = len(d['points'])

    def rename(w):
        if w < point_count:
            return d['point_ids'][w]
        if w < d['n']:
            return full_n + d['line_ids'][w - point_count]
        return 2 * full_n + w - d['n']

    gates = [(op, min(rename(a), rename(b)), max(rename(a), rename(b)))
             for op, a, b in circuit['gates']]
    output = rename(circuit['output'])
    for line in range(full_n):
        if line in d['line_ids']:
            continue
        points = [p for p in range(full_n) if (p, line) in adjacency]
        wire = points[0]
        for p in points[1:]:
            gates.append((1, min(wire, p), max(wire, p)))
            wire = 2 * full_n + len(gates) - 1
        gates.append((0, min(wire, full_n + line), max(wire, full_n + line)))
        wire = 2 * full_n + len(gates) - 1
        gates.append((1, min(output, wire), max(output, wire)))
        output = 2 * full_n + len(gates) - 1
    assert len(gates) == len(circuit['gates']) + (full_n - len(d['lines'])) * (q + 2)
    positive = [(1 << p) | (1 << (full_n + l)) for p, l in adjacency]
    negative = []
    for point_mask in range(1 << full_n):
        lines = [l for l in range(full_n)
                 if all(not ((point_mask >> p) & 1) or (p, l) not in adjacency
                        for p in range(full_n))]
        closure = sum(1 << p for p in range(full_n)
                      if all((p, l) not in adjacency for l in lines))
        if closure == point_mask:
            negative.append(point_mask | sum(1 << (full_n + l) for l in lines))
    assert all(evaluate(2 * full_n, gates, x) for x in positive)
    assert all(not evaluate(2 * full_n, gates, x) for x in negative)
    result = dict(order=q, inputs=2 * full_n, gates=gates, output=output,
                  positive_boundary_checked=len(positive),
                  negative_boundary_checked=len(negative),
                  source_metadata=args.metadata, source_circuit=args.circuit)
    Path(args.output).write_text(json.dumps(result, indent=2))
    print(json.dumps(dict(full_inputs=2 * full_n, gates=len(gates),
                         positive_boundary=len(positive), negative_boundary=len(negative))))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    subs = parser.add_subparsers(dest='mode', required=True)
    g = subs.add_parser('generate')
    g.add_argument('--gates', type=int, required=True)
    g.add_argument('--order', type=int, choices=[2, 3], default=2)
    g.add_argument('--line-ids', default='0,1,2,3,4')
    g.add_argument('--output', required=True)
    g.add_argument('--pin-canonical', action='store_true')
    g.add_argument('--strip-point-leaves', action='store_true')
    g.add_argument('--all-gates-used', action='store_true')
    g.add_argument('--all-gates-pair-active', action='store_true')
    g.add_argument('--at-most', action='store_true')
    g.add_argument('--incomparable-operands', action='store_true')
    g.add_argument('--all-active-gates-used', action='store_true')
    g.add_argument('--essential-inputs-used', action='store_true')
    g.add_argument('--order-independent-gates', action='store_true')
    g.add_argument('--op-critical-domains', action='store_true')
    g.add_argument('--critical-output-witnesses', action='store_true')
    g.add_argument('--first-input-orbit', action='store_true')
    d = subs.add_parser('decode')
    d.add_argument('--metadata', required=True)
    d.add_argument('--solver-output', required=True)
    d.add_argument('--output', required=True)
    e = subs.add_parser('extend')
    e.add_argument('--metadata', required=True)
    e.add_argument('--circuit', required=True)
    e.add_argument('--output', required=True)
    args = parser.parse_args()
    {'generate': generate, 'decode': decode, 'extend': extend}[args.mode](args)
