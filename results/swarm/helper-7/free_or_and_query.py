"""Free-OR AND synthesis, with optional restricted private-OR witness cost.

The default encoder has the same complete normalization as the independently
reviewed H12 query: arbitrary OR source subsets, disjoint common-source factoring,
left/right orientation, greedy colex gate order, and unused false padding.
The optional private-OR cap restricts the witness family; UNSAT with that cap is
not a lower bound for circuits that share OR subexpressions. The optional AND
Kraft bound counts equal operand states over every maximal false assignment.
"""

import argparse
import ctypes
import ctypes.util
import hashlib
import json
from pathlib import Path
import re
import time


H12_EDGES = [(0,4),(0,5),(1,3),(1,5),(2,3),(2,4),(0,6),(6,7),(7,3),
             (1,8),(8,9),(9,4),(2,10),(10,11),(11,5)]
H12_SHA256 = 'feba8ebfee2d453ead6a6e1cda8a90d317d70aef341349ed1d046cb60daf1499'


def boundary(n, edges):
    assert 1 <= n <= 20
    assert all(0 <= a < n and 0 <= b < n and a != b for a, b in edges)
    positive = sorted({(1 << a) | (1 << b) for a, b in edges})
    negative = []
    for row in range(1 << n):
        if any((row & e) == e for e in positive):
            continue
        if all(row & (1 << v) or any(((row | (1 << v)) & e) == e for e in positive)
               for v in range(n)):
            negative.append(row)
    return positive, negative


def generate(n, edges, k, timeout_ms=1200000, private_or_cap=None, and_kraft=False):
    assert k >= 0 and timeout_ms > 0
    assert private_or_cap is None or private_or_cap >= 0
    positive, negative = boundary(n, edges)
    rows = positive + negative
    bits, width = len(rows), n + k
    q = ['(set-logic QF_BV)', f'(set-option :timeout {timeout_ms})',
         '(set-option :produce-models true)']
    for i in range(n):
        value = sum(1 << j for j, row in enumerate(rows) if row & (1 << i))
        q.append(f'(define-fun v{i} () (_ BitVec {bits}) (_ bv{value} {bits}))')
    neutral = f'(_ bv0 {bits})'
    selectors, regions = [], []

    def aggregate(label, end):
        term, mask = neutral, f'(_ bv0 {width})'
        names = []
        for j in range(end):
            name = f'{label}_{j}'
            selectors.append(name)
            names.append(name)
            q.append(f'(declare-const {name} Bool)')
            term = f'(bvor {term} (ite {name} v{j} {neutral}))'
            mask = f'(bvor {mask} (ite {name} (_ bv{1 << j} {width}) (_ bv0 {width})))'
        regions.append(names)
        q.append(f'(define-fun mask_{label} () (_ BitVec {width}) {mask})')
        return term

    for i in range(k):
        left = aggregate(f'l{i}', n + i)
        right = aggregate(f'r{i}', n + i)
        if and_kraft:
            q.append(f'(define-fun kraft_left{i} () (_ BitVec {bits}) {left})')
            q.append(f'(define-fun kraft_right{i} () (_ BitVec {bits}) {right})')
            left, right = f'kraft_left{i}', f'kraft_right{i}'
        q.append(f'(declare-const v{n + i} (_ BitVec {bits}))')
        q.append(f'(assert (= v{n + i} (bvand {left} {right})))')
        rankwidth = (n + k + 1).bit_length()
        rank = f'(_ bv0 {rankwidth})'
        for j in range(n + i):
            rank = f'(ite (or l{i}_{j} r{i}_{j}) (_ bv{j + 1} {rankwidth}) {rank})'
        q.append(f'(define-fun rank{i} () (_ BitVec {rankwidth}) {rank})')
        q.append(f'(assert (= (bvand mask_l{i} mask_r{i}) (_ bv0 {width})))')
        q.append(f'(assert (bvule mask_l{i} mask_r{i}))')
        if i:
            ordered = f'(or (bvult rank{i-1} rank{i}) (and (= rank{i-1} rank{i}) (or (bvult mask_l{i-1} mask_l{i}) (and (= mask_l{i-1} mask_l{i}) (bvule mask_r{i-1} mask_r{i})))))'
            q.append(f'(assert {ordered})')
    output = aggregate('out', n + k)
    q.append(f'(assert (= {output} (_ bv{(1 << len(positive)) - 1} {bits})))')

    if and_kraft:
        # For the M distinct maximal false rows, Kraft gives sum 2^equal <= 2^k.
        # Since 2^equal >= equal+1, the total equal operand count is <= 2^k-M.
        # False padding is included among these k syntactic AND gates.
        budget = (1 << k) - len(negative)
        if budget < 0:
            q.append('(assert false)')
        else:
            maximum_equal = k * len(negative)
            count_width = max(1, max(maximum_equal, budget).bit_length())
            zero, one = f'(_ bv0 {count_width})', f'(_ bv1 {count_width})'
            total = zero
            for i in range(k):
                q.append(f'(define-fun kraft_diff{i} () (_ BitVec {bits}) (bvxor kraft_left{i} kraft_right{i}))')
                for row_index in range(len(positive), bits):
                    equal = f'(= ((_ extract {row_index} {row_index}) kraft_diff{i}) #b0)'
                    total = f'(bvadd {total} (ite {equal} {one} {zero}))'
            q.append(f'(define-fun kraft_equal_total () (_ BitVec {count_width}) {total})')
            q.append(f'(assert (bvule kraft_equal_total (_ bv{budget} {count_width})))')

    if private_or_cap is not None:
        # Exact sum max(region membership count - 1, 0). The accumulator width
        # exceeds the largest possible total, so bit-vector addition cannot wrap.
        total_slots = sum(len(region) for region in regions)
        cost_width = max(1, (max(total_slots, private_or_cap) + 1).bit_length())
        zero, one = f'(_ bv0 {cost_width})', f'(_ bv1 {cost_width})'
        total = zero
        for i, region in enumerate(regions):
            count = zero
            for name in region:
                count = f'(bvadd {count} (ite {name} {one} {zero}))'
            q.append(f'(define-fun region_count{i} () (_ BitVec {cost_width}) {count})')
            cost = f'(ite (= region_count{i} {zero}) {zero} (bvsub region_count{i} {one}))'
            total = f'(bvadd {total} {cost})'
        q.append(f'(assert (bvule {total} (_ bv{private_or_cap} {cost_width})))')
    q.append('(check-sat)')
    source = '\n'.join(q) + '\n'
    metadata = {
        'n': n, 'and_cap': k, 'edges': [list(e) for e in edges],
        'positive_rows': positive, 'negative_rows': negative,
        'selectors': selectors, 'private_or_cap': private_or_cap,
        'scope': ('free-OR AND-count model' if private_or_cap is None else
                  'restricted private-OR witness family; UNSAT is not a full lower bound'),
        'smt_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'smt_bytes': len(source.encode()),
    }
    if and_kraft:
        metadata.update(and_kraft=True, and_kraft_mis_count=len(negative),
                        and_kraft_equal_budget=(1 << k) - len(negative))
    return source, metadata


def solve(source, names):
    path = ctypes.util.find_library('z3')
    if path is None:
        raise RuntimeError('local libz3 is unavailable')
    lib = ctypes.CDLL(path)
    lib.Z3_mk_config.argtypes = []
    lib.Z3_mk_config.restype = ctypes.c_void_p
    lib.Z3_mk_context.argtypes = [ctypes.c_void_p]
    lib.Z3_mk_context.restype = ctypes.c_void_p
    lib.Z3_eval_smtlib2_string.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
    lib.Z3_eval_smtlib2_string.restype = ctypes.c_char_p
    lib.Z3_del_context.argtypes = [ctypes.c_void_p]
    lib.Z3_del_context.restype = None
    lib.Z3_del_config.argtypes = [ctypes.c_void_p]
    lib.Z3_del_config.restype = None
    lib.Z3_get_full_version.argtypes = []
    lib.Z3_get_full_version.restype = ctypes.c_char_p
    cfg = lib.Z3_mk_config()
    ctx = lib.Z3_mk_context(cfg)
    if not cfg or not ctx:
        raise RuntimeError('libz3 failed to create a config/context')
    try:
        started = time.monotonic()
        raw_status = lib.Z3_eval_smtlib2_string(ctx, source.encode()).decode().strip()
        elapsed = time.monotonic() - started
        if raw_status not in ('sat', 'unsat', 'unknown'):
            raise RuntimeError('unexpected solver response: ' + raw_status)
        result = {'status': raw_status, 'seconds': elapsed,
                  'z3_version': lib.Z3_get_full_version().decode(),
                  'raw_status': raw_status}
        if raw_status == 'sat':
            assert all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', name) for name in names)
            query = '(get-value (' + ' '.join(names) + '))'
            raw_values = lib.Z3_eval_smtlib2_string(ctx, query.encode()).decode()
            pairs = re.findall(r'\(([A-Za-z][A-Za-z0-9_]*)\s+(true|false)\)', raw_values)
            values = {name: value == 'true' for name, value in pairs}
            if len(pairs) != len(names) or set(values) != set(names):
                raise RuntimeError('model does not give every Boolean selector exactly once')
            result.update(selectors=values, raw_values=raw_values)
        return result
    finally:
        lib.Z3_del_context(ctx)
        lib.Z3_del_config(cfg)


def selected_regions(metadata, values):
    n, k = metadata['n'], metadata['and_cap']
    assert set(values) == set(metadata['selectors'])
    gates = []
    for i in range(k):
        left = [j for j in range(n + i) if values[f'l{i}_{j}']]
        right = [j for j in range(n + i) if values[f'r{i}_{j}']]
        gates.append((left, right))
    output = [j for j in range(n + k) if values[f'out_{j}']]
    return gates, output


def validate_selected_model(metadata, values):
    n, k = metadata['n'], metadata['and_cap']
    gates, output = selected_regions(metadata, values)
    previous = None
    for left, right in gates:
        assert not (set(left) & set(right))
        lm, rm = sum(1 << j for j in left), sum(1 << j for j in right)
        assert lm <= rm
        key = (max(left + right, default=-1) + 1, lm, rm)
        assert previous is None or previous <= key
        previous = key
    private_cost = sum(max(len(region) - 1, 0) for pair in gates for region in pair)
    private_cost += max(len(output) - 1, 0)
    cap = metadata['private_or_cap']
    assert cap is None or private_cost <= cap
    positives = set(metadata['positive_rows'])
    for row in metadata['positive_rows'] + metadata['negative_rows']:
        wires = [bool(row & (1 << v)) for v in range(n)]
        for left, right in gates:
            wires.append(any(wires[j] for j in left) and any(wires[j] for j in right))
        assert any(wires[j] for j in output) == (row in positives)
    if metadata.get('and_kraft', False):
        counts = equal_operand_counts(metadata, values)
        assert counts['equal_total'] <= metadata['and_kraft_equal_budget']
    return private_cost


def equal_operand_counts(metadata, values):
    n, k = metadata['n'], metadata['and_cap']
    gates, _ = selected_regions(metadata, values)
    row_counts = []
    for row in metadata['negative_rows']:
        wires = [bool(row & (1 << v)) for v in range(n)]
        count = 0
        for left, right in gates:
            a, b = any(wires[j] for j in left), any(wires[j] for j in right)
            count += a == b
            wires.append(a and b)
        row_counts.append(count)
    return {'equal_per_MIS_row': row_counts, 'equal_total': sum(row_counts),
            'mis_count': len(row_counts), 'and_count': k,
            'linear_budget': (1 << k) - len(row_counts),
            'exponential_total': sum(1 << count for count in row_counts),
            'exponential_budget': 1 << k}


def reconstruct(metadata, values):
    private_cost = validate_selected_model(metadata, values)
    n, k = metadata['n'], metadata['and_cap']
    abstract_gates, abstract_output = selected_regions(metadata, values)
    gates, source_wires, or_cache = [], list(range(n)), {}

    def add(op, a, b):
        assert a != b
        assert 0 <= a < n + len(gates) and 0 <= b < n + len(gates)
        wire = n + len(gates)
        gates.append({'op': op, 'inputs': [a, b]})
        return wire

    def make_or(wires):
        atoms = frozenset(w for w in wires if w is not None)
        if not atoms:
            return None
        if atoms in or_cache:
            return or_cache[atoms]
        ordered = sorted(atoms)
        result, prefix = ordered[0], {ordered[0]}
        or_cache[frozenset(prefix)] = result
        for wire in ordered[1:]:
            prefix.add(wire)
            key = frozenset(prefix)
            if key in or_cache:
                result = or_cache[key]
            elif result == wire:
                or_cache[key] = result
            else:
                result = add('or', result, wire)
                or_cache[key] = result
        return result

    for left, right in abstract_gates:
        a = make_or(source_wires[j] for j in left)
        b = make_or(source_wires[j] for j in right)
        if a is None or b is None:
            source_wires.append(None)
        elif a == b:
            source_wires.append(a)
        else:
            source_wires.append(add('and', a, b))
    output = make_or(source_wires[j] for j in abstract_output)
    if output is None:
        raise RuntimeError('a graph with positive edges cannot have a false output')

    # Remove dead gates and renumber only after all OR sharing has been resolved.
    needed, todo = set(), [output]
    while todo:
        wire = todo.pop()
        if wire < n or wire - n in needed:
            continue
        needed.add(wire - n)
        todo.extend(gates[wire - n]['inputs'])
    mapping = {i: i for i in range(n)}
    live = []
    for i, gate in enumerate(gates):
        if i in needed:
            mapped = [mapping[w] for w in gate['inputs']]
            mapping[n + i] = n + len(live)
            live.append({'op': gate['op'], 'inputs': mapped})
    output = mapping[output]
    and_count = sum(g['op'] == 'and' for g in live)
    or_count = sum(g['op'] == 'or' for g in live)
    assert and_count <= k and or_count <= private_cost
    edges = metadata['edges']
    for row in range(1 << n):
        wires = [bool(row & (1 << i)) for i in range(n)]
        for i, gate in enumerate(live):
            a, b = gate['inputs']
            assert 0 <= a < n + i and 0 <= b < n + i and a != b
            wires.append(wires[a] and wires[b] if gate['op'] == 'and' else wires[a] or wires[b])
        expected = any((row & (1 << a)) and (row & (1 << b)) for a, b in edges)
        if wires[output] != expected:
            raise RuntimeError(f'reconstructed circuit disagrees at input {row}')
    literal = '⟨[' + ','.join('⟨.' + g['op'] + ',[' + ','.join(map(str, g['inputs'])) + ']⟩'
                              for g in live) + '],' + str(output) + '⟩'
    return {'n': n, 'gates': live, 'output': output, 'size': len(live),
            'and_count': and_count, 'or_count': or_count,
            'unshared_private_or_cost': private_cost,
            'exhaustively_checked_inputs': 1 << n, 'matches_graph': True,
            'lean_circuit_literal': literal}


def self_test():
    source, _ = generate(12, H12_EDGES, 5)
    assert hashlib.sha256(source.encode()).hexdigest() == H12_SHA256
    tests = []
    for name, n, edges, cap, expected in [
        ('single_edge', 2, [(0, 1)], 0, 'sat'),
        ('two_edge_star', 3, [(0, 1), (0, 2)], 1, 'sat'),
        ('square_private2', 4, [(0, 2), (0, 3), (1, 2), (1, 3)], 2, 'sat'),
        ('square_private1', 4, [(0, 2), (0, 3), (1, 2), (1, 3)], 1, 'unsat'),
    ]:
        smt, meta = generate(n, edges, 1, timeout_ms=5000, private_or_cap=cap)
        result = solve(smt, meta['selectors'])
        assert result['status'] == expected
        entry = {'name': name, 'status': result['status'], 'seconds': result['seconds']}
        if expected == 'sat':
            circuit = reconstruct(meta, result['selectors'])
            assert circuit['size'] <= 1 + cap
            entry.update(size=circuit['size'], checked=circuit['exhaustively_checked_inputs'])
        tests.append(entry)

    square = [(0, 2), (0, 3), (1, 2), (1, 3)]
    _, meta = generate(4, square, 2)
    def witness(gates, out):
        values = dict.fromkeys(meta['selectors'], False)
        for i, (left, right) in enumerate(gates):
            for j in left:
                values[f'l{i}_{j}'] = True
            for j in right:
                values[f'r{i}_{j}'] = True
        for j in out:
            values[f'out_{j}'] = True
        return reconstruct(meta, values)
    padded = witness([([], []), ([0, 1], [2, 3])], [4, 5])
    assert padded['size'] == 3 and padded['and_count'] == 1
    shared = witness([([0, 1], [2]), ([0, 1], [3])], [4, 5])
    assert shared['or_count'] == 2 and shared['unshared_private_or_cost'] == 3
    dead = witness([([0], [1]), ([0, 1], [2, 3])], [5])
    assert dead['size'] == 3 and dead['and_count'] == 1
    return {'h12_hash_calibration': H12_SHA256, 'tiny_solver_tests': tests,
            'false_padding_checked': True, 'identical_or_sharing_checked': True,
            'dead_gate_pruning_checked': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture', type=Path)
    parser.add_argument('--and-cap', type=int, default=6)
    parser.add_argument('--private-or-cap', type=int)
    parser.add_argument('--and-kraft', action='store_true')
    parser.add_argument('--timeout-ms', type=int, default=1200000)
    parser.add_argument('--smt-out', type=Path)
    parser.add_argument('--result-out', type=Path)
    parser.add_argument('--solve', action='store_true')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        print(json.dumps(self_test(), indent=2))
        return
    if args.fixture is None or args.smt_out is None:
        parser.error('--fixture and --smt-out are required outside --self-test')
    if args.solve and args.result_out is None:
        parser.error('--result-out is required with --solve')
    fixture = json.loads(args.fixture.read_text())
    source, meta = generate(fixture['n'], fixture['edges'], args.and_cap,
                            args.timeout_ms, args.private_or_cap, args.and_kraft)
    args.smt_out.write_text(source)
    result = {'fixture': fixture.get('name', args.fixture.name), 'model': meta}
    if args.solve:
        result['solver'] = solve(source, meta['selectors'])
        if result['solver']['status'] == 'sat':
            result['circuit'] = reconstruct(meta, result['solver']['selectors'])
            if args.and_kraft:
                result['and_kraft_counts'] = equal_operand_counts(meta, result['solver']['selectors'])
    if args.result_out is not None:
        args.result_out.write_text(json.dumps(result, indent=2) + '\n')
    summary = {'fixture': result['fixture'], 'scope': meta['scope'],
               'and_cap': args.and_cap, 'private_or_cap': args.private_or_cap,
               'edge_rows': len(meta['positive_rows']), 'MIS_rows': len(meta['negative_rows']),
               'smt_sha256': meta['smt_sha256'], 'smt_bytes': meta['smt_bytes'],
               'solver_status': result.get('solver', {}).get('status', 'not run')}
    if 'circuit' in result:
        summary.update(actual_size=result['circuit']['size'],
                       actual_and_count=result['circuit']['and_count'],
                       actual_or_count=result['circuit']['or_count'],
                       checked_inputs=result['circuit']['exhaustively_checked_inputs'])
    if args.and_kraft:
        summary.update(and_kraft=True, and_kraft_equal_budget=meta['and_kraft_equal_budget'])
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
