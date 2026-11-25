import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time


def geometry():
    edges = [(p, 13 + l) for p in range(13) for l in range(13)
             if (p + l) % 13 in (0, 1, 3, 9)]
    neighbors = [sum(1 << l for l in range(13)
                     if (p, 13 + l) in edges) for p in range(13)]
    negatives = set()
    for points in range(1 << 13):
        lines = (1 << 13) - 1
        for p in range(13):
            if points >> p & 1:
                lines &= ~neighbors[p]
        closed = sum(1 << p for p in range(13) if not neighbors[p] & lines)
        if points == closed:
            negatives.add(points | (lines << 13))
    positives = [(1 << p) | (1 << l) for p, l in edges]
    rows = positives + sorted(negatives)
    assert len(edges) == 52 and len(negatives) == 704
    assert len(rows) == len(set(rows)) == 756
    return edges, rows


def star_model(count, edges):
    records = []
    for j in range(count):
        records.append({'left': [j] if j < 13 else [],
                        'right': [l for p, l in edges if p == j] if j < 13 else []})
    return {'ands': records, 'output': list(range(min(count, 13)))}


def evaluate(model, rows):
    values = [sum(((row >> i) & 1) << k for k, row in enumerate(rows))
              for i in range(26)]
    for j, record in enumerate(model['ands']):
        sides = []
        for key in ('left', 'right'):
            selected = record[key]
            assert selected == sorted(set(selected))
            assert all(type(i) is int and 0 <= i < 26 + j for i in selected)
            side = 0
            for i in selected:
                side |= values[i]
            sides.append(side)
        values.append(sides[0] & sides[1])
    selected = model['output']
    assert selected == sorted(set(selected))
    assert all(type(i) is int and 0 <= i < len(model['ands']) for i in selected)
    output = 0
    for i in selected:
        output |= values[26 + i]
    return values, output


def materialize(model):
    gates = []
    wires = list(range(26))
    or_cache = {}

    def make_or(selected):
        terms = sorted({wires[i] for i in selected if wires[i] is not None})
        if not terms:
            return None
        key = tuple(terms)
        if key in or_cache:
            return or_cache[key]
        current = terms[0]
        for k, term in enumerate(terms[1:], start=2):
            prefix = tuple(terms[:k])
            if prefix in or_cache:
                current = or_cache[prefix]
            else:
                gates.append([1, current, term])
                current = 26 + len(gates) - 1
                or_cache[prefix] = current
        or_cache[key] = current
        return current

    for record in model['ands']:
        left = make_or(record['left'])
        right = make_or(record['right'])
        if left is None or right is None:
            wires.append(None)
        elif left == right:
            wires.append(left)
        else:
            gates.append([0, left, right])
            wires.append(26 + len(gates) - 1)
    output = make_or([26 + j for j in model['output']])
    if output is None:
        return {'gates': [], 'output': None, 'constant_false': True, 'size': 0}
    live = {output}
    for j in range(len(gates) - 1, -1, -1):
        if 26 + j in live:
            live.update(gates[j][1:])
    rename = {i: i for i in range(26)}
    pruned = []
    for j, (op, left, right) in enumerate(gates):
        if 26 + j in live:
            rename[26 + j] = 26 + len(pruned)
            pruned.append([op, rename[left], rename[right]])
    return {'gates': pruned, 'output': rename[output],
            'constant_false': False, 'size': len(pruned)}


def ordinary_eval(circuit, rows):
    if circuit['constant_false']:
        return 0
    values = [sum(((row >> i) & 1) << k for k, row in enumerate(rows))
              for i in range(26)]
    for op, left, right in circuit['gates']:
        assert op in (0, 1) and 0 <= left < len(values) and 0 <= right < len(values)
        values.append(values[left] | values[right] if op else values[left] & values[right])
    return values[circuit['output']]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--ands', type=int, default=12)
    parser.add_argument('--prefix', required=True)
    parser.add_argument('--seconds', type=int, default=10)
    parser.add_argument('--fixed-star-prefix', type=int, default=0)
    parser.add_argument('--fix-output', action='store_true')
    parser.add_argument('--emit-only', action='store_true')
    args = parser.parse_args()
    assert 1 <= args.ands <= 64 and 0 <= args.fixed_star_prefix <= args.ands
    resource.setrlimit(resource.RLIMIT_AS, (4 * 1024 ** 3, 4 * 1024 ** 3))
    base = Path(args.prefix)
    base.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    edges, rows = geometry()
    warm = star_model(args.ands, edges)
    warm_values, warm_output = evaluate(warm, rows)
    target = (1 << 52) - 1
    assert ordinary_eval(materialize(warm), rows) == warm_output
    clauses = []
    preferred = {}

    def fresh(value):
        variable = len(preferred) + 1
        preferred[variable] = bool(value)
        return variable

    def add(*literals):
        assert all(type(x) is int and x != 0 for x in literals)
        clauses.append(list(literals))

    left = []
    right = []
    values = []
    for j in range(args.ands):
        selectors = []
        for key in ('left', 'right'):
            selectors.append([fresh(i in warm['ands'][j][key]) for i in range(26 + j)])
        left.append(selectors[0])
        right.append(selectors[1])
        for left_selector, right_selector in zip(selectors[0], selectors[1]):
            add(-left_selector, -right_selector)
        outputs = []
        for k, row in enumerate(rows):
            side_values = []
            for selected, key in zip(selectors, ('left', 'right')):
                terms = [selected[i] for i in range(26) if row >> i & 1]
                for i in range(j):
                    s = selected[26 + i]
                    v = values[i][k]
                    term = fresh(preferred[s] and preferred[v])
                    add(-term, s)
                    add(-term, v)
                    add(term, -s, -v)
                    terms.append(term)
                side = fresh(any((warm_values[i] >> k) & 1
                                 for i in warm['ands'][j][key]))
                for term in terms:
                    add(-term, side)
                add(-side, *terms)
                side_values.append(side)
            a, b = side_values
            z = fresh(preferred[a] and preferred[b])
            add(-z, a)
            add(-z, b)
            add(z, -a, -b)
            outputs.append(z)
        values.append(outputs)
    output = [fresh(j in warm['output']) for j in range(args.ands)]
    for k in range(len(rows)):
        if k >= 52:
            for j in range(args.ands):
                add(-output[j], -values[j][k])
        else:
            terms = []
            for j in range(args.ands):
                s, v = output[j], values[j][k]
                term = fresh(preferred[s] and preferred[v])
                add(-term, s)
                add(-term, v)
                add(term, -s, -v)
                terms.append(term)
            add(*terms)
    active = [fresh(bool(warm_values[26 + j] & target)) for j in range(args.ands)]
    for j, active_record in enumerate(active):
        for positive_value in values[j][:52]:
            add(-positive_value, active_record)
        add(-active_record, *values[j][:52])
        if j > 0:
            add(-active_record, active[j - 1])
        for selected in (left[j], right[j]):
            for i, selector in enumerate(selected):
                add(-selector, active_record)
                if i >= 26:
                    add(-selector, active[i - 26])
        add(-output[j], active_record)
    for j in range(min(10, args.ands)):
        add(active[j])
    if args.ands < 10:
        add()
    add(left[0][0])
    add(right[0][13])
    for j in range(args.fixed_star_prefix):
        for selected, key in ((left[j], 'left'), (right[j], 'right')):
            for i, selector in enumerate(selected):
                add(selector if i in warm['ands'][j][key] else -selector)
    if args.fix_output:
        for j, selector in enumerate(output):
            add(selector if j in warm['output'] else -selector)
    flipped = {v for v, value in preferred.items() if value}

    def rename(literal):
        return -literal if abs(literal) in flipped else literal

    cnf = base.with_suffix('.cnf')
    with cnf.open('w') as stream:
        stream.write(f'p cnf {len(preferred)} {len(clauses)}\n')
        for clause in clauses:
            stream.write(' '.join(str(rename(x)) for x in clause) + ' 0\n')
    mapping = {'n': 26, 'and_bound': args.ands, 'rows': rows,
               'left': left, 'right': right, 'output': output,
               'values': values, 'active': active, 'flipped_variables': sorted(flipped)}
    base.with_suffix('.mapping.json').write_text(json.dumps(mapping, indent=2) + '\n')
    base.with_suffix('.warm.json').write_text(json.dumps(warm, indent=2) + '\n')
    warm_errors = (warm_output ^ target).bit_count()
    record = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'and_bound': args.ands, 'rows': len(rows), 'variables': len(preferred),
              'clauses': len(clauses), 'fixed_star_prefix': args.fixed_star_prefix,
              'fix_output': args.fix_output, 'seconds_limit': args.seconds,
              'warm_boundary_errors': warm_errors,
              'conversion_seconds': time.monotonic() - started,
              'scope': 'AND-count synthesis with free OR subsets; ordinary gate cost measured after decoding',
              'disjoint_source_subsets': True, 'active_records_form_prefix': True,
               'minimum_active_records': 10, 'first_and_anchor': {'left': 0, 'right': 13},
               'inactive_records_empty_unreferenced': True, 'Lean_verified': False}
    if args.emit_only:
        record['status'] = 'CNF emitted; solver not run'
        base.with_suffix('.json').write_text(json.dumps(record, indent=2) + '\n')
        print(json.dumps(record), flush=True)
        return
    executable = '/tmp/oec/pequalnp-pilot-121/toolchain/lean-4.36.0-linux/bin/cadical'
    signal_received = None
    with base.with_suffix('.stdout').open('w') as stdout, base.with_suffix('.stderr').open('w') as stderr:
        proc = subprocess.Popen([executable, '--phase=false', '-t', str(args.seconds),
                                 '-w', str(base.with_suffix('.sol')), str(cnf)],
                                stdout=stdout, stderr=stderr, start_new_session=True)
        base.with_suffix('.process.json').write_text(json.dumps(
            {'wrapper_pid': os.getpid(), 'solver_pid': proc.pid, 'prefix': str(base)}, indent=2) + '\n')

        def stop(sig, frame):
            nonlocal signal_received
            signal_received = sig
            if proc.returncode is not None:
                raise SystemExit(128 + sig)
            try:
                os.killpg(proc.pid, sig)
            except ProcessLookupError:
                pass

        signal.signal(signal.SIGTERM, stop)
        proc.wait()
    record['exit_code'] = proc.returncode
    if signal_received is not None:
        record['status'] = 'interrupted'
        record['signal'] = signal_received
    elif proc.returncode == 10:
        assignment = {}
        for line in base.with_suffix('.sol').read_text().splitlines():
            if line.startswith('v '):
                for literal in map(int, line[2:].split()):
                    if literal:
                        assignment[abs(literal)] = literal > 0
        assert set(assignment) == set(preferred)
        assert all(any(assignment[abs(rename(x))] == (rename(x) > 0)
                       for x in clause) for clause in clauses)
        original = {i: (not value if i in flipped else value)
                    for i, value in assignment.items()}
        assert all(any(original[abs(x)] == (x > 0) for x in clause) for clause in clauses)
        model = {'ands': [{'left': [i for i, v in enumerate(left[j]) if original[v]],
                           'right': [i for i, v in enumerate(right[j]) if original[v]]}
                          for j in range(args.ands)],
                 'output': [j for j, v in enumerate(output) if original[v]]}
        base.with_suffix('.and-model.json').write_text(json.dumps(model, indent=2) + '\n')
        model_values, value = evaluate(model, rows)
        actual_active = [bool(model_values[26 + j] & target) for j in range(args.ands)]
        assert actual_active == [original[v] for v in active]
        assert sum(actual_active) >= 10
        assert actual_active == sorted(actual_active, reverse=True)
        assert 0 in model['ands'][0]['left'] and 13 in model['ands'][0]['right']
        for j, node in enumerate(model['ands']):
            assert not set(node['left']) & set(node['right'])
            if not actual_active[j]:
                assert node['left'] == node['right'] == [] and j not in model['output']
            for i in node['left'] + node['right']:
                assert i < 26 or actual_active[i - 26]
        circuit = materialize(model)
        base.with_suffix('.ordinary.json').write_text(json.dumps(circuit, indent=2) + '\n')
        actual = ordinary_eval(circuit, rows)
        assert actual == value
        assert sum(op == 0 for op, _, _ in circuit['gates']) <= args.ands
        errors = (actual ^ target).bit_count()
        record.update({'status': 'SAT; complete boundary passed; Lean verification required'
                       if errors == 0 else 'INVALID decoded boundary',
                       'clauses_verified': len(clauses), 'boundary_errors': errors,
                       'ordinary_size': circuit['size'],
                       'ordinary_ands': sum(op == 0 for op, _, _ in circuit['gates']),
                       'ordinary_within63': circuit['size'] <= 63 and errors == 0})
    elif proc.returncode == 20:
        record['status'] = 'UNSAT; external solver only, no Lean lower bound'
    elif proc.returncode == 0:
        record['status'] = 'UNKNOWN; time or resource limit'
    else:
        record['status'] = 'solver error'
    record['elapsed_seconds'] = time.monotonic() - started
    record['max_rss_kb'] = max(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                              resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
    base.with_suffix('.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record), flush=True)
    if signal_received is not None:
        raise SystemExit(128 + signal_received)


if __name__ == '__main__':
    main()
