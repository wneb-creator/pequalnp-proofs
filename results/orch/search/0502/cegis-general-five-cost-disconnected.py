import argparse
import gc
import hashlib
import importlib.util
import itertools
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time

HERE = Path('/tmp/oec/pequalnp-pilot-21/search')


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


f = module('disconnected_base', 'cegis-full.py')
h = module('disconnected_helpers', 'cegis-symbolic-five.py')
sw = module('disconnected_streaming', 'streaming_cnf.py')
formal_cost = module('general_formal_cost', 'formal_cost.py')
disconnected_colors = module('general_disconnected_colors', 'disconnected_parent_colors.py')
ROOT = HERE / 'general-five-reduced-cost-disconnected'
BASE = 15
INTERNAL = 9
GATES = 14


def row_values(c, ops, aa, bb, mask):
    values = [c.var() for _ in ops]
    for j, op in enumerate(ops):
        children = [c.var(), c.var()]
        for selectors, value in zip((aa[j], bb[j]), children):
            for k, selected in enumerate(selectors):
                if k < BASE:
                    truth = bool(mask >> k & 1) if k < 13 else k == 14
                    c.add(-selected, value if truth else -value)
                else:
                    source = values[k-BASE]
                    c.add(-selected, -source, value)
                    c.add(-selected, source, -value)
        a, b = children
        value = values[j]
        c.add(-op, -a, -b, value)
        c.add(-op, a, -value)
        c.add(-op, b, -value)
        c.add(op, a, b, -value)
        c.add(op, -a, value)
        c.add(op, -b, value)
    return values


def general_root_guards(c, ops, aa, bb):
    late = []
    for root in range(INTERNAL, GATES):
        c.add(-ops[root])
        # Outputs are external OR pairs over the nine-internal prefix.
        for selected in aa[root][BASE+INTERNAL:]+bb[root][BASE+INTERNAL:]:
            c.add(-selected)
        late.append([selectors[BASE+k] for selectors in (aa[root], bb[root])
                     for k in (6, 7, 8)])
    # Checked TwoPairs: at most one output can avoid the last three internals.
    for first, second in itertools.combinations(range(5), 2):
        c.add(*late[first], *late[second])


def encode(c, rows):
    ops = [c.var() for _ in range(GATES)]
    aa, bb = [], []
    for j in range(GATES):
        a = [c.var() for _ in range(BASE+j)]
        b = [c.var() for _ in a]
        c.one(a)
        c.one(b)
        # Repeated operands are allowed. Constants model nullary/unary gates
        # and the original evaluator's false invalid reads without renumbering.
        for x in range(len(a)):
            for y in range(x):
                c.add(-a[x], -b[y])
        aa.append(a)
        bb.append(b)
    # All internal positions may be renumbered because root parents are free.
    for j in range(INTERNAL-1):
        for x, selected in enumerate(bb[j]):
            for y in range(x):
                c.add(-selected, -bb[j+1][y])
    h.lex_internal(c, ops[:INTERNAL], aa[:INTERNAL], bb[:INTERNAL], 0)
    labels = [[c.var() for _ in range(13)] for _ in range(5)]
    for selectors in labels:
        c.one(selectors)
    for w in range(13):
        for i, j in itertools.combinations(range(5), 2):
            c.add(-labels[i][w], -labels[j][w])
    # Explicit verified plane automorphisms normalize any ordered line pair.
    c.add(labels[0][0])
    c.add(labels[1][1])
    general_root_guards(c, ops, aa, bb)
    disconnected_colors.disconnected_parents(c, aa, bb)
    # Any reconstructed <=38-gate full counterexample needs >=2 AND gates.
    for op in ops:
        c.add(*(other for other in ops if other != op))
    meta = [None]*13 + [(None, set()), (None, set())]
    supports = h.reachability(c, aa, bb, meta, [])
    for j, support in enumerate(supports[-5:]):
        for w, line in enumerate(f.LINES):
            for p in line:
                c.add(-labels[j][w], support[p])
        for excluded in itertools.combinations(range(13), 7):
            c.add(*(support[p] for p in range(13) if p not in excluded))
    for mask in rows:
        values = row_values(c, ops, aa, bb, mask)
        zero = [w for w, line in enumerate(f.LINES) if not any(mask >> p & 1 for p in line)]
        assert len(zero) <= 1
        for j, value in enumerate(values[-5:]):
            if zero:
                assigned = labels[j][zero[0]]
                c.add(value, assigned)
                c.add(-value, -assigned)
            else:
                c.add(value)
    complements = [8191 ^ sum(1 << p for p in line) for line in f.LINES]
    extremes = {mask: row_values(c, ops, aa, bb, mask)[-5:]
                for mask in sorted(set(complements) | {1 << p for p in range(13)})}
    for j in range(5):
        for w, line in enumerate(f.LINES):
            # Global upper bound, then the exact remaining nonordinary test.
            c.add(-labels[j][w], -extremes[complements[w]][j])
            c.add(-labels[j][w], *(-extremes[1 << p][j] for p in line))
    costs = formal_cost.exact_costs(c, ops, aa, bb, 13, {13: 0, 14: 5})
    c.add(*(row[5] for row in costs[-5:]))
    return ops, aa, bb, labels


def rebuild(encoded, labels):
    assert len(encoded) == GATES and len(set(labels)) == 5
    nodes = [('wire', p) for p in range(13)] + [('constant', False), ('constant', True)]
    gates = []
    for a, b, is_and in encoded:
        assert 0 <= a < len(nodes) and 0 <= b < len(nodes)
        x, y = nodes[a], nodes[b]
        if x[0] == 'constant':
            value = y if x[1] == is_and else x
        elif y[0] == 'constant':
            value = x if y[1] == is_and else y
        elif x == y:
            value = x
        else:
            gates.append((x[1], y[1], is_and))
            value = ('wire', 12+len(gates))
        nodes.append(value)
    outputs = [None]*13
    for j, w in enumerate(labels):
        kind, wire = nodes[BASE+INTERNAL+j]
        assert kind == 'wire', 'A band-correct target cannot be constant'
        outputs[w] = wire
    for w, output in enumerate(outputs):
        if output is not None:
            continue
        a, b, c, d = sorted(f.LINES[w])
        gates.append((a, b, False))
        first = 12+len(gates)
        gates.append((c, d, False))
        second = 12+len(gates)
        gates.append((first, second, False))
        outputs[w] = 12+len(gates)
    assert len(gates) <= 38 and all(isinstance(w, int) for w in outputs)
    return {'gates': gates, 'out': outputs, 'selected_line_labels': labels,
            'encoded_gates_with_constants': encoded,
            'scope': 'full original-band counterexample after independent scalar validation'}


def validate(result):
    errors = [0]*13
    global_differences = [0]*13
    selected = set(result['selected_line_labels'])
    for mask in range(8192):
        wires = [bool(mask >> p & 1) for p in range(13)]
        for a, b, is_and in result['gates']:
            assert 0 <= a < len(wires) and 0 <= b < len(wires)
            wires.append(wires[a] and wires[b] if is_and else wires[a] or wires[b])
        for w, line in enumerate(f.LINES):
            actual = wires[result['out'][w]]
            wanted = any(mask >> p & 1 for p in line)
            assert not actual or wanted
            global_differences[w] += actual != wanted
            if mask.bit_count() in (7, 8):
                errors[w] += actual != wanted
    assert not any(errors), errors
    assert all(global_differences[w] > 0 for w in selected)
    return {'original_band_rows': 3003, 'global_upper_rows': 8192,
            'band_errors_per_output': errors, 'global_differences_per_output': global_differences}


def digest(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1048576), b''):
            result.update(chunk)
    return result.hexdigest()


def main():
    parser = argparse.ArgumentParser(description='General five-output reduced query with checked formal-cost5 and disconnected-parent guards, full3003bandrows.')
    parser.add_argument('--seconds', type=int, default=5400)
    parser.add_argument('--prepare-only', action='store_true')
    args = parser.parse_args()
    ROOT.mkdir(exist_ok=True)
    started = time.monotonic()
    deadline = started+args.seconds
    cnf = ROOT/'query.cnf'
    log = ROOT/'query.log'
    proof = ROOT/'query.lrat.gz'
    c = sw.streaming_class(f.b.CNF, ROOT/'query.clauses.part')()
    ops, aa, bb, labels = encode(c, f.ROWS)
    c.save(cnf)
    counts = {'variables': c.n, 'clauses': len(c.cs), 'band_rows': len(f.ROWS)}
    print('PREPARED', json.dumps(counts), 'elapsed', round(time.monotonic()-started), flush=True)
    del c
    gc.collect()
    if args.prepare_only:
        return
    remaining = max(1, int(deadline-time.monotonic()))
    argv = [f.SOLVER, '--sat', '--lrat', '-t', str(remaining), str(cnf), str(proof)]
    interrupted = None
    lastnote = 0
    with log.open('w') as output:
        proc = subprocess.Popen(argv, stdout=output, stderr=subprocess.STDOUT,
                                preexec_fn=lambda: os.setpriority(os.PRIO_PROCESS, 0, 15))
        (ROOT/'query-pid.json').write_text(json.dumps({'solver_pid': proc.pid, 'runner_pid': os.getpid()})+'\n')
        while proc.poll() is None:
            now = time.monotonic()
            free = shutil.disk_usage(ROOT).free
            if (free < 6.5*2**30 or now >= deadline) and interrupted is None:
                interrupted = now
                proc.send_signal(signal.SIGINT)
                print('INTERRUPT', 'disk_floor' if free < 6.5*2**30 else 'budget', flush=True)
            if interrupted is not None and now-interrupted > 30 and proc.poll() is None:
                proc.terminate()
            if now-lastnote >= 60:
                print('RUNNING', 'elapsed', round(now-started), 'freeGiB', round(free/2**30, 2),
                      'proofMiB', round(proof.stat().st_size/2**20, 1) if proof.exists() else 0, flush=True)
                lastnote = now
            time.sleep(5)
        code = proc.wait()
    status, encoded, selections = f.b.extract(log, ops, aa, bb, labels)
    print('RESULT', status, 'exit', code, 'elapsed', round(time.monotonic()-started), flush=True)
    if status == 'sat':
        result = rebuild(encoded, selections[:5])
        result['validation'] = validate(result)
        rebuilt_costs = [1]*13
        for a, b, op in result['gates']:
            rebuilt_costs.append(min(rebuilt_costs[a], rebuilt_costs[b]) if op else min(5, rebuilt_costs[a]+rebuilt_costs[b]))
        result['formal_output_costs'] = [rebuilt_costs[o] for o in result['out']]
        assert max(result['formal_output_costs']) == 5
        (ROOT/'counterexample.json').write_text(json.dumps(result, indent=2)+'\n')
        print('FOUND_SCALAR_VERIFIED_ALL3003', 'gates', len(result['gates']), flush=True)
    elif status == 'unsat':
        record = {'status': 'UNSAT_GENERAL_FIVE_OUTPUT_DISCONNECTED_REDUCED_ENCODING',
                  'internal_gate_budget': 9, 'external_or_outputs': 5,
                  'parent_graph': 'arbitrary disconnected graph, by checked ConnectedCircuit',
                  'line_labels': 'all injective assignments modulo explicit ordered-line-pair symmetry',
                  'constants_and_repeated_operands': True, 'all9_internals_ordered': True,
                  'at_least_four_outputs_use_internal6_7_8': True,
                  'some_residual_output_formal_cost5': True,
                  'formal_cost_justification': 'Checked FalsePruning.some_large_cost; constant/copy cleanup cannot increase cost and eight appended direct outputs have cost4',
                  'last_three_guard_justification': 'Lean-checked TwoPairs.four_use_last_three',
                  'counts': counts, 'cnf': str(cnf), 'cnf_sha256': digest(cnf), 'proof': str(proof),
                  'scope': 'general five-output reduced problem, not the unrestricted thirteen-output posted theorem'}
        (ROOT/'unsat.json').write_text(json.dumps(record, indent=2)+'\n')
    print('FINISHED', flush=True)


if __name__ == '__main__':
    main()
