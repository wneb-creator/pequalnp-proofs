from pathlib import Path
import argparse
import hashlib
import json
import os
import resource
import shutil
import subprocess
import time

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
parser = argparse.ArgumentParser()
parser.add_argument('--round', type=int, default=0)
parser.add_argument('--first', type=int, choices=range(4), default=1)
parser.add_argument('--seconds', type=int, default=110)
parser.add_argument('--gates', type=int, default=63)
parser.add_argument('--all-tests', action='store_true')
parser.add_argument('--generate-only', action='store_true')
parser.add_argument('--near-seed', type=Path)
parser.add_argument('--changes', type=int, default=5)
parser.add_argument('--colex', action='store_true')
parser.add_argument('--negative-level', type=int, choices=[0, 1], default=1)
parser.add_argument('--add-counterexamples', type=int, default=24)
parser.add_argument('--false-phase', action='store_true')
parser.add_argument('--sat-profile', action='store_true')
parser.add_argument('--extra-negatives', type=Path)
parser.add_argument('--all-active', action='store_true')
parser.add_argument('--bad-and', action='store_true')
args = parser.parse_args()
assert 1 <= args.seconds <= 120 and 1 <= args.gates <= 64
data_path = job / 'meta3773-synthesis-data.json'
data_sha = hashlib.sha256(data_path.read_bytes()).hexdigest()
data = json.loads(data_path.read_text())
seed = None
if args.near_seed is not None:
    seed = json.loads(args.near_seed.read_text())
    assert len(seed) == args.gates and 0 <= args.changes <= args.gates
negatives = data['negative_maximal']
assert 1 <= args.add_counterexamples <= 704
initial = [x for x in negatives if (x & 8191).bit_count() <= args.negative_level or
    (x >> 13).bit_count() <= args.negative_level]
selected_path = job / ('meta3773-whole-selected-' + str(args.first) + '.json')
selected = set(initial)
if selected_path.exists():
    selected.update(json.loads(selected_path.read_text()))
if args.all_tests:
    selected.update(negatives)
if args.extra_negatives is not None:
    extra = json.loads(args.extra_negatives.read_text())
    assert isinstance(extra, list) and set(extra) <= set(negatives)
    selected.update(extra)
tests = [(x, True) for x in data['positive']] + [(x, False) for x in sorted(selected)]
stem = 'meta3773-whole-' + str(args.first) + '-r' + str(args.round)
body = job / (stem + '.clauses')
counter = 0
clauses = 0

def fresh():
    global counter
    counter += 1
    return counter

with body.open('w') as handle:
    def clause(*values):
        global clauses
        handle.write(' '.join(map(str, values)) + ' 0\n')
        clauses += 1

    def choice(size):
        selections = [fresh() for _ in range(size)]
        prefix = [fresh() for _ in range(size)]
        clause(-prefix[0], selections[0])
        clause(prefix[0], -selections[0])
        for i in range(1, size):
            clause(-prefix[i - 1], prefix[i])
            clause(-selections[i], prefix[i])
            clause(prefix[i - 1], selections[i], -prefix[i])
            clause(-prefix[i - 1], -selections[i])
        clause(prefix[-1])
        return selections, prefix

    gates = []
    outputs = []
    deviations = []
    previous_right_prefix = None
    for gate in range(args.gates):
        count = 26 + gate
        left, lp = choice(count)
        right, rp = choice(count)
        operation = fresh()
        if args.colex and previous_right_prefix is not None:
            for j, previous in enumerate(previous_right_prefix):
                clause(-right[j], previous)
        previous_right_prefix = rp
        if seed is not None:
            deviation = fresh()
            deviations.append(deviation)
            op, a, b = seed[gate]
            assert op in ['and', 'or'] and 0 <= a < b < count
            clause(deviation, left[a])
            clause(deviation, right[b])
            clause(deviation, operation if op == 'and' else -operation)
            clause(-deviation, -left[a], -right[b], -operation if op == 'and' else operation)
        clause(-right[0])
        for j in range(1, count):
            clause(-right[j], lp[j - 1])
        if gate == 0:
            op, a, b = [(True, 0, 13), (False, 0, 1),
                (False, 0, 13), (False, 2, 13)][args.first]
            clause(operation if op else -operation)
            clause(left[a])
            clause(right[b])
        values = []
        for index, (sample, desired) in enumerate(tests):
            a, b, y = fresh(), fresh(), fresh()
            values.append(y)
            for selectors, selected_value in [(left, a), (right, b)]:
                for wire, select in enumerate(selectors):
                    if wire < 26:
                        clause(-select, selected_value if sample >> wire & 1 else -selected_value)
                    else:
                        value = outputs[wire - 26][index]
                        clause(-select, -selected_value, value)
                        clause(-select, selected_value, -value)
            clause(-a, -b, y)
            clause(a, b, -y)
            clause(-operation, a, -y)
            clause(-operation, b, -y)
            clause(operation, -a, y)
            clause(operation, -b, y)
        gates.append({'left': left, 'right': right, 'and': operation})
        outputs.append(values)
    if args.all_active:
        for i in range(args.gates - 1):
            wire = 26 + i
            clause(*(variable for later in gates[i + 1:]
                for variable in [later['left'][wire], later['right'][wire]]))
        for values in outputs:
            clause(*values[:52])
    if args.bad_and:
        assert args.all_active
        flags = []
        for gate, values in zip(gates, outputs):
            flag = fresh()
            flags.append(flag)
            clause(-flag, gate['and'])
            clause(-flag, *values[52:])
        clause(*flags)
    if deviations:
        previous = None
        for deviation in deviations:
            current = [fresh() for _ in range(args.changes + 1)]
            clause(-deviation, current[0])
            if previous is not None:
                for j in range(args.changes + 1):
                    clause(-previous[j], current[j])
                    if j:
                        clause(-deviation, -previous[j - 1], current[j])
            clause(-current[-1])
            previous = current
    for output, (_, desired) in zip(outputs[-1], tests):
        clause(output if desired else -output)

cnf = job / (stem + '.cnf')
with cnf.open('wb') as output, body.open('rb') as source:
    output.write(('p cnf ' + str(counter) + ' ' + str(clauses) + '\n').encode())
    shutil.copyfileobj(source, output)
body.unlink()
assert hashlib.sha256(data_path.read_bytes()).hexdigest() == data_sha
binding = {'data_sha256': data_sha, 'tests': tests, 'variables': counter,
    'clauses': clauses, 'gates': gates, 'cnf_sha256': hashlib.sha256(cnf.read_bytes()).hexdigest()}
binding['seed'] = seed
binding['max_deviations'] = args.changes if seed is not None else None
binding['colex_order'] = args.colex
binding['all_active'] = args.all_active
binding['bad_and'] = args.bad_and
(job / (stem + '-metadata.json')).write_text(json.dumps(binding) + '\n')
print(json.dumps({'tests': len(tests), 'variables': counter, 'clauses': clauses,
    'cnf_bytes': cnf.stat().st_size}), flush=True)
if args.generate_only:
    raise SystemExit(0)

def limits():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024 ** 3, 3 * 1024 ** 3))
    resource.setrlimit(resource.RLIMIT_CPU, (args.seconds + 5, args.seconds + 5))

solver = job / 'elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
solver_args = [str(solver), '-t', str(args.seconds)]
if args.false_phase:
    solver_args.append('--phase=false')
if args.sat_profile:
    solver_args.append('--sat')
solver_args.append(str(cnf))
start = time.monotonic()
with (job / (stem + '-solver.log')).open('w') as log:
    completed = subprocess.run(solver_args,
        stdout=log, stderr=subprocess.STDOUT, cwd=job,
        env={'PATH': '/usr/bin:/bin', 'LC_ALL': 'C.UTF-8'}, preexec_fn=limits,
        timeout=args.seconds + 15)
status = {'returncode': completed.returncode, 'seconds': time.monotonic() - start,
    'samples': len(tests), 'first_gate_case': args.first}
log_text = (job / (stem + '-solver.log')).read_text()
if completed.returncode == 10:
    literals = set()
    for line in log_text.splitlines():
        if line.startswith('v '):
            literals.update(int(x) for x in line.split()[1:] if int(x) > 0)
    circuit = []
    for gate in gates:
        left = [i for i, x in enumerate(gate['left']) if x in literals]
        right = [i for i, x in enumerate(gate['right']) if x in literals]
        assert len(left) == len(right) == 1 and left[0] < right[0]
        circuit.append(['and' if gate['and'] in literals else 'or', left[0], right[0]])

    def evaluate(sample):
        wires = [bool(sample >> i & 1) for i in range(26)]
        for operation, a, b in circuit:
            wires.append(wires[a] and wires[b] if operation == 'and' else wires[a] or wires[b])
        return wires[-1]

    assert all(evaluate(sample) == desired for sample, desired in tests)
    false_negatives = [x for x in data['positive'] if not evaluate(x)]
    false_positives = [x for x in data['negative_full'] if evaluate(x)]
    assert not false_negatives
    status['false_positives'] = len(false_positives)
    status['witness'] = not false_positives
    (job / (stem + '-candidate.json')).write_text(json.dumps({'circuit': circuit,
        'false_positives': sorted(set(false_positives)), 'tested_original_negative_rows': 756,
        'status': status}) + '\n')
    selected.update(sorted(set(false_positives))[:args.add_counterexamples])
    selected_path.write_text(json.dumps(sorted(selected)) + '\n')
(job / (stem + '-status.json')).write_text(json.dumps(status, indent=2) + '\n')
print(json.dumps(status), flush=True)
