from pathlib import Path
import argparse
import hashlib
import json
import random
import resource
import shutil
import subprocess
import time

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
parser = argparse.ArgumentParser()
parser.add_argument('--round', type=int, required=True)
parser.add_argument('--changes', type=int, default=5)
parser.add_argument('--seconds', type=int, default=110)
parser.add_argument('--all-tests', action='store_true')
parser.add_argument('--seed-file', default='geometry-core-search7901-best.json')
parser.add_argument('--generate-only', action='store_true')
args = parser.parse_args()
assert 0 <= args.changes <= 58 and 1 <= args.seconds <= 110
data_file = job / 'geometry-meta3773-core-data.json'
seed_file = job / args.seed_file
assert seed_file.parent == job
bindings = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in [data_file, seed_file]}
data = json.loads(data_file.read_text())
seed = json.loads(seed_file.read_text())
n = data['n']
gate_count = len(seed['gates'])
assert n == 24 and gate_count == 60 and len(data['rows']) == 737

def bit(words, index):
    return bool(words[index // 64] >> (index % 64) & 1)

selected_file = job / 'meta3773-core-sat-selected.json'
selected = set(range(data['positive_count']))
selected.update(random.Random(7903).sample(range(data['positive_count'], len(data['rows'])), 64))
if selected_file.exists():
    selected.update(json.loads(selected_file.read_text()))
if args.all_tests:
    selected.update(range(len(data['rows'])))
tests = sorted(selected)
stem = 'meta3773-core-sat-r' + str(args.round)
counter = 0
clause_count = 0

def fresh():
    global counter
    counter += 1
    return counter

body = job / (stem + '.body')
with body.open('w') as handle:
    def clause(*literals):
        global clause_count
        handle.write(' '.join(map(str, literals)) + ' 0\n')
        clause_count += 1

    def choice(size):
        variables = [fresh() for _ in range(size)]
        prefixes = [fresh() for _ in range(size)]
        clause(-prefixes[0], variables[0])
        clause(prefixes[0], -variables[0])
        for i in range(1, size):
            clause(-prefixes[i - 1], prefixes[i])
            clause(-variables[i], prefixes[i])
            clause(prefixes[i - 1], variables[i], -prefixes[i])
            clause(-prefixes[i - 1], -variables[i])
        clause(prefixes[-1])
        return variables, prefixes

    gates = []
    values = []
    deviations = []
    for i in range(gate_count):
        left, left_prefix = choice(n + i)
        right, right_prefix = choice(n + i)
        operation, deviation = fresh(), fresh()
        deviations.append(deviation)
        seed_op, sa, sb = seed['gates'][i]
        sa, sb = sorted([sa, sb])
        assert 0 <= sa < sb < n + i
        clause(deviation, left[sa])
        clause(deviation, right[sb])
        clause(deviation, operation if seed_op else -operation)
        clause(-right[0])
        for j in range(1, n + i):
            clause(-right[j], left_prefix[j - 1])
        output = []
        sample_vars = []
        for position, row in enumerate(tests):
            a, b, y = fresh(), fresh(), fresh()
            output.append(y)
            sample_vars.append([a, b, y])
            sample = data['rows'][row]
            for selectors, value in [(left, a), (right, b)]:
                for wire, select in enumerate(selectors):
                    if wire < n:
                        clause(-select, value if sample >> wire & 1 else -value)
                    else:
                        earlier = values[wire - n][position]
                        clause(-select, -value, earlier)
                        clause(-select, value, -earlier)
            clause(-a, -b, y)
            clause(a, b, -y)
            clause(-operation, a, -y)
            clause(-operation, b, -y)
            clause(operation, -a, y)
            clause(operation, -b, y)
        values.append(output)
        gates.append({'left': left, 'right': right, 'left_prefix': left_prefix,
            'right_prefix': right_prefix, 'and': operation, 'deviation': deviation,
            'sample_vars': sample_vars})
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
    output_selectors = []
    for k in range(3):
        selectors, _ = choice(n + gate_count)
        output_selectors.append(selectors)
        for position, row in enumerate(tests):
            if not bit(data['care'][k], row):
                continue
            desired = bit(data['truth'][k], row)
            sample = data['rows'][row]
            for wire, select in enumerate(selectors):
                if wire < n:
                    if bool(sample >> wire & 1) != desired:
                        clause(-select)
                else:
                    value = values[wire - n][position]
                    clause(-select, value if desired else -value)
cnf = job / (stem + '.cnf')
with cnf.open('wb') as out, body.open('rb') as inp:
    out.write(('p cnf ' + str(counter) + ' ' + str(clause_count) + '\n').encode())
    shutil.copyfileobj(inp, out)
body.unlink()
for path in [data_file, seed_file]:
    assert hashlib.sha256(path.read_bytes()).hexdigest() == bindings[path.name]
metadata = {'bindings': bindings, 'tests': tests, 'variables': counter,
    'clauses': clause_count, 'gates': gates, 'outputs': output_selectors,
    'changes': args.changes, 'seed_file': seed_file.name}
(job / (stem + '-metadata.json')).write_text(json.dumps(metadata) + '\n')
print(json.dumps({'samples': len(tests), 'variables': counter,
    'clauses': clause_count, 'cnf_bytes': cnf.stat().st_size}), flush=True)
if args.generate_only:
    raise SystemExit(0)

def limits():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024 ** 3, 3 * 1024 ** 3))
    resource.setrlimit(resource.RLIMIT_CPU, (args.seconds + 5, args.seconds + 5))

solver = job / 'elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
start = time.monotonic()
with (job / (stem + '-solver.log')).open('w') as log:
    run = subprocess.run([str(solver), '-t', str(args.seconds), str(cnf)],
        stdout=log, stderr=subprocess.STDOUT, cwd=job,
        env={'PATH': '/usr/bin:/bin', 'LC_ALL': 'C.UTF-8'}, preexec_fn=limits,
        timeout=args.seconds + 15)
status = {'returncode': run.returncode, 'seconds': time.monotonic() - start,
    'samples': len(tests), 'max_changed_gates': args.changes}
if run.returncode == 10:
    literals = set()
    for line in (job / (stem + '-solver.log')).read_text().splitlines():
        if line.startswith('v '):
            literals.update(int(x) for x in line.split()[1:] if int(x) > 0)
    circuit = []
    for gate in gates:
        a = [i for i, x in enumerate(gate['left']) if x in literals]
        b = [i for i, x in enumerate(gate['right']) if x in literals]
        assert len(a) == len(b) == 1
        circuit.append([int(gate['and'] in literals), a[0], b[0]])
    outputs = []
    for selectors in output_selectors:
        chosen = [i for i, x in enumerate(selectors) if x in literals]
        assert len(chosen) == 1
        outputs.append(chosen[0])
    errors = []
    for row, sample in enumerate(data['rows']):
        wires = [bool(sample >> i & 1) for i in range(n)]
        for op, a, b in circuit:
            wires.append(wires[a] and wires[b] if op else wires[a] or wires[b])
        if any(bit(data['care'][k], row) and wires[outputs[k]] != bit(data['truth'][k], row)
                for k in range(3)):
            errors.append(row)
    assert not (set(errors) & selected)
    status['errors'] = len(errors)
    status['witness'] = not errors
    (job / (stem + '-candidate.json')).write_text(json.dumps({'inputs': n,
        'gates': circuit, 'outputs': outputs, 'errors': len(errors),
        'error_rows': errors, 'status': status}) + '\n')
    selected.update(errors[:32])
    selected_file.write_text(json.dumps(sorted(selected)) + '\n')
(job / (stem + '-status.json')).write_text(json.dumps(status, indent=2) + '\n')
print(json.dumps(status), flush=True)
