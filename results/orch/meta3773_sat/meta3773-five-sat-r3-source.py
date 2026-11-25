from pathlib import Path
import argparse
import hashlib
import json
import resource
import shutil
import subprocess
import time

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
parser = argparse.ArgumentParser()
parser.add_argument('--round', type=int, required=True)
parser.add_argument('--seconds', type=int, default=110)
parser.add_argument('--fixed-trees', action='store_true')
parser.add_argument('--no-colex', action='store_true')
parser.add_argument('--generate-only', action='store_true')
parser.add_argument('--gates', type=int, default=23)
parser.add_argument('--and-count', type=int)
args = parser.parse_args()
assert args.gates in [23, 24] and 1 <= args.seconds <= 110
assert args.and_count is None or 0 <= args.and_count <= args.gates

def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()

source_sha = sha(Path(__file__))
data_file = job / 'meta3773-five-patch-data.json'
data_sha = sha(data_file)
data = json.loads(data_file.read_text())
tests = [(mask, True) for mask in data['positive_raw_masks']] + [
    (mask, False) for mask in data['maximal_negative_raw_masks']]
assert len(tests) == len(set(mask for mask, _ in tests)) == 50
n = data['inputs_with_free_or_signals']
assert n == 32 and data['raw_inputs'] == 16
stem = 'meta3773-five-sat-r' + str(args.round)
(job / (stem + '-source.py')).write_bytes(Path(__file__).read_bytes())
variables = 0
clauses = 0

def fresh():
    global variables
    variables += 1
    return variables

body = job / (stem + '.body')
with body.open('w') as stream:
    def clause(*literals):
        global clauses
        stream.write(' '.join(map(str, literals)) + ' 0\n')
        clauses += 1

    def choice(count):
        selections = [fresh() for _ in range(count)]
        prefix = [fresh() for _ in range(count)]
        clause(-prefix[0], selections[0])
        clause(prefix[0], -selections[0])
        for i in range(1, count):
            clause(-prefix[i - 1], prefix[i])
            clause(-selections[i], prefix[i])
            clause(prefix[i - 1], selections[i], -prefix[i])
            clause(-prefix[i - 1], -selections[i])
        clause(prefix[-1])
        return selections, prefix

    def at_most(literals, bound):
        previous = None
        for literal in literals:
            current = [fresh() for _ in range(bound + 1)]
            clause(-literal, current[0])
            if previous is not None:
                for j in range(bound + 1):
                    clause(-previous[j], current[j])
                    if j:
                        clause(-literal, -previous[j - 1], current[j])
            clause(-current[-1])
            previous = current

    basis = [[None for _ in tests] for _ in range(16)]
    basis_aux = []
    tree_choices = []
    for group in data['outside_groups']:
        selections, _ = choice(len(group['variants']))
        tree_choices.append(selections)
        if args.fixed_trees:
            clause(selections[0])
        variant_values = []
        for variant in group['variants']:
            local_values = [[] for _ in variant]
            for sample_index, (sample, _) in enumerate(tests):
                values = {i: bool(sample >> i & 1) for i in range(16)}
                for j, (a, b) in enumerate(variant):
                    wire = group['first_free_wire'] + j
                    values[wire] = values[a] or values[b]
                    local_values[j].append(values[wire])
            variant_values.append(local_values)
        for j in range(len(group['variants'][0])):
            wire = group['first_free_wire'] + j
            for sample_index in range(len(tests)):
                truth = [values[j][sample_index] for values in variant_values]
                if all(truth):
                    value = True
                elif not any(truth):
                    value = False
                elif sum(truth) == 1:
                    value = selections[truth.index(True)]
                elif sum(truth) == len(truth) - 1:
                    value = -selections[truth.index(False)]
                else:
                    value = fresh()
                    basis_aux.append(value)
                    for selected, desired in zip(selections, truth):
                        clause(-selected, value if desired else -value)
                basis[wire - 16][sample_index] = value
    assert all(value is not None for row in basis for value in row)
    gates = []
    outputs = []
    previous_max = None
    leaf_occurrences = [[] for _ in range(n)]
    for gate_index in range(args.gates):
        left, left_prefix = choice(n + gate_index)
        right, right_prefix = choice(n + gate_index)
        operation = fresh()
        same_max = same_pair = None
        for wire in range(n):
            leaf_occurrences[wire].extend([left[wire], right[wire]])
        clause(-right[0])
        for j in range(1, n + gate_index):
            clause(-right[j], left_prefix[j - 1])
        if not args.no_colex and previous_max is not None:
            for j, previous in enumerate(previous_max):
                clause(-right[j], previous)
            previous_gate = gates[-1]
            same_max, same_pair = fresh(), fresh()
            for j, previous in enumerate(previous_gate['right']):
                clause(-previous, -right[j], same_max)
            for j, previous in enumerate(previous_gate['left_prefix']):
                clause(-same_max, -left[j], previous)
                clause(-same_max, -previous_gate['left'][j], -left[j], same_pair)
            clause(-same_pair, -previous_gate['and'])
            clause(-same_pair, operation)
        previous_max = right_prefix
        values = []
        sample_variables = []
        for sample_index, (sample, _) in enumerate(tests):
            a, b, y = fresh(), fresh(), fresh()
            values.append(y)
            sample_variables.append([a, b, y])
            for selections, target in [(left, a), (right, b)]:
                for wire, selected in enumerate(selections):
                    if wire < 16:
                        clause(-selected, target if sample >> wire & 1 else -target)
                    else:
                        value = basis[wire - 16][sample_index] if wire < n else outputs[wire - n][sample_index]
                        if isinstance(value, bool):
                            clause(-selected, target if value else -target)
                        else:
                            clause(-selected, -target, value)
                            clause(-selected, target, -value)
            clause(-a, -b, y)
            clause(a, b, -y)
            clause(-operation, a, -y)
            clause(-operation, b, -y)
            clause(operation, -a, y)
            clause(operation, -b, y)
        gates.append({'left': left, 'right': right, 'left_prefix': left_prefix,
            'right_prefix': right_prefix, 'and': operation, 'sample_variables': sample_variables,
            'same_max': same_max, 'same_pair': same_pair})
        outputs.append(values)
    for occurrences in leaf_occurrences[:16]:
        clause(*occurrences)
    if args.and_count is not None:
        at_most([gate['and'] for gate in gates], args.and_count)
        at_most([-gate['and'] for gate in gates], args.gates - args.and_count)
    for gate_index in range(args.gates - 1):
        wire = n + gate_index
        clause(*(variable for later in gates[gate_index + 1:]
            for variable in [later['left'][wire], later['right'][wire]]))
    for values in outputs:
        clause(*values[:len(data['positive_raw_masks'])])
    bad_flags = []
    if args.gates == 23:
        for gate, values in zip(gates, outputs):
            flag = fresh()
            bad_flags.append(flag)
            clause(-flag, gate['and'])
            clause(-flag, *values[len(data['positive_raw_masks']):])
        clause(*bad_flags)
    used_helpers = [fresh() for _ in range(16)]
    for used, occurrences in zip(used_helpers, leaf_occurrences[16:]):
        for occurrence in occurrences:
            clause(-occurrence, used)
        clause(-used, *occurrences)
    previous = None
    maximum_helpers = args.gates + 1 - 16
    for used in used_helpers:
        current = [fresh() for _ in range(maximum_helpers + 1)]
        clause(-used, current[0])
        if previous is not None:
            for j in range(maximum_helpers + 1):
                clause(-previous[j], current[j])
                if j:
                    clause(-used, -previous[j - 1], current[j])
        clause(-current[-1])
        previous = current
    for value, (_, desired) in zip(outputs[-1], tests):
        clause(value if desired else -value)

cnf = job / (stem + '.cnf')
with cnf.open('wb') as output, body.open('rb') as source:
    output.write(('p cnf ' + str(variables) + ' ' + str(clauses) + '\n').encode())
    shutil.copyfileobj(source, output)
body.unlink()
assert sha(data_file) == data_sha
metadata = {'data_sha256': data_sha, 'source_sha256': source_sha, 'cnf_sha256': sha(cnf),
    'tests': tests, 'variables': variables, 'clauses': clauses, 'gates': gates,
    'tree_choices': tree_choices, 'basis_variables': basis, 'maximum_helpers': maximum_helpers,
    'basis_auxiliary_variables': basis_aux,
    'fixed_trees': args.fixed_trees, 'colex': not args.no_colex,
    'all_gates_active': True, 'all_gates_positive_somewhere': True, 'bad_and_flags': bad_flags,
    'exact_and_count': args.and_count}
(job / (stem + '-metadata.json')).write_text(json.dumps(metadata) + '\n')
print(json.dumps({'variables': variables, 'clauses': clauses, 'samples': len(tests),
    'gate_budget': args.gates, 'free_tree_variants': [len(x) for x in tree_choices]}), flush=True)
if args.generate_only:
    raise SystemExit(0)

def limits():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024 ** 3, 3 * 1024 ** 3))
    resource.setrlimit(resource.RLIMIT_CPU, (args.seconds + 5, args.seconds + 5))

solver = job / 'elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
start = time.monotonic()
with (job / (stem + '-solver.log')).open('w') as log:
    try:
        run = subprocess.run([str(solver), '--sat', '--phase=false', '-t', str(args.seconds), str(cnf)],
            stdout=log, stderr=subprocess.STDOUT, cwd=job,
            env={'PATH': '/usr/bin:/bin', 'LC_ALL': 'C.UTF-8'}, preexec_fn=limits,
            timeout=args.seconds + 15)
        returncode = run.returncode
        outer_timeout = False
    except subprocess.TimeoutExpired:
        returncode = None
        outer_timeout = True
status = {'returncode': returncode, 'seconds': time.monotonic() - start,
    'outer_timeout': outer_timeout,
    'source_sha256': source_sha, 'cnf_sha256': metadata['cnf_sha256']}
assert sha(Path(__file__)) == source_sha and sha(cnf) == metadata['cnf_sha256']
if returncode == 10:
    true_literals = set()
    for line in (job / (stem + '-solver.log')).read_text().splitlines():
        if line.startswith('v '):
            true_literals.update(int(x) for x in line.split()[1:] if int(x) > 0)
    selected_trees = []
    for selectors in tree_choices:
        selected = [i for i, variable in enumerate(selectors) if variable in true_literals]
        assert len(selected) == 1
        selected_trees.append(selected[0])
    circuit = []
    for gate in gates:
        left = [i for i, variable in enumerate(gate['left']) if variable in true_literals]
        right = [i for i, variable in enumerate(gate['right']) if variable in true_literals]
        assert len(left) == len(right) == 1
        circuit.append([int(gate['and'] in true_literals), left[0], right[0]])
    width = 1 << 16
    all_ones = (1 << width) - 1
    raw = []
    for i in range(16):
        block = 1 << i
        raw.append((all_ones // ((1 << (2 * block)) - 1)) * ((1 << block) - 1) << block)
    words = list(raw)
    for group, selected in zip(data['outside_groups'], selected_trees):
        for j, (a, b) in enumerate(group['variants'][selected]):
            assert len(words) == group['first_free_wire'] + j
            words.append(words[a] | words[b])
    for operation, a, b in circuit:
        words.append(words[a] & words[b] if operation else words[a] | words[b])
    target = 0
    for a, b in data['edges']:
        target |= raw[a] & raw[b]
    failures = (words[-1] ^ target).bit_count()
    status['all_65536_inputs_verified'] = failures == 0
    status['failed_inputs'] = failures
    assert failures == 0
    (job / (stem + '-candidate.json')).write_text(json.dumps({'gates': circuit,
        'selected_tree_variants': selected_trees, 'status': status}) + '\n')
(job / (stem + '-status.json')).write_text(json.dumps(status, indent=2) + '\n')
print(json.dumps(status), flush=True)
