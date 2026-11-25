from pathlib import Path
import argparse
import hashlib
import json
import resource
import subprocess
import time

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
parser = argparse.ArgumentParser()
parser.add_argument('--stem', required=True)
parser.add_argument('--run', type=int, required=True)
parser.add_argument('--seconds', type=int, default=110)
parser.add_argument('--control29', action='store_true')
parser.add_argument('--generate-only', action='store_true')
args = parser.parse_args()
assert 1 <= args.seconds <= 110 and args.run >= 0
assert args.stem.startswith('meta3773-six-dense-')
assert all(c.isalnum() or c == '-' for c in args.stem)


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


source_path = Path(__file__)
source_sha = sha(source_path)
metadata_path = job / (args.stem + '-metadata.json')
original_path = job / (args.stem + '.cnf')
data_path = job / 'meta3773-six-dense-patch-data.json'
bindings = {str(path): sha(path) for path in [metadata_path, original_path, data_path]}
metadata = json.loads(metadata_path.read_text())
data = json.loads(data_path.read_text())
assert bindings[str(original_path)] == metadata['cnf_sha256']
assert bindings[str(data_path)] == metadata['data_sha256']
if args.control29:
    seed_path = job / 'meta3773-six-dense-known29.json'
    bindings[str(seed_path)] = sha(seed_path)
    circuit = json.loads(seed_path.read_text())
    selected_trees = [0] * len(data['outside_groups'])
    assert len(circuit) == 29
else:
    seed_path = job / 'meta3773-six-dense-matched-over-seed.json'
    bindings[str(seed_path)] = sha(seed_path)
    assert bindings[str(seed_path)] == metadata['near_seed_sha256']
    seed = json.loads(seed_path.read_text())
    circuit = metadata['near_seed_normalized']
    assert len(circuit) == 28
    selected_trees = []
    for group in data['outside_groups']:
        start = group['first_free_wire'] - 17
        count = len(group['variants'][0])
        actual = [sorted(pair) for pair in seed['free_ors'][start:start + count]]
        matches = [i for i, variant in enumerate(group['variants'])
            if [sorted(pair) for pair in variant] == actual]
        assert len(matches) == 1
        selected_trees.append(matches[0])

assert len(circuit) == len(metadata['gates'])
assignment = [False] * (metadata['variables'] + 1)
for selectors, selected in zip(metadata['tree_choices'], selected_trees):
    assert 0 <= selected < len(selectors)
    for i, variable in enumerate(selectors):
        assignment[variable] = i == selected
        assignment[selectors[-1] + 1 + i] = i >= selected

sample_wires = []
basis_auxiliary = set(metadata['basis_auxiliary_variables'])
for row, (sample, expected) in enumerate(metadata['tests']):
    values = [bool(sample >> i & 1) for i in range(17)]
    for group, selected in zip(data['outside_groups'], selected_trees):
        for a, b in group['variants'][selected]:
            truth = values[a] or values[b]
            expression = metadata['basis_variables'][len(values) - 17][row]
            if isinstance(expression, bool):
                assert expression == truth
            elif abs(expression) in basis_auxiliary:
                assignment[abs(expression)] = truth if expression > 0 else not truth
            else:
                assert (assignment[abs(expression)] if expression > 0 else
                    not assignment[abs(expression)]) == truth
            values.append(truth)
    sample_wires.append(values)

for index, (encoded, actual) in enumerate(zip(metadata['gates'], circuit)):
    operation, left, right = actual
    assert type(operation) is int and operation in [0, 1]
    assert type(left) is int and type(right) is int and 0 <= left < right < 30 + index
    for name, selected in [('left', left), ('right', right)]:
        for i, variable in enumerate(encoded[name]):
            assignment[variable] = i == selected
            assignment[encoded[name + '_prefix'][i]] = i >= selected
    assignment[encoded['and']] = bool(operation)
    if encoded['same_max'] is not None:
        previous_operation, previous_left, previous_right = circuit[index - 1]
        assignment[encoded['same_max']] = previous_right == right
        assignment[encoded['same_pair']] = previous_right == right and previous_left == left
    for values, (a_var, b_var, y_var) in zip(sample_wires, encoded['sample_variables']):
        a, b = values[left], values[right]
        y = a and b if operation else a or b
        assignment[a_var], assignment[b_var], assignment[y_var] = a, b, y
        values.append(y)

if metadata['bad_and_flags']:
    positive_count = len(data['positive_raw_masks'])
    bad = [i for i, gate in enumerate(circuit) if gate[0] and
        any(values[30 + i] for values in sample_wires[positive_count:])]
    assert bad
    assignment[metadata['bad_and_flags'][bad[0]]] = True

flips = {i for i in range(1, len(assignment)) if assignment[i]}
stem = 'meta3773-six-dense-phase-r' + str(args.run)
transformed = job / (stem + '.cnf')
checked = 0
with original_path.open() as source, transformed.open('w') as destination:
    for line in source:
        if line.startswith('p '):
            assert line.split() == ['p', 'cnf', str(metadata['variables']), str(metadata['clauses'])]
            destination.write(line)
            continue
        literals = [int(x) for x in line.split()]
        assert literals and literals[-1] == 0
        literals = literals[:-1]
        assert all(0 < abs(x) <= metadata['variables'] for x in literals)
        changed = [-x if abs(x) in flips else x for x in literals]
        assert [(-x if abs(x) in flips else x) for x in changed] == literals
        if args.control29:
            assert any(assignment[abs(x)] == (x > 0) for x in literals)
            assert any(x < 0 for x in changed)
        destination.write(' '.join(map(str, changed)) + ' 0\n')
        checked += 1
assert checked == metadata['clauses']
assert all(sha(Path(path)) == digest for path, digest in bindings.items())
transformed_sha = sha(transformed)
record = {'source_sha256': source_sha, 'bindings': bindings,
    'original_stem': args.stem, 'transformed_cnf_sha256': transformed_sha,
    'flipped_variables': sorted(flips), 'selected_seed_trees': selected_trees,
    'control29': args.control29, 'clauses_checked': checked}
(job / (stem + '-metadata.json')).write_text(json.dumps(record) + '\n')
(job / (stem + '-source.py')).write_bytes(source_path.read_bytes())
print(json.dumps({'clauses': checked, 'flipped_variables': len(flips),
    'known_control_every_clause_verified': args.control29}), flush=True)
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
        run = subprocess.run([str(solver), '--sat', '--phase=false', '-t', str(args.seconds),
            str(transformed)], stdout=log, stderr=subprocess.STDOUT, cwd=job,
            env={'PATH': '/usr/bin:/bin', 'LC_ALL': 'C.UTF-8'}, preexec_fn=limits,
            timeout=args.seconds + 15)
        returncode = run.returncode
        outer_timeout = False
    except subprocess.TimeoutExpired:
        returncode = None
        outer_timeout = True
status = {'returncode': returncode, 'seconds': time.monotonic() - start,
    'outer_timeout': outer_timeout, 'source_sha256': source_sha,
    'original_cnf_sha256': metadata['cnf_sha256'],
    'transformed_cnf_sha256': transformed_sha}
assert sha(source_path) == source_sha and sha(transformed) == transformed_sha
assert all(sha(Path(path)) == digest for path, digest in bindings.items())
if returncode == 10:
    signed_model = {}
    for line in (job / (stem + '-solver.log')).read_text().splitlines():
        if line.startswith('v '):
            for value in map(int, line.split()[1:]):
                if value:
                    assert abs(value) not in signed_model
                    signed_model[abs(value)] = value > 0
    assert set(signed_model) == set(range(1, metadata['variables'] + 1))
    original_model = {i: truth != (i in flips) for i, truth in signed_model.items()}
    original_checked = 0
    with original_path.open() as stream:
        for line in stream:
            if line.startswith('p '):
                continue
            literals = [int(x) for x in line.split()[:-1]]
            assert any(original_model[abs(x)] == (x > 0) for x in literals)
            original_checked += 1
    assert original_checked == metadata['clauses']
    selected_trees = []
    for choices in metadata['tree_choices']:
        selected = [i for i, variable in enumerate(choices) if original_model[variable]]
        assert len(selected) == 1
        selected_trees.append(selected[0])
    decoded = []
    for encoded in metadata['gates']:
        left = [i for i, variable in enumerate(encoded['left']) if original_model[variable]]
        right = [i for i, variable in enumerate(encoded['right']) if original_model[variable]]
        assert len(left) == len(right) == 1
        decoded.append([int(original_model[encoded['and']]), left[0], right[0]])
    if metadata.get('near_seed_normalized') is not None:
        changed = sum(a != b for a, b in zip(decoded, metadata['near_seed_normalized']))
        status['decoded_changed_gates'] = changed
        assert changed <= metadata['maximum_changes']
    width = 1 << 17
    ones = (1 << width) - 1
    raw = []
    for index in range(17):
        block = 1 << index
        raw.append((ones // ((1 << (2 * block)) - 1)) * ((1 << block) - 1) << block)
    words = raw.copy()
    for group, selected in zip(data['outside_groups'], selected_trees):
        for a, b in group['variants'][selected]:
            words.append(words[a] | words[b])
    for operation, a, b in decoded:
        words.append(words[a] & words[b] if operation else words[a] | words[b])
    target = 0
    for a, b in data['edges']:
        target |= raw[a] & raw[b]
    status['failed_physical_inputs'] = (target ^ words[-1]).bit_count()
    assert status['failed_physical_inputs'] == 0
    status['all_131072_inputs_verified'] = True
    (job / (stem + '-candidate.json')).write_text(json.dumps({'gates': decoded,
        'selected_tree_variants': selected_trees, 'status': status}) + '\n')
(job / (stem + '-status.json')).write_text(json.dumps(status, indent=2) + '\n')
print(json.dumps(status), flush=True)
