import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


EDGES = [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13),
         (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12),
         (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
         (6, 8), (6, 9), (6, 11)]
CORE = [edge for edge in EDGES if 13 not in edge]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    assert not path.exists(), path
    path.write_text(json.dumps(value, indent=2) + '\n')


def evaluate(gates, mask):
    values = [bool(mask >> i & 1) for i in range(14)]
    for op, a, b in gates:
        assert op in ('and', 'or') and 0 <= a <= b < len(values)
        values.append(values[a] or values[b] if op == 'or' else values[a] and values[b])
    return values


def normalize_prefix(gates):
    mapping = {i: i for i in range(14)}
    pending = set(range(len(gates)))
    result = []
    while pending:
        choices = []
        for i in pending:
            op, a, b = gates[i]
            if a in mapping and b in mapping:
                a, b = sorted((mapping[a], mapping[b]))
                choices.append(((a, b, op == 'or'), i, [op, a, b]))
        assert choices
        _, i, gate = min(choices)
        mapping[14 + i] = 14 + len(result)
        result.append(gate)
        pending.remove(i)
    return result, mapping


def make_witness(missing=None):
    gates = []

    def gate(op, a, b):
        a, b = sorted((a, b))
        gates.append([op, a, b])
        return 13 + len(gates)

    stars = []
    for right in range(7, 13):
        neighbors = [a for a, b in CORE if b == right]
        assert len(neighbors) == 3
        total = gate('or', neighbors[0], neighbors[1])
        total = gate('or', total, neighbors[2])
        stars.append(gate('and', right, total))
    c = stars[0]
    for star in stars[1:]:
        c = gate('or', c, star)
    assert len(gates) == 23
    neighbors = [v for v in (1, 2, 4) if v != missing]
    factor = gate('or', neighbors[0], neighbors[1])
    if len(neighbors) == 3:
        factor = gate('or', factor, neighbors[2])
    prefix, mapping = normalize_prefix(gates)
    c, factor = mapping[c], mapping[factor]
    gates = prefix + [['and', 13, factor], ['or', c, 14 + len(prefix)]]
    errors = []
    for mask in range(1 << 14):
        values = evaluate(gates, mask)
        core = any(values[a] and values[b] for a, b in CORE)
        target = any(values[a] and values[b] for a, b in EDGES)
        expected = any(values[a] and values[b] for a, b in EDGES
                       if missing is None or (a, b) != (missing, 13))
        assert values[c] == core and values[-1] == expected
        if values[-1] != target:
            errors.append(mask)
    return dict(gates=gates, prefix_gates=len(prefix), core_wire=c,
                tail_factors=[13, factor], missing_edge=None if missing is None else [missing, 13],
                full_assignment_count=1 << 14, target_error_count=len(errors),
                target_error_masks=errors,
                scope='Exact full truth-table baseline or one-edge-missing seed; no synthesized witness.')


def read_cnf(path):
    lines = path.read_text().splitlines()
    assert lines[0].startswith('p cnf ')
    _, _, nv, count = lines[0].split()
    clauses = []
    for line in lines[1:]:
        if not line or line.startswith('c'):
            continue
        literals = list(map(int, line.split()))
        assert literals[-1] == 0 and 0 not in literals[:-1]
        clauses.append(literals[:-1])
    assert len(clauses) == int(count)
    return int(nv), clauses


def write_cnf(path, nv, clauses):
    assert not path.exists(), path
    with path.open('w') as stream:
        stream.write(f'p cnf {nv} {len(clauses)}\n')
        for clause in clauses:
            stream.write(' '.join(map(str, clause)) + ' 0\n')


def generate(base_encoder, output, gates):
    assert gates >= 3
    base = output.with_name(output.stem + '-base.cnf')
    assert not base.exists() and not output.exists()
    command = [sys.executable, str(base_encoder), '--gates', str(gates), '--no-canon',
               '--no-liveness', '--allow-trivial', '--allow-initial-repeats',
               '--no-lex-order', '--output', str(base)]
    log = output.with_name(output.stem + '-base-generation.log')
    with log.open('w') as stream:
        subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT, check=True)
    metadata = json.loads(base.with_suffix('.map.json').read_text())
    nv, clauses = read_cnf(base)
    assert metadata['nv'] == nv and metadata['clauses'] == len(clauses)
    assert metadata['ninputs'] == 14 and metadata['edges'] == [list(e) for e in EDGES]
    assert metadata['allow_initial_repeats'] and not metadata['lex_order']
    assert not metadata['canonical_prefix'] and not metadata['liveness']
    structure = metadata['structure']
    added = []

    def clause(*literals):
        assert 0 not in literals
        added.append(list(literals))

    # Only the prefix is lex-normalized. The fixed AND tail may use early wires
    # and therefore must not be compared with the last prefix gate.
    lex_aux = []
    for i in range(1, gates - 2):
        previous, current = structure[i - 1], structure[i]
        nv += 2
        equal_left, equal_right = nv - 1, nv
        lex_aux.append([i, equal_left, equal_right])
        dependent = current['right'][-1]
        for a in range(14 + i - 1):
            clause(-previous['left'][a], -current['left'][a], equal_left)
            clause(-previous['right'][a], -current['right'][a], equal_right)
            for b in range(a):
                clause(dependent, -previous['left'][a], -current['left'][b])
                clause(dependent, -equal_left, -previous['right'][a], -current['right'][b])
        clause(dependent, -equal_left, -equal_right, -previous['op'], current['op'])

    penultimate = 14 + gates - 2
    clause(-structure[-2]['op'])
    clause(structure[-1]['op'])
    clause(structure[-1]['right'][penultimate])
    clause(-structure[-1]['left'][penultimate])
    core_masks = [(1 << a) | (1 << b) for a, b in CORE]
    anchor_count = 0
    for mask in core_masks:
        r = metadata['rows'].index(mask)
        for wire, selected in enumerate(structure[-1]['left'][:penultimate]):
            if wire < 14:
                if not mask >> wire & 1:
                    clause(-selected)
                    anchor_count += 1
            else:
                clause(-selected, structure[wire - 14]['out'][r])
                anchor_count += 1
    clauses += added
    write_cnf(output, nv, clauses)
    metadata.update(nv=nv, clauses=len(clauses), cnf_file=str(output.resolve()),
                    cnf_sha256=digest(output), source_sha256=digest(Path(__file__)),
                    base_encoder=str(base_encoder.resolve()), base_encoder_sha256=digest(base_encoder),
                    base_cnf_sha256=digest(base), base_command=command,
                    anchored_tail=dict(prefix_gates=gates - 2, core_edges=CORE,
                                       core_rows=core_masks, prefix_only_lex=True,
                                       lex_aux=lex_aux, anchor_clauses=anchor_count,
                                       added_clauses=len(added), fixed_tail=['and', 'or'],
                                       scope='C OR (U AND V), with F0 <= C <= Heawood. Restricted sufficient family only.'))
    save(output.with_suffix('.map.json'), metadata)
    return dict(file=str(output), gates=gates, variables=nv, clauses=len(clauses),
                rows=len(metadata['rows']), prefix_gates=gates - 2,
                anchor_clauses=anchor_count, added_clauses=len(added))


def fix(base, witness_file, output):
    metadata = json.loads(base.with_suffix('.map.json').read_text())
    witness = json.loads(witness_file.read_text())
    nv, clauses = read_cnf(base)
    assert digest(base) == metadata['cnf_sha256']
    assert len(witness['gates']) == metadata['gates']
    for (op, a, b), gate in zip(witness['gates'], metadata['structure']):
        clauses.extend([[gate['left'][a]], [gate['right'][b]],
                        [gate['op'] if op == 'or' else -gate['op']]])
    write_cnf(output, nv, clauses)
    metadata.update(clauses=len(clauses), cnf_file=str(output.resolve()), cnf_sha256=digest(output),
                    fixed_witness_file=str(witness_file.resolve()), fixed_witness_sha256=digest(witness_file))
    save(output.with_suffix('.map.json'), metadata)


def verify(cnf, log, output):
    metadata = json.loads(cnf.with_suffix('.map.json').read_text())
    assert digest(cnf) == metadata['cnf_sha256']
    nv, clauses = read_cnf(cnf)
    assert (nv, len(clauses)) == (metadata['nv'], metadata['clauses'])
    assignment = {}
    for line in log.read_text().splitlines():
        if line.startswith('v '):
            for literal in map(int, line.split()[1:]):
                if literal:
                    assert abs(literal) <= nv
                    assert abs(literal) not in assignment or assignment[abs(literal)] == (literal > 0)
                    assignment[abs(literal)] = literal > 0
    assert len(assignment) == nv
    assert all(any(assignment[abs(literal)] == (literal > 0) for literal in clause) for clause in clauses)
    gates = []
    for gate in metadata['structure']:
        left = [i for i, variable in enumerate(gate['left']) if assignment[variable]]
        right = [i for i, variable in enumerate(gate['right']) if assignment[variable]]
        assert len(left) == len(right) == 1
        gates.append(['or' if assignment[gate['op']] else 'and', left[0], right[0]])
    assert gates[-2][0] == 'and' and gates[-1][0] == 'or'
    assert gates[-1][2] == 14 + len(gates) - 2
    core_wire = gates[-1][1]
    assert core_wire < gates[-1][2]
    for mask in range(1 << 14):
        values = evaluate(gates, mask)
        target = any(values[a] and values[b] for a, b in EDGES)
        core = any(values[a] and values[b] for a, b in CORE)
        assert values[-1] == target
        assert not core or values[core_wire]
        assert not values[core_wire] or target
    for row, mask in enumerate(metadata['rows']):
        values = evaluate(gates, mask)
        for i, gate in enumerate(metadata['structure']):
            assert assignment[gate['out'][row]] == values[14 + i]
    report = dict(status='VERIFIED', gates=gates, gate_count=len(gates), core_wire=core_wire,
                  checked_clauses=len(clauses), checked_assignments=1 << 14,
                  cnf_sha256=digest(cnf), log_sha256=digest(log), source_sha256=digest(Path(__file__)))
    save(output, report)
    return {key: value for key, value in report.items() if key != 'gates'}


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest='action', required=True)
    artifacts = sub.add_parser('artifacts')
    artifacts.add_argument('--directory', type=Path, required=True)
    encoding = sub.add_parser('generate')
    encoding.add_argument('--base-encoder', type=Path, required=True)
    encoding.add_argument('--gates', type=int, required=True)
    encoding.add_argument('--output', type=Path, required=True)
    fixing = sub.add_parser('fix')
    fixing.add_argument('--base', type=Path, required=True)
    fixing.add_argument('--witness', type=Path, required=True)
    fixing.add_argument('--output', type=Path, required=True)
    checking = sub.add_parser('verify')
    checking.add_argument('--cnf', type=Path, required=True)
    checking.add_argument('--log', type=Path, required=True)
    checking.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.action == 'artifacts':
        baseline = make_witness()
        save(args.directory / 'anchored-tail-baseline27.json', baseline)
        for missing in (1, 2, 4):
            save(args.directory / f'anchored-tail-seed26-missing-{missing}-13.json', make_witness(missing))
        result = dict(baseline_gates=len(baseline['gates']), seeds=3, full_checks_per_witness=1 << 14)
    elif args.action == 'generate':
        result = generate(args.base_encoder, args.output, args.gates)
    elif args.action == 'fix':
        fix(args.base, args.witness, args.output)
        result = dict(file=str(args.output))
    else:
        result = verify(args.cnf, args.log, args.output)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
