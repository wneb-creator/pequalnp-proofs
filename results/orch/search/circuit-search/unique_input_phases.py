import argparse
import hashlib
import json
from pathlib import Path


def normalize(gates, permutation):
    mapping = dict(enumerate(permutation))
    pending, result = set(range(len(gates))), []
    while pending:
        choices = []
        for i in pending:
            op, a, b = gates[i]
            if a in mapping and b in mapping:
                a, b = sorted((mapping[a], mapping[b]))
                choices.append(((a, b, op == 'or'), i, [op, a, b]))
        _, i, gate = min(choices)
        mapping[14 + i] = 14 + len(result)
        result.append(gate)
        pending.remove(i)
    assert mapping[13 + len(gates)] == 13 + len(gates)
    return result


def evaluate(gates, rows):
    values = [[bool(mask >> i & 1) for mask in rows] for i in range(14)]
    for op, a, b in gates:
        assert op in ('and', 'or') and 0 <= a <= b < len(values)
        values.append([(x or y) if op == 'or' else (x and y)
                       for x, y in zip(values[a], values[b])])
    return values


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cnf', type=Path, required=True)
    parser.add_argument('--seed', type=Path, required=True)
    parser.add_argument('--automorphisms', type=Path, required=True)
    parser.add_argument('--prefix', type=Path, required=True)
    args = parser.parse_args()
    metadata = json.loads(args.cnf.with_suffix('.map.json').read_text())
    assert metadata['unique_input']['input'] == 0 and metadata['ninputs'] == 14
    gates = json.loads(args.seed.read_text())
    assert len(gates) == metadata['gates']
    automorphisms = json.loads(args.automorphisms.read_text())['automorphisms']
    edges = {tuple(sorted(edge)) for edge in metadata['edges']}
    target = lambda mask: any((mask >> a) & (mask >> b) & 1 for a, b in edges)
    rows = metadata['rows']
    critical = metadata['unique_input']['incident_edge_rows'] + metadata['unique_input']['critical_false_rows']
    candidates = []
    for permutation in automorphisms:
        assert sorted(permutation) == list(range(14))
        assert {tuple(sorted((permutation[a], permutation[b]))) for a, b in edges} == edges
        if sum(permutation[v] == 0 for _, a, b in gates for v in (a, b) if v < 14) != 1:
            continue
        candidate = normalize(gates, permutation)
        consumer = next(i for i, (_, a, b) in enumerate(candidate) if a == 0 or b == 0)
        op, a, other = candidate[consumer]
        assert a == 0 and other != 0
        values = evaluate(candidate, rows)
        if all(values[other][r] == (op == 'and') for r in critical):
            candidates.append(candidate)
    assert candidates
    gates = min(candidates, key=lambda program: [(a, b, op == 'or') for op, a, b in program])
    values = evaluate(gates, rows)
    mismatches = [i for i, mask in enumerate(rows) if values[-1][i] != target(mask)]
    assert len(mismatches) == 1 and target(rows[mismatches[0]])
    preferences = {}
    def prefer(variable, value):
        assert 0 < variable <= metadata['nv']
        assert variable not in preferences or preferences[variable] == bool(value)
        preferences[variable] = bool(value)
    for i, ((op, a, b), gate) in enumerate(zip(gates, metadata['structure'])):
        for j, variable in enumerate(gate['left']):
            prefer(variable, j == a)
        for j, variable in enumerate(gate['right']):
            prefer(variable, j == b)
        prefer(gate['op'], op == 'or')
        for key, truth in [('left_values', values[a]), ('right_values', values[b]), ('out', values[14 + i])]:
            for variable, value in zip(gate[key], truth):
                prefer(variable, value)
    violated, unresolved, satisfied = [], 0, 0
    for line in args.cnf.read_text().splitlines():
        if line.startswith(('c', 'p')):
            continue
        clause = list(map(int, line.split()))
        assert clause[-1] == 0
        clause = clause[:-1]
        if any(preferences.get(abs(lit)) == (lit > 0) for lit in clause if abs(lit) in preferences):
            satisfied += 1
        elif any(abs(lit) not in preferences for lit in clause):
            unresolved += 1
        else:
            violated.append(clause)
    assert violated == [[metadata['structure'][-1]['out'][mismatches[0]]]]
    full_rows = list(range(1 << 14))
    full_values = evaluate(gates, full_rows)[-1]
    full_errors = [mask for mask, value in zip(full_rows, full_values) if value != target(mask)]
    assert full_errors and all(target(mask) and not full_values[mask] for mask in full_errors)
    phases = Path(str(args.prefix) + '.phases')
    seed = Path(str(args.prefix) + '-seed.json')
    report = Path(str(args.prefix) + '-report.json')
    assert not any(path.exists() for path in (phases, seed, report))
    phases.write_text('\n'.join(str(variable if value else -variable)
                                for variable, value in sorted(preferences.items())) + '\n')
    seed.write_text(json.dumps(gates, indent=2) + '\n')
    result = {'cnf_sha256': hashlib.sha256(args.cnf.read_bytes()).hexdigest(),
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'original_seed_sha256': hashlib.sha256(args.seed.read_bytes()).hexdigest(),
              'automorphisms_sha256': hashlib.sha256(args.automorphisms.read_bytes()).hexdigest(),
              'phase_sha256': hashlib.sha256(phases.read_bytes()).hexdigest(),
              'eligible_automorphisms': len(candidates), 'phase_literals': len(preferences),
              'unphased_variables': metadata['nv'] - len(preferences),
              'boundary_mismatches': mismatches, 'missing_edge_mask': rows[mismatches[0]],
              'full_truth_assignments_checked': len(full_rows), 'full_errors': len(full_errors),
              'partially_assigned_clauses_satisfied': satisfied,
              'partially_assigned_clauses_unresolved': unresolved,
              'fully_falsified_clauses': violated,
              'scope': 'Soft preferences only. The normalized seed has one missing target edge and is not a witness.'}
    report.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
