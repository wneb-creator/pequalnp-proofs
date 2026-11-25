import argparse
import hashlib
import json
from itertools import combinations
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('cnf', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    metadata = json.loads(args.cnf.with_suffix('.map.json').read_text())
    expected_edges = [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13),
                      (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12),
                      (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
                      (6, 8), (6, 9), (6, 11)]
    assert metadata['ninputs'] == 14
    assert sorted(map(tuple, metadata['edges'])) == sorted(expected_edges)
    assert metadata.get('canonical_prefix') is False and metadata.get('prefix') is None
    assert metadata.get('liveness') is True
    assert metadata.get('allow_initial_repeats') is True
    assert metadata.get('allow_trivial') is True
    assert not metadata.get('ordered_max')
    assert not metadata.get('minimal') and metadata.get('minimal_prefix', 0) == 0
    assert metadata.get('shadow_missing', 0) == 0 and not metadata.get('dirty_and')
    assert not any(key in metadata for key in ('unique_input', 'third_gate_symmetry',
                                             'repair', 'auxiliary_prefix', 'fixed_smoke_gates'))
    structure, rows = metadata['structure'], metadata['rows']
    assert metadata['gates'] == len(structure) and len(structure) > 0
    target = lambda mask: any((mask >> a) & (mask >> b) & 1 for a, b in expected_edges)
    incident = [i for i, mask in enumerate(rows) if target(mask) and mask & 1]
    critical_false = [i for i, mask in enumerate(rows) if not target(mask) and not mask & 1]
    assert len(rows) == 58 and len(incident) == 3 and len(critical_false) == 25
    assert all(target(rows[i] | 1) for i in critical_false)
    assert all(not target(rows[i] & ~1) for i in incident)
    critical = incident + critical_false
    occurrences = [side[0] for gate in structure for side in (gate['left'], gate['right'])]
    assert len(set(occurrences)) == len(occurrences)
    clauses = [occurrences]
    clauses.extend([-a, -b] for a, b in combinations(occurrences, 2))
    count_clauses = len(clauses)
    for i, gate in enumerate(structure):
        assert len(gate['left']) == len(gate['right']) == 14 + i
        assert len(gate['right_values']) == len(rows)
        consumer, op = gate['left'][0], gate['op']
        for row in critical:
            other = gate['right_values'][row]
            clauses.append([-consumer, op, other])
            clauses.append([-consumer, -op, -other])
    lines = args.cnf.read_text().splitlines(keepends=True)
    headers = [i for i, line in enumerate(lines) if line.startswith('p cnf ')]
    assert len(headers) == 1
    header = headers[0]
    assert lines[header].split() == ['p', 'cnf', str(metadata['nv']), str(metadata['clauses'])]
    assert not args.output.exists() and not args.output.with_suffix('.map.json').exists()
    metadata['clauses'] += len(clauses)
    lines[header] = f'p cnf {metadata["nv"]} {metadata["clauses"]}\n'
    lines.extend(' '.join(map(str, clause)) + ' 0\n' for clause in clauses)
    metadata['unique_input'] = {
        'input': 0, 'counted_slots': len(occurrences),
        'exactly_one_clauses': count_clauses,
        'critical_row_clauses': len(clauses) - count_clauses,
        'incident_edge_rows': incident, 'critical_false_rows': critical_false,
        'critical_row_masks': [rows[i] for i in critical],
        'base_sha256': hashlib.sha256(args.cnf.read_bytes()).hexdigest(),
        'postprocessor_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope': 'Live circuits of at most 26 gates have a singly occurring input by the raw-occurrence count; Heawood transitivity maps it to 0. No full-group prefix restriction is present. Critical rows force the other fanin to NOT(op), where OR is true.'}
    args.output.write_text(''.join(lines))
    args.output.with_suffix('.map.json').write_text(json.dumps(metadata, separators=(',', ':')) + '\n')
    print(json.dumps({'variables': metadata['nv'], 'clauses': metadata['clauses'],
                      'unique_input': metadata['unique_input']}))


if __name__ == '__main__':
    main()
