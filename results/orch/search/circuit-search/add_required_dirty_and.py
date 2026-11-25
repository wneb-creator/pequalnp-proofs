import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('cnf', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    metadata = json.loads(args.cnf.with_suffix('.map.json').read_text())
    assert metadata['format'] == 'joint-correlated-v1'
    assert hashlib.sha256(args.cnf.read_bytes()).hexdigest() == metadata['cnf_sha256']
    assert not metadata.get('required_dirty_and')
    assert metadata['gates'] == len(metadata['structure']) and metadata['gates'] > 0
    targets = metadata['targets']
    assert targets and all(t in (0, 1) for t in targets)
    negative = [i for i, target in enumerate(targets) if target == 0]
    assert negative and any(targets)
    edges = [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13),
             (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12),
             (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
             (6, 8), (6, 9), (6, 11)]
    target = lambda mask: any((mask >> a) & (mask >> b) & 1 for a, b in edges)
    maximal_false = [mask for mask in range(1 << 14) if not target(mask)
                     and all(target(mask | (1 << v)) for v in range(14) if not mask >> v & 1)]
    assert len(maximal_false) == 37
    full_gate_counts = []
    for variant in metadata['variants']:
        data = variant['data']
        assert data['cut_inputs'] == metadata['ninputs']
        assert len(data['original_variables']) == data['real_inputs']
        assert len(set(data['original_variables'])) == data['real_inputs']
        full_gate_counts.append(len(data['fixed_gates']) + metadata['gates'] + 1)
        for mask in maximal_false:
            values = [bool(mask >> i & 1) for i in range(14)]
            for op, a, b in data['fixed_gates']:
                assert op in (0, 1) and 0 <= a < len(values) and 0 <= b < len(values)
                value = (values[a] or values[b]) if op == 1 else (values[a] and values[b])
                if op == 0:
                    assert not value, 'Fixed prefix has a dirty AND; cone-only necessity does not follow'
                values.append(value)
    variables = metadata['nv']
    clauses, witnesses = [], []
    for i, gate in enumerate(metadata['structure']):
        assert len(gate['out']) == len(targets)
        for row in negative:
            variables += 1
            witnesses.append({'variable': variables, 'gate': i, 'row': row})
            clauses.append([-variables, -gate['op']])
            clauses.append([-variables, gate['out'][row]])
    clauses.append([witness['variable'] for witness in witnesses])
    lines = args.cnf.read_text().splitlines(keepends=True)
    assert lines[0].split() == ['p', 'cnf', str(metadata['nv']), str(metadata['clauses'])]
    assert not args.output.exists() and not args.output.with_suffix('.map.json').exists()
    lines[0] = f'p cnf {variables} {metadata["clauses"] + len(clauses)}\n'
    lines.extend(' '.join(map(str, clause)) + ' 0\n' for clause in clauses)
    content = ''.join(lines)
    metadata.update(nv=variables, clauses=metadata['clauses'] + len(clauses),
                    cnf_file=str(args.output.resolve()),
                    cnf_sha256=hashlib.sha256(content.encode()).hexdigest())
    metadata['required_dirty_and'] = {
        'witnesses': witnesses, 'added_variables': len(witnesses), 'added_clauses': len(clauses),
        'full_gate_counts': full_gate_counts, 'fixed_prefix_and_clean_on_37_maximal_false_rows': True,
        'base_sha256': hashlib.sha256(args.cnf.read_bytes()).hexdigest(),
        'postprocessor_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope': 'Existence of a cone AND accepting a residual maximal-false row. Necessary for full circuits of at most26 gates in the independently reviewed fixed-star embeddings, by the clean-AND27 lower bound and monotonicity. Above26 gates this is only a deliberate smoke restriction.'}
    args.output.write_text(content)
    args.output.with_suffix('.map.json').write_text(json.dumps(metadata, separators=(',', ':')) + '\n')
    print(json.dumps({'variables': variables, 'clauses': metadata['clauses'],
                      'added_variables': len(witnesses), 'added_clauses': len(clauses),
                      'full_gate_counts': full_gate_counts,
                      'cnf_sha256': metadata['cnf_sha256']}))


if __name__ == '__main__':
    main()
