import argparse
import hashlib
import json
from pathlib import Path


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('cnf', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    metadata = json.loads(args.cnf.with_suffix('.map.json').read_text())
    assert metadata.get('allow_initial_repeats') is True
    assert metadata.get('allow_trivial') is True
    assert metadata.get('canonical_prefix') is False
    assert metadata.get('liveness') is False, 'Do not require every correlated input signal'
    assert not metadata.get('ordered_max')
    assert not metadata.get('minimal') and metadata.get('minimal_prefix', 0) == 0
    assert not metadata.get('shadow_missing') and not metadata.get('dirty_and')
    assert metadata.get('prefix') is None
    assert not any(key in metadata for key in ('gate_liveness', 'support_coverage',
                                             'repair', 'auxiliary_prefix', 'fixed_smoke_gates'))
    ninputs, gates = metadata['ninputs'], metadata['gates']
    structure = metadata['structure']
    assert gates > 0 and len(structure) == gates
    for i, gate in enumerate(structure):
        assert len(gate['left']) == len(gate['right']) == ninputs + i
    if metadata.get('format') == 'joint-correlated-v1':
        assert sha256(args.cnf) == metadata['cnf_sha256']
        selectors = metadata['variant_selectors']
        assert len(selectors) == len(metadata['variants'])
        branches = [(selector, variant['data'])
                    for selector, variant in zip(selectors, metadata['variants'])]
    else:
        assert 'variant_selectors' not in metadata
        branches = [(None, metadata['correlated'])]
    clauses = []
    for i in range(gates - 1):
        wire = ninputs + i
        clauses.append([selector[wire] for later in structure[i + 1:]
                        for selector in (later['left'], later['right'])])
    gate_clauses = len(clauses)
    coverage = []
    for selector, data in branches:
        nreal = data['real_inputs']
        supports = [[i] for i in range(nreal)] + data.get(
            'free_or_supports', data.get('free_or_sums', []))
        assert len(supports) == ninputs
        assert all(s and all(isinstance(v, int) and 0 <= v < nreal for v in s)
                   for s in supports)
        edges = data['edges']
        assert edges and all(len(e) == 2 and e[0] != e[1]
                             and all(0 <= v < nreal for v in e) for e in edges)
        essential = sorted({v for edge in edges for v in edge})
        coverage.append({'selector': selector, 'essential_variables': essential})
        for variable in essential:
            inputs = [j for j, support in enumerate(supports) if variable in support]
            clause = [] if selector is None else [-selector]
            clause.extend(fanins[j] for gate in structure
                          for fanins in (gate['left'], gate['right']) for j in inputs)
            assert clause
            clauses.append(clause)
    lines = args.cnf.read_text().splitlines(keepends=True)
    headers = [i for i, line in enumerate(lines) if line.startswith('p cnf ')]
    assert len(headers) == 1
    header = headers[0]
    assert lines[header].split() == ['p', 'cnf', str(metadata['nv']), str(metadata['clauses'])]
    assert not args.output.exists() and not args.output.with_suffix('.map.json').exists()
    metadata['clauses'] += len(clauses)
    lines[header] = f'p cnf {metadata["nv"]} {metadata["clauses"]}\n'
    lines.extend(' '.join(map(str, clause)) + ' 0\n' for clause in clauses)
    metadata['gate_liveness'] = {'computed_only': True, 'clauses': gate_clauses}
    metadata['support_coverage'] = {
        'clauses': len(clauses) - gate_clauses,
        'branches': coverage,
        'base_sha256': sha256(args.cnf),
        'source_sha256': sha256(Path(__file__)),
        'scope': 'Prune unused gates and output-copy-pad; each essential underlying variable must occur in a consumed initial OR support. No liveness of every correlated signal is required.'}
    content = ''.join(lines)
    if metadata.get('format') == 'joint-correlated-v1':
        metadata['cnf_file'] = str(args.output.resolve())
        metadata['cnf_sha256'] = hashlib.sha256(content.encode()).hexdigest()
    args.output.write_text(content)
    args.output.with_suffix('.map.json').write_text(json.dumps(metadata, separators=(',', ':')) + '\n')
    print(json.dumps({'variables': metadata['nv'], 'clauses': metadata['clauses'],
                      'gate_liveness': metadata['gate_liveness'],
                      'support_coverage': metadata['support_coverage']}))


if __name__ == '__main__':
    main()
