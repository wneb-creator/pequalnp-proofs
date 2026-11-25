import json
from pathlib import Path

P = Path(__file__).resolve().parent
old = Path('/tmp/oec/pequalnp-pilot-99/gap4970/counterexample')
small = [(old / 'variable' / ('seed-' + str(i) + '.graph.json'), old / 'variable' / ('seed-' + str(i) + '.circuit.json')) for i in range(10)]
large = small[:]
for name in ['subk4', 'irregular11', 'fano_minus_incident', 'fano_minus_nonincident', 'cubic16']:
    for d in range(3):
        large.append((old / 'stochastic' / (name + '.json'), old / 'stochastic' / (name + '-control.control' + str(d) + '.json')))

for n, p, sources in [(11, 5, small), (16, 8, large)]:
    dest = P / ('case' + str(n))
    dest.mkdir(exist_ok=True)
    data, provenance = [], []
    for index, (graph_file, circuit_file) in enumerate(sources):
        graph = json.loads(graph_file.read_text())
        circuit = json.loads(circuit_file.read_text())
        used = {v for edge in graph['edges'] for v in edge}
        left = sorted(v for v in used if v < graph['p'])
        right = sorted(v for v in used if v >= graph['p'])
        assert len(left) <= p and len(right) <= n - p
        mapping = {v: i for i, v in enumerate(left)} | {v: p + i for i, v in enumerate(right)}
        gates = []
        for j, (op, a, b) in enumerate(circuit['gates']):
            assert a in mapping and b in mapping
            gates.append([op, mapping[a], mapping[b]])
            mapping[graph['n'] + j] = n + j
        out = mapping[circuit['output']]
        mapped_graph = {'name': 'seed' + str(index), 'n': n, 'p': p, 'l': n-p,
                        'edges': [[mapping[a], mapping[b]] for a, b in graph['edges']], 'tau': graph['tau']}
        mapped_circuit = {'gates': gates, 'output': out}
        (dest / ('seed' + str(index) + '.graph.json')).write_text(json.dumps(mapped_graph, indent=2) + '\n')
        (dest / ('seed' + str(index) + '.circuit.json')).write_text(json.dumps(mapped_circuit, indent=2) + '\n')
        data.append(str(len(gates)) + ' ' + str(out) + '\n' + '\n'.join(' '.join(map(str, gate)) for gate in gates))
        provenance.append({'source_graph': str(graph_file), 'source_circuit': str(circuit_file), 'mapping': mapping})
    (dest / 'seeds.dat').write_text(str(len(data)) + '\n' + '\n'.join(data) + '\n')
    (dest / 'seed-provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
    print('PREPARED', n, 'inputs;', len(sources), 'seeds')
