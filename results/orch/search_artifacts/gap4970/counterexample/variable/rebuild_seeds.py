"""Reproduce seeds.dat and relabeled input seeds from frozen provenance."""
import json
from pathlib import Path

P = Path(__file__).resolve().parent
provenance = json.loads((P / 'seed-provenance.json').read_text())
data = []
for ix, source in enumerate(provenance):
    graph = json.loads(Path(source['source_graph']).read_text())
    circuit = json.loads(Path(source['source_circuit']).read_text())
    used = {v for edge in graph['edges'] for v in edge}
    left = sorted(v for v in used if v < graph['p'])
    right = sorted(v for v in used if v >= graph['p'])
    assert len(left) <= 5 and len(right) <= 6
    mapping = {v: i for i, v in enumerate(left)} | {v: 5 + i for i, v in enumerate(right)}
    gates = []
    for j, (op, a, b) in enumerate(circuit['gates']):
        assert a in mapping and b in mapping
        gates.append([op, mapping[a], mapping[b]])
        mapping[graph['n'] + j] = 11 + j
    assert mapping == {int(k): v for k, v in source['mapping'].items()}
    out = mapping[circuit['output']]
    data.append(str(len(gates)) + ' ' + str(out) + '\n' + '\n'.join(' '.join(map(str, gate)) for gate in gates))
expected = str(len(data)) + '\n' + '\n'.join(data) + '\n'
assert (P / 'seeds.dat').read_text() == expected
print('PASS:', len(data), 'seeds reproduced byte-for-byte from provenance')
