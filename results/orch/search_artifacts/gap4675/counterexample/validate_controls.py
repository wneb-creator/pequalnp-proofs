import json
from pathlib import Path
import validate

P = Path(__file__).resolve().parent
results = []
for n, count in [(11, 10), (16, 25)]:
    case = P / ('case' + str(n))
    for i in range(count):
        source_graph = case / ('seed' + str(i) + '.graph.json')
        source_circuit = case / ('seed' + str(i) + '.circuit.json')
        graph = case / ('control.control' + str(i) + '.graph.json')
        circuit = case / ('control.control' + str(i) + '.circuit.json')
        source = validate.check(source_graph, source_circuit)
        saved = validate.check(graph, circuit)
        assert source['wrong_rows'] == source['tCount'] == saved['wrong_rows'] == saved['tCount'] == 0
        a, b = json.loads(source_graph.read_text()), json.loads(graph.read_text())
        assert (a['n'], a['p'], set(map(tuple, a['edges']))) == (b['n'], b['p'], set(map(tuple, b['edges'])))
        results.extend([source, saved])
        print('CONTROL', n, i, 'rows', saved['full_rows'], 'gates', saved['gates'], 'margin', saved['margin'],
              'COUNTEREXAMPLE', saved['is_counterexample'])
case = P / 'case11'
negative = validate.check(case / 'seed0.graph.json', case / 'pruning-probe.input.json')
positive = validate.check(case / 'pruning-probe.control0.graph.json', case / 'pruning-probe.control0.circuit.json')
assert negative['wrong_rows'] == positive['wrong_rows'] == 0
assert negative['tCount'] == 1 and positive['tCount'] == 0
assert negative['gates'] == positive['gates'] + 1
results.extend([negative, positive])
print('PRUNING CONTROL: actual saved circuit has T0 after removing and renumbering one dead mixed OR')
(P / 'control-validation.json').write_text(json.dumps(results, indent=2) + '\n')
print('TOTAL', len(results), 'full truth/certificate checks; counterexamples', sum(r['is_counterexample'] for r in results))
