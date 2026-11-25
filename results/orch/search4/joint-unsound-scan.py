import itertools
import json
from pathlib import Path

ROOT = Path('/tmp/oec/pequalnp-pilot-66')
ARCHIVE = Path('/workspace/pequalnp-proofs/results/orch/search3')


def evaluate(n, gates, assignment, disabled):
    wires = [bool(assignment & (1 << i)) for i in range(n)]
    for j, (op, a, b) in enumerate(gates):
        wires.append(False if j in disabled else
                     (wires[a] and wires[b] if op == 'and' else wires[a] or wires[b]))
    return wires[-1]


def minimum_cover(n, edges):
    for count in range(n + 1):
        for subset in itertools.combinations(range(n), count):
            if all(a in subset or b in subset for a, b in edges):
                return list(subset)


def main():
    data = json.loads((ARCHIVE / 'model-validation.json').read_text())
    results = []
    for row in data['models']:
        path = ARCHIVE / row['file']
        model = json.loads(path.read_text())
        bad = []
        for j, (op, _, _) in enumerate(model['gates']):
            if op != 'and':
                continue
            for assignment in range(1 << model['n']):
                if any(assignment & (1 << a) and assignment & (1 << b) for a, b in model['edges']):
                    continue
                wires = [bool(assignment & (1 << i)) for i in range(model['n'])]
                for operation, a, b in model['gates']:
                    wires.append(wires[a] and wires[b] if operation == 'and' else wires[a] or wires[b])
                if wires[model['n'] + j]:
                    bad.append(j)
                    break
        if not bad:
            continue
        n, gates, edges = model['n'], model['gates'], model['edges']
        covers = {}
        candidates = {j: [] for j in bad}
        counts = {j: {size: 0 for size in range(1, min(6, len(gates) - 1) + 1)} for j in bad}
        tested = 0
        for size in range(1, min(6, len(gates) - 1) + 1):
            for chosen in itertools.combinations(range(len(gates)), size):
                selected_bad = [j for j in bad if j in chosen]
                if not selected_bad:
                    continue
                tested += 1
                lost = tuple(tuple(edge) for edge in edges
                             if not evaluate(n, gates, (1 << edge[0]) | (1 << edge[1]), chosen))
                if lost not in covers:
                    covers[lost] = minimum_cover(n, lost)
                cover = covers[lost]
                budget = len(lost) + len(cover) - 1 if lost else 1
                if budget <= size:
                    certificate = {'S': list(chosen), 'lost_edges': lost, 'minimum_cover': cover,
                                   'clean_budget': budget, 'selected_gate_count': size,
                                   'slack': size - budget}
                    for j in selected_bad:
                        candidates[j].append(certificate)
                        counts[j][size] += 1
        answer = {'model': path.name, 'gates': len(gates), 'unsound_ands': bad,
                  'subsets_tested': tested, 'results': []}
        for j in bad:
            found = candidates[j]
            best = sorted(found, key=lambda x: (x['selected_gate_count'], -x['slack'], x['S']))
            answer['results'].append({'unsound_and': j, 'counts_by_size': counts[j],
                                      'smallest_certificates': best[:12],
                                      'minimum_size': best[0]['selected_gate_count'] if best else None})
        results.append(answer)
    output = {'scope': 'Every proper subset of at most6 gates containing a unsound AND; '
                       'full simultaneous forced-false evaluation on every graph edge. '
                       'Clean circuit size is a star-cover upper bound, not minimum general circuit size.',
              'results': results}
    (ROOT / 'joint-unsound-results.json').write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps([{'model': r['model'], 'minimum_sizes':
                       [[x['unsound_and'], x['minimum_size']] for x in r['results']]}
                      for r in results]))


if __name__ == '__main__':
    main()
