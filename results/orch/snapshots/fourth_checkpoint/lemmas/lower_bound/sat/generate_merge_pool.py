import argparse
import itertools
import json
from pathlib import Path

from global_synthesis import evaluate


parser = argparse.ArgumentParser()
parser.add_argument('problem', type=Path)
parser.add_argument('output', type=Path)
parser.add_argument('--include', type=Path)
args = parser.parse_args()
problem = json.loads(args.problem.read_text())
n, count = problem['inputs'], problem['max_gates']
rows = list(range(len(problem['original_rows'])))
neighbors = {p: sorted(b for a, b in problem['edges'] if a == p) for p in rows}
pool = json.loads(args.include.read_text()) if args.include else []
generated = 0
for size in range(2, len(rows) + 1):
    for group in itertools.combinations(rows, size):
        gates = []

        def join(wires):
            answer = wires[0]
            for value in wires[1:]:
                gates.append([1, *sorted((answer, value))])
                answer = n + len(gates) - 1
            return answer

        centers = join(list(group))
        adjacent = join(sorted(set().union(*(neighbors[p] for p in group))))
        gates.append([0, *sorted((centers, adjacent))])
        blocks = [n + len(gates) - 1]
        for p in rows:
            if p in group:
                continue
            adjacent = join(neighbors[p])
            gates.append([0, *sorted((p, adjacent))])
            blocks.append(n + len(gates) - 1)
        output = join(blocks)
        if len(gates) > count:
            continue
        original_size = len(gates)
        while len(gates) < count:
            gates.append([0, output, output])
            output = n + len(gates) - 1
        assert output == n + count - 1
        assert all(evaluate(gates, mask, n) for mask, label in problem['tests'] if label)
        errors = sum(evaluate(gates, mask, n) for mask, label in problem['tests'] if not label)
        entry = dict(group=group, gates=gates, output=output, size=count,
                     original_size=original_size, positive_errors=0,
                     negative_errors=errors, exact_witness=(errors == 0))
        pool.append(entry)
        generated += 1
        if errors == 0:
            args.output.with_name('MERGE-EXACT-WITNESS.json').write_text(json.dumps(entry))
args.output.write_text(json.dumps(pool))
print('Generated', generated, 'merged-row candidates; combined pool', len(pool))
