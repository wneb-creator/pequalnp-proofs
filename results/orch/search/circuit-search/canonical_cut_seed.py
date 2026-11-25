import argparse
import json
from pathlib import Path
from repair_neighborhood import normalize_gates

parser = argparse.ArgumentParser()
parser.add_argument('--mapping', type=Path, required=True)
parser.add_argument('--seed', type=Path, required=True)
parser.add_argument('--actions', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--variant', type=int)
args = parser.parse_args()
metadata = json.loads(args.mapping.read_text())
actions = json.loads(args.actions.read_text())
if args.variant is not None:
    actions = next(item for item in actions['variants'] if item['variant'] == args.variant)
original = normalize_gates(json.loads(args.seed.read_text()))
assert len(original) == metadata['gates']
ninputs = metadata['ninputs']
candidates = []
for permutation in actions['permutations']:
    mapping = {i: permutation[i] for i in range(ninputs)}
    pending = set(range(len(original)))
    result = []
    while pending:
        ready = []
        for i in pending:
            op, a, b = original[i]
            if a in mapping and b in mapping:
                a, b = sorted((mapping[a], mapping[b]))
                ready.append(((a, b, op == 'or'), i, [op, a, b]))
        _, i, gate = min(ready)
        mapping[ninputs + i] = ninputs + len(result)
        result.append(gate)
        pending.remove(i)
    assert mapping[ninputs + len(original) - 1] == ninputs + len(original) - 1
    candidates.append(result)
gates = min(candidates, key=lambda program: [(a, b, op == 'or') for op, a, b in program])
args.output.write_text(json.dumps(gates, indent=2) + '\n')
print(json.dumps({'automorphisms': len(candidates), 'first_gate': gates[0], 'gates': len(gates)}))
