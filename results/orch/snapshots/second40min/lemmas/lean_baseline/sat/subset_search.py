import argparse
import ast
import json
import re
from pathlib import Path
from resynthesize import run_window, evaluate


def validate_basis(data):
    n = data['inputs']
    k = len(data['original_rows'])
    edges = [tuple(e) for e in data['edges']]
    tests = [tuple(t) for t in data['tests']]
    assert len(data['input_original']) == n
    assert all(0 <= a < k <= b < n for a, b in edges)
    posted = json.loads(Path('/tmp/oec/pequalnp-pilot-57/assigned-gap.json').read_text())['gap']['statement']
    full_edges = ast.literal_eval(re.search(r'\(\[(.*?)\] : List', posted).group(0).split(' : List')[0][1:])
    mapped = {(data['input_original'][a], data['input_original'][b]) for a, b in edges}
    assert mapped == {(a,b) for a,b in full_edges if a in data['original_rows']}
    assert {(mask, label) for mask, label in tests if label} == {(1 << a | 1 << b, 1) for a, b in edges}
    neighbors = [sum(1 << (b-k) for a, b in edges if a == u) for u in range(k)]
    maximal = set()
    for points in range(1 << k):
        excluded = 0
        for u in range(k):
            if points >> u & 1:
                excluded |= neighbors[u]
        lines = ((1 << (n-k)) - 1) ^ excluded
        closure = sum(1 << u for u in range(k) if not neighbors[u] & lines)
        if closure == points:
            maximal.add((points | (lines << k), 0))
    assert {(mask, label) for mask, label in tests if not label} == maximal
    assert all(evaluate(data['seed']['gates'], mask, n)[-1] == bool(label) for mask, label in tests)
    return tests


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('cases', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--seconds', type=int, default=60)
    parser.add_argument('--names', nargs='+', default=['k4_p2', 'k6_p3', 'k3_p1', 'k5_p2'])
    parser.add_argument('--order-max', action='store_true')
    parser.add_argument('--and-count', type=int)
    parser.add_argument('--final-and', action='store_true')
    parser.add_argument('--positive-live', action='store_true')
    parser.add_argument('--or-incomparable', action='store_true')
    parser.add_argument('--and-incomparable', action='store_true')
    args = parser.parse_args()
    args.output.mkdir(exist_ok=True, parents=True)
    for name in args.names:
        data = json.loads((args.cases / (name + '.json')).read_text())
        tests = validate_basis(data)
        gates = data['seed']['gates'][:data['max_gates']]
        print(name, 'inputs', data['inputs'], 'gates', len(gates), 'tests', len(tests), flush=True)
        answer = run_window(gates, tests, list(range(len(gates))), args.output, name,
                            args.seconds, ninputs=data['inputs'], ordered_inputs=True, require_used=True, order_max=args.order_max,
                            and_count=args.and_count, final_op=0 if args.final_and else None, positive_live=args.positive_live,
                            or_incomparable=args.or_incomparable, allow_equal_and=args.or_incomparable or args.and_incomparable,
                            and_incomparable=args.and_incomparable)
        if answer is not None:
            n = data['inputs']
            assert all(evaluate(answer, mask, n)[-1] == any(mask >> a & 1 and mask >> b & 1 for a, b in data['edges'])
                       for mask in range(1 << n))
            result = {'gates': answer, 'input_original': data['input_original'], 'original_rows': data['original_rows'], 'case': name}
            (args.output / 'FULL-SUBSET-WITNESS.json').write_text(json.dumps(result))
            print('FULL SUBSET WITNESS', name, flush=True)
            return


if __name__ == '__main__':
    main()
