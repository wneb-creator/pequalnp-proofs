import argparse
import json
from pathlib import Path
from resynthesize import run_window, evaluate
from subset_search import validate_basis


PROFILES = {
    8: [[3,7,11,15,19,23,25,27], [0,4,8,12,16,20,24,27],
        [1,4,7,10,13,16,19,23], [2,5,8,11,14,17,20,27]],
    9: [[2,5,8,11,14,17,20,23,27], [0,3,6,9,12,15,18,23,27],
        [0,3,6,9,12,15,18,21,24], [3,6,9,12,15,18,21,24,27]],
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('case', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--and-count', type=int, choices=[8,9], required=True)
    parser.add_argument('--seconds', type=int, default=180)
    parser.add_argument('--line-first', action='store_true')
    parser.add_argument('--order-sameop', action='store_true')
    args = parser.parse_args()
    data = json.loads(args.case.read_text())
    tests = validate_basis(data)
    new_to_old = list(range(data['inputs']))
    if args.line_first:
        k = len(data['original_rows'])
        new_to_old = list(range(k,data['inputs'])) + list(range(k))
        old_to_new = {old:new for new,old in enumerate(new_to_old)}
        tests = [(sum(1<<old_to_new[i] for i in range(data['inputs']) if mask>>i&1), label) for mask,label in tests]
    args.output.mkdir(exist_ok=True, parents=True)
    for i, positions in enumerate(PROFILES[args.and_count]):
        gates = [[0 if j in positions else 1, 0, 1] for j in range(28)]
        assert sum(g[0] == 0 for g in gates) == args.and_count
        name = f'and{args.and_count}-profile{i}'
        print(name, 'ANDpositions', positions, flush=True)
        answer = run_window(gates, tests, list(range(28)), args.output, name, args.seconds,
                            fixed_ops=True, ninputs=data['inputs'], ordered_inputs=True,
                            require_used=True, positive_live=True, or_incomparable=True,
                            allow_equal_and=False, and_incomparable=True, order_sameop=args.order_sameop)
        if answer is not None:
            answer = [[op,new_to_old[a] if a<data['inputs'] else a,new_to_old[b] if b<data['inputs'] else b] for op,a,b in answer]
            assert all(evaluate(answer,mask,data['inputs'])[-1] == any(mask>>a&1 and mask>>b&1 for a,b in data['edges'])
                       for mask in range(1<<data['inputs']))
            result = {'gates':answer, 'input_original':data['input_original'], 'original_rows':data['original_rows'], 'case':data['name']}
            (args.output/'FULL-SUBSET-WITNESS.json').write_text(json.dumps(result))
            print('FULL SUBSET WITNESS', name, flush=True)
            return


if __name__ == '__main__':
    main()
