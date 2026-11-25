import argparse
import json
from pathlib import Path
from resynthesize import run_window, evaluate
from subset_search import validate_basis


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('case', type=Path)
    parser.add_argument('seeds', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--seconds', type=int, default=180)
    args = parser.parse_args()
    data = json.loads(args.case.read_text())
    seeds = json.loads(args.seeds.read_text())
    tests = validate_basis(data)
    seed = next(s for s in seeds if s['center'] == 6)
    original = seed['gates']
    profiles = [[0,4,8], [14,17,20], [27,28,29], [12,13,23], [2,6,10], [15,18,21]]
    args.output.mkdir(exist_ok=True, parents=True)
    for index, dropped in enumerate(profiles):
        assert all(original[i][0] == 1 for i in dropped)
        gates = [[gate[0],0,1] for i,gate in enumerate(original) if i not in dropped]
        assert len(gates) == data['max_gates']
        name = f'profile-{index:02}'
        print(name, 'dropped', dropped, 'ANDpositions', [i for i,g in enumerate(gates) if g[0] == 0], flush=True)
        answer = run_window(gates, tests, list(range(len(gates))), args.output, name,
                            args.seconds, fixed_ops=True, ninputs=data['inputs'], ordered_inputs=True,
                            require_used=True, positive_live=True, or_incomparable=True, allow_equal_and=True, and_incomparable=True)
        if answer is not None:
            assert all(evaluate(answer,mask,data['inputs'])[-1] == any(mask>>a&1 and mask>>b&1 for a,b in data['edges'])
                       for mask in range(1<<data['inputs']))
            result = {'gates':answer,'input_original':data['input_original'],'original_rows':data['original_rows'],'case':data['name']}
            (args.output/'FULL-SUBSET-WITNESS.json').write_text(json.dumps(result))
            print('FULL SUBSET WITNESS', name, flush=True)
            return


if __name__ == '__main__':
    main()
