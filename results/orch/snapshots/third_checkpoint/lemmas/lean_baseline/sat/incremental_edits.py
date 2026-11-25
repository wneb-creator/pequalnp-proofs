import argparse
import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lower_bound' / 'sat'))
from global_synthesis import emit, evaluate
from incremental_cegis import Solver, LiveCNF, model
from subset_search import validate_basis


def stamp(*items):
    print(datetime.now(timezone.utc).isoformat(), *items, flush=True)


def threshold_row(cnf, literals, bound):
    row = [1] + [-1] * (bound + 1)
    for literal in literals:
        next_row = [1]
        for j in range(1, bound + 2):
            old, previous = row[j], row[j - 1]
            z = cnf.var(False)
            cnf.clause(-old, z)
            cnf.clause(-previous, -literal, z)
            cnf.clause(old, previous, -z)
            cnf.clause(old, literal, -z)
            next_row.append(z)
        row = next_row
    return row


def prepare(data, gates, directory, metric, maximum, seed):
    samples = validate_basis(data)
    n = data['inputs']
    assert all(op in (0, 1) and 0 <= a < n+i and 0 <= b < n+i
               for i, (op, a, b) in enumerate(gates))
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / 'initial.cnf'
    selected, variables, clauses = emit(path, len(gates), samples, ninputs=n,
                                        positive_live=True, phase_seed=gates)
    solver = Solver(seed)
    for op, sa, sb in selected:
        for lit in [op] + sa + sb:
            solver.freeze(lit)
    with path.open() as source:
        for line in source:
            if not line.startswith('p'):
                solver.add(*[int(word) for word in line.split()[:-1]])
    journal = (directory / 'edit-clauses.txt').open('w')
    cnf = LiveCNF(solver, variables, clauses, journal)
    changes = []
    for (op, sa, sb), (hint_op, hint_a, hint_b) in zip(selected, gates):
        differences = [-op if hint_op else op, -sa[hint_a], -sb[hint_b]]
        if metric == 'components':
            changes.extend(differences)
        else:
            changed = cnf.var(False)
            for difference in differences:
                cnf.clause(-difference, changed)
            cnf.clause(-changed, *differences)
            changes.append(changed)
    row = threshold_row(cnf, changes, maximum)
    for lit in row:
        solver.freeze(lit)
    journal.flush()
    stamp('PREPARED', len(gates), 'gates', len(samples), 'tests', metric,
          cnf.variables, 'variables', cnf.clauses, 'clauses')
    return solver, selected, row, journal


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('problem', type=Path)
    parser.add_argument('seeds', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--indices', type=int, nargs='+', default=[15])
    parser.add_argument('--metric', choices=['components', 'gates'], default='components')
    parser.add_argument('--minimum', type=int, default=7)
    parser.add_argument('--maximum', type=int, default=15)
    parser.add_argument('--seconds', type=int, default=30)
    parser.add_argument('--seed', type=int, default=5757)
    parser.add_argument('--calibrate', action='store_true')
    args = parser.parse_args()
    data = json.loads(args.problem.read_text())
    seeds = json.loads(args.seeds.read_text())
    for index in args.indices:
        start = seeds[index]
        gates = [[op, *sorted((a,b))] for op,a,b in
                 (data['seed']['gates'] if args.calibrate else start['gates'])]
        while len(gates) < data['max_gates']:
            last = data['inputs'] + len(gates) - 1
            gates.append([0, last, last])
        assert args.calibrate or len(gates) <= data['max_gates']
        folder = args.output / f'seed-{index}'
        stamp('SEED', index, start.get('group'), 'calibrate', args.calibrate)
        solver, selected, row, journal = prepare(data, gates, folder, args.metric,
                                                args.maximum, args.seed+index)
        for bound in range(args.minimum, args.maximum+1):
            solver.lib.ccadical_assume(solver.ptr, -row[bound+1])
            begin = time.monotonic()
            result = solver.solve(args.seconds)
            stamp('BOUND', bound, 'RESULT', result, 'seconds', round(time.monotonic()-begin,3))
            if result == 10:
                answer = model(solver, selected)
                differences = [[a != b for a,b in zip(gate, old)]
                               for gate,old in zip(answer,gates)]
                distance = sum(sum(d) if args.metric == 'components' else any(d)
                               for d in differences)
                assert distance <= bound, (distance,bound)
                assert all(evaluate(answer, mask, data['inputs']) == bool(label)
                           for mask,label in data['tests'])
                assert all(evaluate(answer, mask, data['inputs']) ==
                           any(mask >> a & 1 and mask >> b & 1 for a,b in data['edges'])
                           for mask in range(1 << data['inputs']))
                result = {'gates':answer, 'input_original':data['input_original'],
                          'original_rows':data['original_rows'], 'distance':distance,
                          'calibration':args.calibrate}
                if args.calibrate:
                    name = 'BASELINE-WITNESS.json'
                    status = 'CALIBRATION BASELINE'
                else:
                    assert len(answer) <= data['max_gates']
                    name = 'FULL-SUBSET-WITNESS.json'
                    status = 'EXACT TARGET WITNESS'
                (folder / name).write_text(json.dumps(result))
                stamp(status, len(answer), 'gates', 'distance', distance)
                break
        journal.close()
        solver.close()


if __name__ == '__main__':
    main()
