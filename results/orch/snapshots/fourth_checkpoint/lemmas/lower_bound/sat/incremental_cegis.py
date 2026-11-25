import argparse
import ctypes
import json
import random
import time
from pathlib import Path

from global_synthesis import CNF, canonicalize, emit, evaluate, evaluate_wires
from subset_cegis import stamp


LIBRARY = '/tmp/oec/pequalnp-pilot-57/libcadical.so'


class Solver:
    def __init__(self, seed=5700):
        self.lib = ctypes.CDLL(LIBRARY)
        for name in ['init', 'release', 'add', 'assume', 'freeze', 'solve', 'val',
                     'set_option', 'set_terminate']:
            setattr(self.lib, 'ccadical_' + name, getattr(self.lib, 'pilot_' + name))
        self.lib.ccadical_init.argtypes = []
        self.lib.ccadical_init.restype = ctypes.c_void_p
        for name, extra, result in [
            ('release', [], None), ('add', [ctypes.c_int], None),
            ('assume', [ctypes.c_int], None),
            ('freeze', [ctypes.c_int], None), ('solve', [], ctypes.c_int),
            ('val', [ctypes.c_int], ctypes.c_int),
            ('set_option', [ctypes.c_char_p, ctypes.c_int], None),
        ]:
            method = getattr(self.lib, 'ccadical_' + name)
            method.argtypes = [ctypes.c_void_p] + extra
            method.restype = result
        self.ptr = self.lib.ccadical_init()
        self.lib.ccadical_set_option(self.ptr, b'quiet', 1)
        self.lib.ccadical_set_option(self.ptr, b'seed', seed)
        self.deadline = float('inf')
        callback_type = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_void_p)
        self.callback = callback_type(lambda _: int(time.monotonic() >= self.deadline))
        self.lib.ccadical_set_terminate.argtypes = [ctypes.c_void_p, ctypes.c_void_p, callback_type]
        self.lib.ccadical_set_terminate.restype = None
        self.lib.ccadical_set_terminate(self.ptr, None, self.callback)

    def add(self, *clause):
        for lit in clause:
            self.lib.ccadical_add(self.ptr, lit)
        self.lib.ccadical_add(self.ptr, 0)

    def freeze(self, lit):
        self.lib.ccadical_freeze(self.ptr, abs(lit))

    def solve(self, seconds):
        self.deadline = time.monotonic() + seconds
        return self.lib.ccadical_solve(self.ptr)

    def truth(self, lit):
        return self.lib.ccadical_val(self.ptr, abs(lit)) * lit > 0

    def close(self):
        self.lib.ccadical_release(self.ptr)


class LiveCNF(CNF):
    def __init__(self, solver, variables, clauses, journal):
        self.solver = solver
        self.variables = variables
        self.clauses = clauses
        self.journal = journal

    def clause(self, *xs):
        if 1 in xs:
            return
        ys = tuple(dict.fromkeys(x for x in xs if x != -1))
        if any(-x in ys for x in ys):
            return
        self.solver.add(*ys)
        self.journal.write(' '.join(map(str, ys)) + ' 0\n')
        self.clauses += 1


def add_sample(cnf, selected, n, mask, label, phase_seed):
    wires = [1 if mask >> i & 1 else -1 for i in range(n)]
    hints = evaluate_wires(phase_seed, mask, n)
    for i, (op, sa, sb) in enumerate(selected):
        a = cnf.var(hints[phase_seed[i][1]])
        b = cnf.var(hints[phase_seed[i][2]])
        for selectors, value in ((sa, a), (sb, b)):
            for j, selector in enumerate(selectors):
                cnf.clause(-selector, -value, wires[j])
                cnf.clause(-selector, value, -wires[j])
        wires.append(cnf.ao_gate(op, a, b, hints[n + i]))
    cnf.clause(wires[-1] if label else -wires[-1])
    cnf.journal.flush()


def model(solver, selected):
    answer = []
    for op, sa, sb in selected:
        a = [j for j, lit in enumerate(sa) if solver.truth(lit)]
        b = [j for j, lit in enumerate(sb) if solver.truth(lit)]
        assert len(a) == len(b) == 1
        answer.append([int(solver.truth(op)), a[0], b[0]])
    return answer


def self_test():
    solver = Solver()
    solver.add(1, 2)
    solver.freeze(1)
    solver.freeze(2)
    assert solver.solve(5) == 10
    solver.add(-1)
    assert solver.solve(5) == 10
    assert not solver.truth(1) and solver.truth(-1)
    assert solver.truth(2) and not solver.truth(-2)
    solver.add(-2)
    assert solver.solve(5) == 20
    solver.close()
    stamp('INCREMENTAL C API SELF TEST PASSED')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('problem', type=Path, nargs='?')
    parser.add_argument('seeds', type=Path, nargs='?')
    parser.add_argument('output', type=Path, nargs='?')
    parser.add_argument('--index', type=int, default=15)
    parser.add_argument('--seconds', type=int, default=120)
    parser.add_argument('--rounds', type=int, default=50)
    parser.add_argument('--add', type=int, default=3)
    parser.add_argument('--seed', type=int, default=5781)
    parser.add_argument('--lex', action='store_true')
    parser.add_argument('--positive-incomparable', action='store_true')
    parser.add_argument('--retries', type=int, default=1)
    parser.add_argument('--seed-pool', type=Path)
    parser.add_argument('--initial-samples', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    data = json.loads(args.problem.read_text())
    pack = json.loads(args.seeds.read_text())
    start = pack[args.index]
    n, count = data['inputs'], data['max_gates']
    answer = [[op, *sorted((a, b))] for op, a, b in start['gates']]
    while len(answer) < count:
        last = n + len(answer) - 1
        answer.append([0, last, last])
    assert len(answer) == count
    if args.lex:
        answer = canonicalize(answer, n)
    samples = [(mask, label) for mask, label in data['tests'] if label]
    samples += [(0, 0)] + [(1 << i, 0) for i in range(n)]
    left = len(data['original_rows'])
    samples += [((1 << left) - 1, 0), (((1 << n) - 1) ^ ((1 << left) - 1), 0)]
    if args.initial_samples:
        restored = json.loads(args.initial_samples.read_text())
        for mask, label in restored:
            assert 0 <= mask < (1 << n)
            truth = any(mask >> a & 1 and mask >> b & 1 for a, b in data['edges'])
            assert bool(label) == truth
        samples += [tuple(entry) for entry in restored]
    samples = list(dict.fromkeys(samples))
    known = {mask for mask, _ in samples}
    rng = random.Random(args.seed)
    pool = []
    if args.seed_pool:
        seen = set()
        for entry in json.loads(args.seed_pool.read_text()):
            gates = entry['gates'] if isinstance(entry, dict) else entry
            if len(gates) != count:
                continue
            if not all(op in (0, 1) and 0 <= a < n + i and 0 <= b < n + i
                       for i, (op, a, b) in enumerate(gates)):
                continue
            gates = [[op, *sorted((a, b))] for op, a, b in gates]
            used = {parent for _, a, b in gates for parent in (a, b)}
            if not all(wire in used for wire in range(n + count - 1)):
                continue
            if not all(evaluate(gates, mask, n) == bool(label) for mask, label in samples):
                continue
            supports = [0] * (n + count)
            for t, (mask, label) in enumerate(data['tests']):
                if label:
                    for wire, value in enumerate(evaluate_wires(gates, mask, n)):
                        if value:
                            supports[wire] |= 1 << t
            if not all(supports[n + i] for i in range(count)):
                continue
            if args.positive_incomparable and any(
                    op and (not supports[a] & ~supports[b] or not supports[b] & ~supports[a])
                    for op, a, b in gates):
                continue
            if args.lex:
                gates = canonicalize(gates, n)
            key = tuple(tuple(gate) for gate in gates)
            if key in seen:
                continue
            seen.add(key)
            errors = sum(evaluate(gates, mask, n) != bool(label)
                         for mask, label in data['tests'])
            pool.append((errors, gates))
        pool.sort(key=lambda item: item[0])
        stamp('VALIDATED SEED POOL', len(pool))
        if pool and not all(evaluate(answer, mask, n) == bool(label) for mask, label in samples):
            answer = pool[0][1]
            stamp('RESTORED SAMPLE PHASE SEED', 'full_basis_errors', pool[0][0])
    args.output.mkdir(parents=True, exist_ok=True)
    path = args.output / 'initial.cnf'
    selected, variables, clauses = emit(path, count, samples, ninputs=n,
                                        order_max=args.lex, order_lex=args.lex,
                                        positive_live=True, phase_seed=answer,
                                        positive_incomparable=args.positive_incomparable)
    solver = Solver(args.seed)
    for op, sa, sb in selected:
        for lit in [op] + sa + sb:
            solver.freeze(lit)
    with path.open() as source:
        for line in source:
            if line.startswith('p'):
                continue
            solver.add(*[int(word) for word in line.split()[:-1]])
    journal = (args.output / 'added-clauses.txt').open('w')
    cnf = LiveCNF(solver, variables, clauses, journal)
    stamp('INITIAL', start.get('group'), 'samples', len(samples), 'variables', variables,
          'clauses', clauses)
    result = solver.solve(args.seconds)
    stamp('INITIAL SOLVER', result)
    if result != 10:
        return
    answer = model(solver, selected)
    for round_no in range(args.rounds):
        assert all(evaluate(answer, mask, n) == bool(label) for mask, label in samples)
        wrong = [(mask, label) for mask, label in data['tests']
                 if evaluate(answer, mask, n) != bool(label)]
        (args.output / f'candidate-{round_no}.json').write_text(json.dumps(answer))
        stamp('CANDIDATE', round_no, 'errors', len(wrong))
        if not wrong:
            (args.output / 'EXACT-WITNESS.json').write_text(json.dumps(answer))
            stamp('EXACT TARGET WITNESS', len(answer))
            break
        minimized = set()
        for mask, label in wrong:
            assert not label
            order = list(range(n))
            rng.shuffle(order)
            for j in order:
                small = mask & ~(1 << j)
                if evaluate(answer, small, n):
                    mask = small
            assert not any(mask >> u & 1 and mask >> v & 1 for u, v in data['edges'])
            assert mask not in known
            minimized.add(mask)
        chosen = sorted(minimized, key=lambda mask: (mask.bit_count(), mask))[:args.add]
        stamp('ADD', [(mask, mask.bit_count()) for mask in chosen])
        for mask in chosen:
            add_sample(cnf, selected, n, mask, 0, answer)
            samples.append((mask, 0))
            known.add(mask)
        (args.output / 'samples.json').write_text(json.dumps(samples))
        begin = time.monotonic()
        result = 0
        for errors, proposed in pool:
            if not all(evaluate(proposed, mask, n) == bool(label) for mask, label in samples):
                continue
            for (op, sa, sb), (kind, a, b) in zip(selected, proposed):
                for lit in [op if kind else -op, sa[a], sb[b]]:
                    solver.lib.ccadical_assume(solver.ptr, lit)
            pinned_result = solver.solve(5)
            stamp('PINNED SEED', 'full_basis_errors', errors, 'result', pinned_result)
            if pinned_result == 10:
                assert model(solver, selected) == proposed
                result = 10
                break
        if result != 10:
            for retry in range(args.retries):
                result = solver.solve(args.seconds)
                if result != 0:
                    break
                stamp('UNKNOWN', 'retry', retry + 1, 'of', args.retries)
        stamp('SOLVER', result, 'seconds', round(time.monotonic() - begin, 2),
              'variables', cnf.variables, 'clauses', cnf.clauses)
        if result != 10:
            break
        answer = model(solver, selected)
    journal.close()
    solver.close()


if __name__ == '__main__':
    main()
