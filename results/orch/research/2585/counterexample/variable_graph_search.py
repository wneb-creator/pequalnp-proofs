import itertools
import json
import random
import resource
import subprocess
import sys
import time
from pathlib import Path
from macro_count_search import CNF, OUT, SOLVER, boundary_rows


def build(P, count, assignments, family='c4free'):
    n = 2 * P
    c = CNF()
    edge = {(p, l): c.var() for p in range(P) for l in range(P)}
    for p in range(P):
        c.cl(edge[p, p])
    for p, q in itertools.combinations(range(P), 2):
        if family == 'c4free':
            for l, k in itertools.combinations(range(P), 2):
                c.cl(-edge[p, l], -edge[p, k], -edge[q, l], -edge[q, k])
        elif family == 'fooling':
            c.cl(-edge[p, q], -edge[q, p])
        else:
            raise ValueError(family)
    # Relabel the matched pairs simultaneously so left degrees are increasing.
    # This preserves the diagonal matching, C4-freeness, and every full-function
    # counterexample; circuit gates can then be topologically reordered again.
    degrees = []
    for p in range(P):
        variables = [edge[p, l] for l in range(P)]
        row = []
        for j in range(1, P + 1):
            ge = c.var()
            for subset in itertools.combinations(variables, j):
                c.cl(*(-v for v in subset), ge)
            for subset in itertools.combinations(variables, P - j + 1):
                c.cl(*subset, -ge)
            row.append(ge)
        degrees.append(row)
    for earlier, later in zip(degrees, degrees[1:]):
        for a, b in zip(earlier, later):
            c.cl(-a, b)
    selectors = []
    for i in range(count):
        a = [c.var() for _ in range(n + i)]
        b = [c.var() for _ in range(n + i)]
        c.cl(*a)
        c.cl(*b)
        equal = c.var()
        c.cl(equal)
        for av, bv in zip(reversed(a), reversed(b)):
            c.cl(-equal, -av, bv)
            nxt = c.var()
            c.cl(-equal, av, bv, nxt)
            c.cl(-equal, -av, -bv, nxt)
            c.cl(-nxt, equal)
            c.cl(-nxt, -av, bv)
            c.cl(-nxt, av, -bv)
            equal = nxt
        selectors.append((a, b))
    final = [c.var() for _ in range(n + count)]
    c.cl(*final)
    for i in range(count):
        c.cl(final[n + i], *(operand[n + i]
             for later in selectors[i + 1:] for operand in later))
    for (a, b), (aa, bb) in zip(selectors, selectors[1:]):
        for j in range(len(a)):
            c.cl(-a[j], *(aa[j:] + bb[j:]))
            c.cl(-b[j], *(aa[j:] + bb[j:]))
    for x in sorted(assignments):
        values = [bool(x >> i & 1) for i in range(n)]
        for a, b in selectors:
            av = c.selected(a, values, 'or')
            bv = c.selected(b, values, 'or')
            values.append(c.conjunction(av, bv))
        output = c.selected(final, values, 'or')
        active = [v for (p, l), v in edge.items() if x >> p & x >> (P + l) & 1]
        target = c.disjunction(active)
        c.cl(-output, target)
        c.cl(output, -target)
    return c, edge, selectors, final


def run(P, seconds, seed, solver_cap=60, family='c4free'):
    n, count = 2 * P, P - 1
    family_label = '' if family == 'c4free' else family + '-'
    name = f'variable-{family_label}{P}x{P}-and{count}-{seed}'
    target_dir = OUT / name
    target_dir.mkdir(exist_ok=True)
    assignments = {0} | {1 << i for i in range(n)}
    assignments |= {(1 << i) | (1 << j) for i, j in itertools.combinations(range(n), 2)}
    assignment_path = target_dir / 'assignments.json'
    if assignment_path.is_file():
        assignments |= set(json.loads(assignment_path.read_text()))
    for model_path in sorted(target_dir.glob('iteration-*-model.json')):
        previous_model = json.loads(model_path.read_text())
        assignments |= {x for x, y in boundary_rows(n, previous_model['edges'], P) if not y}
    previous = sorted(target_dir.glob('iteration-*.log'))
    offset = max((int(path.stem.split('-')[1]) for path in previous), default=-1) + 1
    input_masks = [sum(bool(x >> i & 1) << x for x in range(1 << n)) for i in range(n)]
    allmask = (1 << (1 << n)) - 1
    rng = random.Random(seed)
    start, end = time.monotonic(), time.monotonic() + seconds
    rows = []
    for iteration in range(offset, offset + 100):
        remaining = end - time.monotonic()
        if remaining < 2:
            break
        c, edge, selectors, final = build(P, count, assignments, family)
        assignment_path.write_text(json.dumps(sorted(assignments)))
        cnf_path = target_dir / f'iteration-{iteration:03d}.cnf'
        log_path = target_dir / f'iteration-{iteration:03d}.log'
        c.dump(cnf_path)
        cap = min(solver_cap, int(remaining))
        print('ITERATION', iteration, 'rows', len(assignments), 'variables', c.n,
              'clauses', len(c.clauses), 'cap', cap, flush=True)

        def limits():
            resource.setrlimit(resource.RLIMIT_AS, (1500 * 1024**2, 1500 * 1024**2))
            resource.setrlimit(resource.RLIMIT_CPU, (cap + 5, cap + 5))

        with log_path.open('w') as f:
            try:
                r = subprocess.run([SOLVER, '-t', str(cap), str(cnf_path)],
                                   stdout=f, stderr=subprocess.STDOUT,
                                   timeout=cap + 10, preexec_fn=limits)
            except subprocess.TimeoutExpired:
                f.write('\nPython outer timeout.\n')
                r = subprocess.CompletedProcess([], 124)
        print('STATUS', r.returncode, 'elapsed', round(time.monotonic() - start, 2), flush=True)
        if r.returncode != 10:
            rows.append({'iteration': iteration, 'status': r.returncode})
            break
        text = log_path.read_text()
        model = {int(v) for line in text.splitlines() if line.startswith('v ')
                 for v in line[2:].split() if int(v) > 0}
        selected = lambda ss: [i for i, v in enumerate(ss) if v in model]
        E = [pair for pair, v in edge.items() if v in model]
        assert all((p, p) in E for p in range(P))
        if family == 'c4free':
            assert not any(all((a, b) in E for a in [p, q] for b in [l, k])
                           for p, q in itertools.combinations(range(P), 2)
                           for l, k in itertools.combinations(range(P), 2))
        else:
            assert not any((p, q) in E and (q, p) in E
                           for p, q in itertools.combinations(range(P), 2))
        macro = [(selected(a), selected(b)) for a, b in selectors]
        last = selected(final)
        values = input_masks.copy()
        def aggregate(indices):
            result = 0
            for i in indices:
                result |= values[i]
            return result
        for a, b in macro:
            values.append(aggregate(a) & aggregate(b))
        function = aggregate(last)
        target = 0
        for p, l in E:
            target |= input_masks[p] & input_masks[P + l]
        assert target & ~function == 0, 'two-hot correctness must imply no false negatives'
        excess = function & (allmask ^ target)
        witness = {'P': P, 'L': P, 'family': family, 'edges': E, 'macro': macro, 'final': last,
                   'false_positive_count': excess.bit_count(), 'iteration': iteration}
        (target_dir / f'iteration-{iteration:03d}-model.json').write_text(json.dumps(witness, indent=2))
        rows.append({'iteration': iteration, 'status': r.returncode,
                     'edges': len(E), 'false_positives': excess.bit_count()})
        print('MODEL', 'edges', len(E), 'false_positives', excess.bit_count(), flush=True)
        if excess == 0:
            gates, wires = [], list(range(n))
            def combine(indices):
                assert indices
                wire = wires[indices[0]]
                for i in indices[1:]:
                    gates.append(('or', wire, wires[i]))
                    wire = n + len(gates) - 1
                return wire
            for a, b in macro:
                av, bv = combine(a), combine(b)
                gates.append(('and', av, bv))
                wires.append(n + len(gates) - 1)
            output = combine(last)
            assert sum(op == 'and' for op, _, _ in gates) == count
            witness.update(gates=gates, output=output)
            label = 'FULL_TRUTH_TABLE_COUNT_COUNTEREXAMPLE' if family == 'c4free' else 'FULL_TRUTH_TABLE_AUXILIARY_COUNT_COUNTEREXAMPLE'
            print(label, json.dumps(witness), flush=True)
            (target_dir / 'counterexample.json').write_text(json.dumps(witness, indent=2))
            break
        cuts = set()
        edge_masks = [(1 << p) | (1 << (P + l)) for p, l in E]
        for _ in range(24):
            if not excess:
                break
            lowest = excess & -excess
            x = lowest.bit_length() - 1
            order = list(range(n))
            rng.shuffle(order)
            for v in order:
                extended = x | (1 << v)
                if not any(extended & e == e for e in edge_masks):
                    x = extended
            assert function >> x & 1 and not target >> x & 1
            assert x not in assignments
            cuts.add(x)
            # Remove this assignment and its subsets to diversify subsequent cuts.
            sub = x
            while True:
                excess &= ~(1 << sub)
                if sub == 0:
                    break
                sub = (sub - 1) & x
        assignments |= cuts
        assignments |= {x for x, y in boundary_rows(n, E, P) if not y}
        assignment_path.write_text(json.dumps(sorted(assignments)))
        print('ADDED_CUTS', len(cuts), flush=True)
    (target_dir / f'summary-{offset:03d}.json').write_text(json.dumps(rows, indent=2))
    print('FINISH', round(time.monotonic() - start, 2), 'iterations', len(rows), flush=True)


if __name__ == '__main__':
    run(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]),
        int(sys.argv[4]) if len(sys.argv) > 4 else 60,
        sys.argv[5] if len(sys.argv) > 5 else 'c4free')
