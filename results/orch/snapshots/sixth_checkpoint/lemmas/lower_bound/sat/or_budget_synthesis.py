import argparse
import json
import time
from pathlib import Path

from global_synthesis import CNF, evaluate
from incremental_cegis import Solver
from subset_cegis import stamp


def graph_truth(edges, mask):
    return any(mask >> a & 1 and mask >> b & 1 for a, b in edges)


def graph_tests(n, edges):
    tests = [((1 << a) | (1 << b), 1) for a, b in edges]
    tests += [(mask, 0) for mask in range(1 << n)
              if not graph_truth(edges, mask)
              and all(graph_truth(edges, mask | (1 << i)) for i in range(n)
                      if not (mask >> i & 1))]
    return tests


def conjunction(cnf, selectors, sources, prefer=None):
    value = cnf.var(prefer)
    failures = []
    for selector, source in zip(selectors, sources):
        cnf.clause(-value, -selector, source)
        if source == 1:
            continue
        if source == -1:
            failures.append(selector)
        else:
            failure = cnf.var()
            cnf.clause(-failure, selector)
            cnf.clause(-failure, -source)
            failures.append(failure)
    cnf.clause(value, *failures)
    return value


def lex_order(cnf, left, right):
    equal = 1
    for a, b in reversed(list(zip(left, right))):
        cnf.clause(-equal, -a, b)
        next_equal = cnf.var()
        cnf.clause(-next_equal, equal)
        cnf.clause(-next_equal, -a, b)
        cnf.clause(-next_equal, a, -b)
        cnf.clause(-equal, -a, -b, next_equal)
        cnf.clause(-equal, a, b, next_equal)
        equal = next_equal


def emit_or(path, n, edges, count, tests, fixed=False, ordered=True):
    cnf = CNF(path)
    selectors = []
    hints = []
    source_unions = []
    base = n + 1  # The additional available signal is constant false.
    edge_sets = {frozenset(edge) for edge in edges}
    for i in range(count):
        pair = [list(edges[0]) if i == 0 else [base + i - 1],
                list(edges[min(i + 1, len(edges) - 1)])]
        pair.sort(key=lambda subset: sum(1 << j for j in subset))
        hints.append(pair)
        sides = []
        for subset in pair:
            side = [cnf.var(j in subset) for j in range(base + i)]
            # Positive incomparability makes each conjunction true on an edge.
            cnf.clause(-side[n])
            for a in range(n):
                for b in range(a):
                    if frozenset((a, b)) not in edge_sets:
                        cnf.clause(-side[a], -side[b])
            if fixed:
                for j, literal in enumerate(side):
                    cnf.clause(literal if j in subset else -literal)
            sides.append(side)
        lex_order(cnf, *sides)
        for left, right in (sides, list(reversed(sides))):
            exclusive = []
            for a, b in zip(left, right):
                witness = cnf.var()
                cnf.clause(-witness, a)
                cnf.clause(-witness, -b)
                exclusive.append(witness)
            cnf.clause(*exclusive)
        union = []
        for a, b in zip(*sides):
            used = cnf.var()
            cnf.clause(-a, used)
            cnf.clause(-b, used)
            cnf.clause(a, b, -used)
            union.append(used)
        if ordered and source_unions:
            before = source_unions[-1] + [-1]
            lex_order(cnf, before, union)
        source_unions.append(union)
        selectors.append(sides)
    output_hint = base + count - 1
    output_selectors = [cnf.var(j == output_hint) for j in range(base + count)]
    cnf.clause(-output_selectors[n])
    for raw in range(n):
        if not all(raw in edge for edge in edges):
            cnf.clause(-output_selectors[raw])
    if fixed:
        for j, literal in enumerate(output_selectors):
            cnf.clause(literal if j == output_hint else -literal)
    witnesses = [[[], []] for _ in range(count)]
    for mask, label in tests:
        values = [1 if mask >> i & 1 else -1 for i in range(n)] + [-1]
        for i, sides in enumerate(selectors):
            a, b = [conjunction(cnf, side, values) for side in sides]
            z = cnf.var()
            cnf.clause(-a, z)
            cnf.clause(-b, z)
            cnf.clause(a, b, -z)
            values.append(z)
            if label:
                for direction, (u, v) in enumerate(((a, b), (b, a))):
                    witness = cnf.var()
                    cnf.clause(-witness, u)
                    cnf.clause(-witness, -v)
                    witnesses[i][direction].append(witness)
        output = conjunction(cnf, output_selectors, values)
        cnf.clause(output if label else -output)
    for directions in witnesses:
        for values in directions:
            cnf.clause(*values)
    cnf.finish()
    return selectors, output_selectors, cnf.variables, cnf.clauses


def materialize(n, gates, output):
    answer = []
    signals = [('wire', i) for i in range(n)] + [('constant', False)]

    def combine(op, xs):
        absorbing = bool(op)
        identity = not bool(op)
        if ('constant', absorbing) in xs:
            return ('constant', absorbing)
        xs = list(dict.fromkeys(x for x in xs if x != ('constant', identity)))
        if not xs:
            return ('constant', identity)
        result, *rest = xs
        for value in rest:
            assert result[0] == value[0] == 'wire'
            answer.append([op, result[1], value[1]])
            result = ('wire', n + len(answer) - 1)
        return result

    for left, right in gates:
        a = combine(0, [signals[j] for j in left])
        b = combine(0, [signals[j] for j in right])
        signals.append(combine(1, [a, b]))
    result = combine(0, [signals[j] for j in output])
    assert result[0] == 'wire'
    # Keep exactly the output cone, preserving the actual number of ORs.
    live = set()

    def visit(wire):
        if wire >= n and wire not in live:
            live.add(wire)
            _, a, b = answer[wire - n]
            visit(a)
            visit(b)

    visit(result[1])
    compact = []
    mapping = {i: i for i in range(n)}
    for i, (op, a, b) in enumerate(answer):
        if n + i in live:
            compact.append([op, mapping[a], mapping[b]])
            mapping[n + i] = n + len(compact) - 1
    assert mapping[result[1]] == n + len(compact) - 1
    return compact


def run(name, n, edges, folder, count, seconds, fixed=False, ordered=True):
    folder.mkdir(parents=True, exist_ok=True)
    tests = graph_tests(n, edges)
    path = folder / 'problem.cnf'
    selectors, output_selectors, variables, clauses = emit_or(path, n, edges, count, tests, fixed, ordered)
    solver = Solver(57000 + count)
    for side in [side for gate in selectors for side in gate] + [output_selectors]:
        for literal in side:
            solver.freeze(literal)
    with path.open() as source:
        for line in source:
            if not line.startswith('p'):
                solver.add(*[int(word) for word in line.split()[:-1]])
    stamp('OR BUDGET', name, count, 'fixed', fixed, 'tests', len(tests),
          'variables', variables, 'clauses', clauses)
    start = time.monotonic()
    result = solver.solve(20 if fixed else seconds)
    stamp('RESULT', name, 'ORs', count, result, 'seconds', round(time.monotonic() - start, 2))
    report = dict(name=name, raw_inputs=n, edges=edges, or_budget=count,
                  result=result, fixed=fixed, unrestricted_and_count=True,
                  ordered_or_nodes=ordered)
    if fixed:
        assert result == 10
    if result == 10:
        gates = [[[j for j, lit in enumerate(side) if solver.truth(lit)] for side in gate]
                 for gate in selectors]
        output = [j for j, lit in enumerate(output_selectors) if solver.truth(lit)]
        concrete = materialize(n, gates, output)
        assert sum(op for op, _, _ in concrete) <= count
        assert all(evaluate(concrete, mask, n) == graph_truth(edges, mask) for mask in range(1 << n))
        report.update(or_conjunction_gates=gates, output_conjunction=output,
                      circuit=concrete, gate_count=len(concrete),
                      and_count=sum(not op for op, _, _ in concrete),
                      or_count=sum(op for op, _, _ in concrete),
                      raw_assignments_checked=1 << n)
        stamp('VERIFIED CONCRETE CIRCUIT', len(concrete), 'gates', report['or_count'], 'ORs')
    (folder / 'result.json').write_text(json.dumps(report))
    solver.close()
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('output', type=Path)
    parser.add_argument('--case', choices=['c4', 'c5', 'c6', 'subdiv_k4', 'heawood'], required=True)
    parser.add_argument('--seconds', type=int, default=60)
    parser.add_argument('--unordered', action='store_true')
    args = parser.parse_args()
    if args.case in ['c4', 'c5', 'c6']:
        n = int(args.case[1:])
        edges = [(i, (i + 1) % n) for i in range(n)]
    elif args.case == 'subdiv_k4':
        n = 10
        edges = []
        for line, (a, b) in enumerate(__import__('itertools').combinations(range(4), 2), 4):
            edges.extend([(a, line), (b, line)])
    else:
        n = 14
        edges = [(point, 7 + (point + offset) % 7) for point in range(7) for offset in [0, 1, 3]]
    run(args.case, n, edges, args.output / 'calibration', len(edges) - 1, 20,
        fixed=True, ordered=not args.unordered)
    run(args.case, n, edges, args.output / 'search', len(edges) - 2, args.seconds,
        ordered=not args.unordered)


if __name__ == '__main__':
    main()
