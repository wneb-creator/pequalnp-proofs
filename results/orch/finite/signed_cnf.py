import itertools
import json
import sys
from pathlib import Path


def main():
    out = Path(sys.argv[1])
    n, size = 9, 15
    edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
             (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
    counter = 0

    def fresh():
        nonlocal counter
        counter += 1
        return counter

    ops = [[fresh() for _ in range(4)] for _ in range(size)]
    left = [[fresh() for _ in range(n + 1 + j)] for j in range(size)]
    right = [[fresh() for _ in range(n + 1 + j)] for j in range(size)]
    av = [[fresh() for _ in range(1 << n)] for _ in range(size)]
    bv = [[fresh() for _ in range(1 << n)] for _ in range(size)]
    val = [[fresh() for _ in range(1 << n)] for _ in range(size)]
    count = 0
    body = out.with_suffix('.body')
    with body.open('w') as handle:
        def clause(items):
            nonlocal count
            handle.write(' '.join(map(str, items)) + ' 0\n')
            count += 1

        def exactly_one(items):
            clause(items)
            for a, b in itertools.combinations(items, 2):
                clause([-a, -b])

        for j in range(size):
            exactly_one(ops[j])
            exactly_one(left[j])
            exactly_one(right[j])
            for a in range(n + 1 + j):
                for b in range(a):
                    clause([-left[j][a], -right[j][b]])
            for row in range(1 << n):
                for selectors, value in ((left[j], av[j][row]), (right[j], bv[j][row])):
                    for source, selector in enumerate(selectors):
                        if source <= n:
                            bit = (row >> source) & 1 if source < n else 0
                            clause([-selector, value if bit else -value])
                        else:
                            old = val[source - n - 1][row]
                            clause([-selector, -old, value])
                            clause([-selector, old, -value])
                for op in range(4):
                    for a, b in itertools.product((False, True), repeat=2):
                        z = (a and b, a or b, a and not b, not a and b)[op]
                        clause([-ops[j][op], -av[j][row] if a else av[j][row],
                                -bv[j][row] if b else bv[j][row],
                                val[j][row] if z else -val[j][row]])
        for row in range(1 << n):
            target = any((row >> a) & 1 and (row >> b) & 1 for a, b in edges)
            clause([val[-1][row] if target else -val[-1][row]])
    with out.open('w') as handle, body.open() as data:
        handle.write(f'p cnf {counter} {count}\n')
        for line in data:
            handle.write(line)
    body.unlink()
    out.with_suffix('.json').write_text(json.dumps(dict(n=n, size=size, edges=edges,
        ops=ops, left=left, right=right, av=av, bv=bv, val=val,
        variables=counter, clauses=count)))
    print(json.dumps(dict(variables=counter, clauses=count, bytes=out.stat().st_size)))


if __name__ == '__main__':
    main()
