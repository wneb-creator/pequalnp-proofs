import ast
import itertools
import json
import random
import resource
from fractions import Fraction as Q
from pathlib import Path

resource.setrlimit(resource.RLIMIT_AS, (256 * 2**20, 256 * 2**20))
resource.setrlimit(resource.RLIMIT_CPU, (30, 35))
base = Path('/tmp/oec/pequalnp-pilot-78/numeric')
coords = [(i, j) for i in range(4) for j in range(i, 4)]
perms = list(itertools.permutations(range(4)))
rng = random.Random(231)

def evaluate(node, xs):
    if isinstance(node, ast.Expression):
        return evaluate(node.body, xs)
    if isinstance(node, ast.Constant):
        return Q(node.value)
    if isinstance(node, ast.Name):
        return xs[int(node.id[1:])]
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return -evaluate(node.operand, xs)
    a, b = evaluate(node.left, xs), evaluate(node.right, xs)
    if isinstance(node.op, ast.Add): return a + b
    if isinstance(node.op, ast.Sub): return a - b
    if isinstance(node.op, ast.Mult): return a * b
    if isinstance(node.op, ast.Div): return a / b
    if isinstance(node.op, ast.Pow):
        assert b.denominator == 1
        return a ** b.numerator
    raise AssertionError(type(node))

def permanent(M):
    return sum((M[0][p[0]] * M[1][p[1]] * M[2][p[2]] * M[3][p[3]] for p in perms), Q(0))

counts = {'charts': 0, 'assignments': 0, 'coefficient_comparisons': 0, 'direct_permanents': 0}
for label, edge in [('incident', 1), ('disjoint', 5)]:
    lines = (base / ('chart-rank1-' + label + '-p0.ms')).read_text().splitlines()
    assert lines[0].split(',') == ['x' + str(i) for i in range(11)] and lines[1] == '0'
    parsed = [ast.parse(p.replace('^', '**'), mode='eval') for p in ''.join(lines[2:]).split(',')]
    exps = [(i, degree-i) for degree in range(2, 5) for i in range(degree+1)]
    assert len(parsed) == len(exps) == 12
    solved = 2 if edge == 1 else 1
    for trial in range(5):
        xs = [Q(rng.randrange(-3, 4), rng.randrange(1, 4)) for _ in range(11)]
        av = [Q(0)] * 10
        bv = [Q(0)] * 10
        av[edge] = Q(1)
        bv[0] = Q(1)
        free_a = [i for i, (r, c) in enumerate(coords) if r != c and i not in (edge, solved)]
        free_b = [i for i in range(10) if i not in (0, edge, 9)]
        for i, x in zip(free_a, xs[:4]): av[i] = x
        av[solved] = -sum(av)
        for i, x in zip(free_b, xs[4:]): bv[i] = x
        bv[9] = -sum((1 if r == c else 2) * bv[i] for i, (r, c) in enumerate(coords))
        A, B = [[Q(0)]*4 for _ in range(4)], [[Q(0)]*4 for _ in range(4)]
        for i, (r, c) in enumerate(coords):
            A[r][c] = A[c][r] = av[i]
            B[r][c] = B[c][r] = bv[i]
        assert sum(map(sum, A)) == sum(map(sum, B)) == 0
        coefficients = {}
        for p in perms:
            product = {(0, 0): Q(1)}
            for i in range(4):
                new = {}
                for (a, b), value in product.items():
                    for da, db, factor in [(0, 0, Q(1)), (1, 0, A[i][p[i]]), (0, 1, B[i][p[i]])]:
                        exp = (a+da, b+db)
                        new[exp] = new.get(exp, Q(0)) + value * factor
                product = new
            for exp, value in product.items(): coefficients[exp] = coefficients.get(exp, Q(0)) + value
        values = [evaluate(p, xs) for p in parsed]
        assert coefficients[(0, 0)] == 24 and coefficients[(1, 0)] == coefficients[(0, 1)] == 0
        for exp, value in zip(exps, values): assert coefficients[exp] == value
        counts['coefficient_comparisons'] += len(exps)
        for s, t in [(Q(2, 3), Q(-1, 2)), (Q(-2), Q(3))]:
            M = [[1+s*A[i][j]+t*B[i][j] for j in range(4)] for i in range(4)]
            assert permanent(M) == 24 + sum(value*s**exp[0]*t**exp[1] for exp, value in zip(exps, values))
            counts['direct_permanents'] += 1
        counts['assignments'] += 1
    counts['charts'] += 1
print(json.dumps({'status': 'PASS', **counts}, sort_keys=True))
