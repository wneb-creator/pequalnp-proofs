import itertools
import json
import resource
import subprocess
import sys
import time
from pathlib import Path

OUT = Path(__file__).resolve().parent
SOLVER = '/tmp/oec/pequalnp-pilot-46/toolchain/lean-4.36.0-linux/bin/cadical'


class CNF:
    def __init__(self):
        self.n = 0
        self.clauses = []

    def var(self):
        self.n += 1
        return self.n

    def cl(self, *xs):
        self.clauses.append(xs)

    def conjunction(self, a, b):
        v = self.var()
        self.cl(-v, a)
        self.cl(-v, b)
        self.cl(v, -a, -b)
        return v

    def disjunction(self, lits):
        v = self.var()
        for x in lits:
            self.cl(-x, v)
        self.cl(-v, *lits)
        return v

    def selected(self, selectors, values, kind):
        # Disjunction of selected values, or negated disjunction of selected
        # false values. Selector sets are globally constrained to be nonempty.
        terms = []
        for s, w in zip(selectors, values):
            if isinstance(w, bool):
                if w == (kind == 'or'):
                    terms.append(s)
            else:
                terms.append(self.conjunction(s, w if kind == 'or' else -w))
        v = self.disjunction(terms)
        return v if kind == 'or' else -v

    def dump(self, path):
        with path.open('w') as f:
            f.write(f'p cnf {self.n} {len(self.clauses)}\n')
            for clause in self.clauses:
                f.write(' '.join(map(str, clause)) + ' 0\n')


def boundary_rows(n, E, P):
    edges = [(1 << p) | (1 << (P + l)) for p, l in E]
    positives = sorted(set(edges))
    negatives = []
    for x in range(1 << n):
        if any(x & e == e for e in edges):
            continue
        if all(any((x | (1 << v)) & e == e for e in edges)
               for v in range(n) if not x >> v & 1):
            negatives.append(x)
    return [(x, True) for x in positives] + [(x, False) for x in negatives]


def solve(P, L, E, count, kind, name, seconds=300, profile='private', generate_only=False):
    assert profile in ['base', 'topo', 'private']
    n = P + L
    c = CNF()
    selectors = []
    for i in range(count):
        a = [c.var() for _ in range(n + i)]
        b = [c.var() for _ in range(n + i)]
        c.cl(*a)
        c.cl(*b)
        # The two aggregated operands commute. Lexicographically order their
        # selector vectors, without constraining either possible operand set.
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
    # A topological order can choose the currently available counted gate with
    # smallest maximum aggregate predecessor. Newly unlocked gates have a
    # maximum predecessor at least the newly chosen gate's index. Thus these
    # maxima can be arranged nondecreasingly.
    if profile in ['topo', 'private']:
        for (a, b), (aa, bb) in zip(selectors, selectors[1:]):
            for j in range(len(a)):
                higher = aa[j:] + bb[j:]
                c.cl(-a[j], *higher)
                c.cl(-b[j], *higher)
    other = 'or' if kind == 'and' else 'and'
    rows = boundary_rows(n, E, P)
    private10 = [[] for _ in range(count)]
    private01 = [[] for _ in range(count)]
    for x, target in rows:
        values = [bool(x >> v & 1) for v in range(n)]
        for i, (a, b) in enumerate(selectors):
            av = c.selected(a, values, other)
            bv = c.selected(b, values, other)
            if profile == 'private' and target == (kind == 'or'):
                private10[i].append(c.conjunction(av, -bv))
                private01[i].append(c.conjunction(-av, bv))
            v = c.conjunction(av, bv) if kind == 'and' else c.disjunction([av, bv])
            values.append(v)
        out = c.selected(final, values, other)
        c.cl(out if target else -out)
    if profile == 'private':
        for i, (a, b) in enumerate(selectors):
            # A minimum-count circuit has private boundary rows on both operand
            # sides: otherwise bypass this counted gate and preserve the target.
            # Exact-count padding remains possible through identical-operand copies.
            copy = c.var()
            for av, bv in zip(a, b):
                c.cl(-copy, -av, bv)
                c.cl(-copy, av, -bv)
            c.cl(copy, *private10[i])
            c.cl(copy, *private01[i])
    suffix = '' if profile == 'base' else profile + '-'
    name = f'{name}-macro-{suffix}{kind}{count}'
    path, log = OUT / (name + '.cnf'), OUT / (name + '.log')
    c.dump(path)
    print('start', name, 'rows', len(rows), 'variables', c.n,
          'clauses', len(c.clauses), flush=True)
    if generate_only:
        return {'name': name, 'variables': c.n, 'clauses': len(c.clauses),
                'generated_cnf': str(path)}

    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (1900 * 1024**2, 1900 * 1024**2))
        resource.setrlimit(resource.RLIMIT_CPU, (seconds + 10, seconds + 10))

    start = time.monotonic()
    with log.open('w') as f:
        try:
            result = subprocess.run([SOLVER, '-t', str(seconds), str(path)],
                                    stdout=f, stderr=subprocess.STDOUT,
                                    preexec_fn=limits, timeout=seconds + 20)
        except subprocess.TimeoutExpired:
            f.write('\nPython outer timeout reached.\n')
            result = subprocess.CompletedProcess([], 124)
    text = log.read_text()
    print('finish', name, 'seconds', round(time.monotonic() - start, 3),
          'returncode', result.returncode, flush=True)
    witness = None
    if result.returncode == 10:
        model = {int(v) for line in text.splitlines() if line.startswith('v ')
                 for v in line[2:].split() if int(v) > 0}
        selected = lambda ss: [i for i, v in enumerate(ss) if v in model]
        macro = [(selected(a), selected(b)) for a, b in selectors]
        last = selected(final)
        gates = []
        wires = list(range(n))

        def combine(indices):
            assert indices
            w = wires[indices[0]]
            for j in indices[1:]:
                gates.append((other, w, wires[j]))
                w = n + len(gates) - 1
            return w

        for a, b in macro:
            av, bv = combine(a), combine(b)
            gates.append((kind, av, bv))
            wires.append(n + len(gates) - 1)
        output = combine(last)
        for x in range(1 << n):
            values = [bool(x >> v & 1) for v in range(n)]
            for op, a, b in gates:
                values.append(values[a] and values[b] if op == 'and'
                              else values[a] or values[b])
            target = any((x >> p) & (x >> (P + l)) & 1 for p, l in E)
            assert values[output] == target
        assert sum(op == kind for op, _, _ in gates) == count
        witness = {'P': P, 'L': L, 'edges': E, 'gates': gates,
                   'output': output, 'macro': macro, 'final': last}
        (OUT / (name + '-witness.json')).write_text(json.dumps(witness, indent=2))
        print('WITNESS', json.dumps(witness), flush=True)
    return {'name': name, 'P': P, 'L': L, 'edges': E, 'kind': kind,
            'count': count, 'returncode': result.returncode,
            'seconds': round(time.monotonic() - start, 3),
            'witness_gate_count': None if witness is None else len(witness['gates'])}


if __name__ == '__main__':
    problem, mode = sys.argv[1:3]
    seconds = int(sys.argv[3])
    if problem == 'c6':
        P = L = 3
        E = [(0, 0), (0, 1), (1, 1), (1, 2), (2, 2), (2, 0)]
        tau = 3
    elif problem == 'theta':
        P = L = 4
        E = json.loads((OUT / 'maximum44.json').read_text())
        tau = 4
    elif problem == 'fano':
        P = L = 7
        E = [(p, l) for p in range(7) for l in range(7) if (p - l) % 7 in [0, 1, 3]]
        tau = 7
    elif problem == 'p4':
        P = L = 2
        E = [(0, 0), (1, 0), (1, 1)]
        tau = 2
    elif problem.startswith('cycle'):
        P = L = int(problem[5:]) // 2
        E = [(p, l) for p in range(P) for l in range(L)
             if l in [p, (p + 1) % L]]
        tau = P
    bound = tau - 1 if mode == 'and' else len(E) - 2
    row = solve(P, L, E, bound, mode, problem, seconds,
                profile=sys.argv[4] if len(sys.argv) > 4 else 'private')
    (OUT / f'{problem}-macro-{mode}-result.json').write_text(json.dumps(row, indent=2))
