#!/usr/bin/env python3
"""Finite AO2 circuit synthesis with explicit DIMACS and independently checked models."""
import argparse
import itertools
import json
from pathlib import Path


class CNF:
    def __init__(self):
        self.nvars = 0
        self.clauses = []

    def var(self):
        self.nvars += 1
        return self.nvars

    def add(self, *lits):
        if any(type(x) is bool and x for x in lits):
            return
        lits = list(dict.fromkeys(x for x in lits if type(x) is not bool))
        if any(-x in lits for x in lits):
            return
        self.clauses.append(lits)

    def onehot(self, xs):
        self.add(*xs)
        for a, b in itertools.combinations(xs, 2):
            self.add(-a, -b)

    def write(self, path):
        with Path(path).open('w') as f:
            f.write(f'p cnf {self.nvars} {len(self.clauses)}\n')
            for clause in self.clauses:
                f.write(' '.join(map(str, clause)) + ' 0\n')


def canonical(data):
    n = data['n']
    left = data['points']
    gates = []
    roots = []
    for l in range(len(data['lines'])):
        ps = [p for p, r in data['edges'] if r == l]
        r = ps[0]
        for p in ps[1:]:
            gates.append({'op': 'or', 'a': r, 'b': p})
            r = n + len(gates) - 1
        gates.append({'op': 'and', 'a': r, 'b': left + l})
        roots.append(n + len(gates) - 1)
    r = roots[0]
    for x in roots[1:]:
        gates.append({'op': 'or', 'a': r, 'b': x})
        r = n + len(gates) - 1
    return gates


def delete_gate(data, gates, index, side):
    n = data['n']
    replacement = gates[index][side]
    result = []
    for i, g in enumerate(gates):
        if i == index:
            continue
        h = dict(g)
        for k in ['a', 'b']:
            x = h[k]
            if x == n + index:
                x = replacement
            if x > n + index:
                x -= 1
            h[k] = x
        result.append(h)
    return result


def encode(args):
    data = json.loads(Path(args.tests).read_text())
    n = data['n']
    tests = data['tests']
    c = CNF()
    k = args.gates
    left = [[c.var() for _ in range(n + g)] for g in range(k)]
    right = [[c.var() for _ in range(n + g)] for g in range(k)]
    op = [c.var() for _ in range(k)]
    val = [[c.var() for _ in tests] for _ in range(k)]
    aval = [[c.var() for _ in tests] for _ in range(k)]
    bval = [[c.var() for _ in tests] for _ in range(k)]
    for g in range(k):
        m = n + g
        c.onehot(left[g])
        c.onehot(right[g])
        # Strictly ordered operands; duplicate wires give redundant gates and
        # can be removed. Unused padding gates remain allowed.
        for a in range(m):
            for b in range(a + 1):
                c.add(-left[g][a], -right[g][b])
        for selectors, operands in [(left[g], aval[g]), (right[g], bval[g])]:
            for wire, sel in enumerate(selectors):
                for t, test in enumerate(tests):
                    v = operands[t]
                    if wire < n:
                        c.add(-sel, v if (test['mask'] >> wire) & 1 else -v)
                    else:
                        x = val[wire - n][t]
                        c.add(-sel, -v, x)
                        c.add(-sel, v, -x)
        for t in range(len(tests)):
            a, b, y, o = aval[g][t], bval[g][t], val[g][t], op[g]
            # Positive op means AND; negative means OR.
            c.add(-o, -y, a)
            c.add(-o, -y, b)
            c.add(-o, y, -a, -b)
            c.add(o, y, -a)
            c.add(o, y, -b)
            c.add(o, -y, a, b)
    for t, test in enumerate(tests):
        c.add(val[-1][t] if test['value'] else -val[-1][t])
    if getattr(args, 'live', False):
        # Optional exact-size scope: every gate reaches the final output.
        # This is intentionally recorded, since arbitrary unused padding
        # is excluded by these clauses.
        for g in range(k - 1):
            c.add(*(s[h][n + g] for h in range(g + 1, k)
                    for s in [left, right]))
    if getattr(args, 'edge_live', False):
        # A gate false on every minimal true input can be replaced by
        # false and propagated away from a minimum monotone circuit.
        for g in range(k):
            c.add(*(val[g][t] for t,test in enumerate(tests) if test['value']))
    if args.irredundant:
        # Comparable operands make either AND or OR equal one operand on
        # the complete boundary tests, and the gate can then be removed.
        for g in range(k):
            for aa, bb in [(aval[g], bval[g]), (bval[g], aval[g])]:
                witnesses = []
                for a, b in zip(aa, bb):
                    w = c.var()
                    witnesses.append(w)
                    c.add(-w, a)
                    c.add(-w, -b)
                c.add(*witnesses)
    if getattr(args, 'minimal', False):
        for g in range(k):
            c.add(*(val[g][t] for t,test in enumerate(tests) if test['value']))
            c.add(*(-val[g][t] for t,test in enumerate(tests) if not test['value']))
            # An OR comparable on minimal true rows can be replaced by its
            # dominating operand; an AND comparable on maximal false rows
            # can be replaced by its narrower operand. Both replacements
            # preserve the specified monotone output function.
            for on_true, active in [(True, -op[g]), (False, op[g])]:
                for aa, bb in [(aval[g], bval[g]), (bval[g], aval[g])]:
                    ws = []
                    for t,test in enumerate(tests):
                        if bool(test['value']) != on_true:
                            continue
                        w = c.var()
                        ws.append(w)
                        c.add(-w, aa[t])
                        c.add(-w, -bb[t])
                    c.add(-active, *ws)
    if getattr(args, 'topform', False):
        negative = [t for t,test in enumerate(tests) if not test['value']]
        for g in range(k - 1):
            for h in range(g + 1, k):
                for selectors in [left[h], right[h]]:
                    c.add(-selectors[n + g], -op[h], *(val[g][t] for t in negative))
    if args.first:
        a, b = map(int, args.first.split(','))
        assert 0 <= a < b < n
        c.add(left[0][a])
        c.add(right[0][b])
    fixed = None
    free = []
    if args.fixed:
        fixed = json.loads(Path(args.fixed).read_text())
        if isinstance(fixed, dict):
            fixed = fixed['gates']
        assert len(fixed) == k
        free = [int(x) for x in args.free.split(',')] if args.free else []
        for g, h in enumerate(fixed):
            if g in free:
                continue
            a, b = sorted([h['a'], h['b']])
            c.add(left[g][a])
            c.add(right[g][b])
            c.add(op[g] if h['op'] == 'and' else -op[g])
    if args.and_count is not None:
        # Exact cardinality via prefix dynamic programming. States p[i,j]
        # encode at least j positive operator bits among the first i gates.
        count = args.and_count
        p = [[False] * (count + 2) for _ in range(k + 1)]
        for i in range(k + 1):
            p[i][0] = True
        for i in range(1, k + 1):
            for j in range(1, count + 2):
                if j > i:
                    continue
                y = c.var()
                p[i][j] = y
                a, b, o = p[i - 1][j], p[i - 1][j - 1], op[i - 1]
                neg = lambda x: (not x) if type(x) is bool else -x
                c.add(neg(a), y)
                c.add(neg(b), -o, y)
                c.add(-y, a, b)
                c.add(-y, a, o)
        c.add(p[k][count])
        c.add(-p[k][count + 1])
    c.write(args.output)
    meta = {'n': n, 'k': k, 'tests': args.tests, 'left': left, 'right': right,
            'op': op, 'val': val, 'first': args.first, 'fixed': fixed,
            'free': free, 'and_count': args.and_count,
            'irredundant': args.irredundant,
            'live': getattr(args, 'live', False),
            'edge_live': getattr(args, 'edge_live', False),
            'minimal': getattr(args, 'minimal', False),
            'topform': getattr(args, 'topform', False),
            'variables': c.nvars, 'clauses': len(c.clauses)}
    Path(args.output + '.json').write_text(json.dumps(meta))
    print(json.dumps({x: meta[x] for x in ['n','k','first','free','and_count','variables','clauses']}))


def verify(data, gates):
    n = data['n']
    for i, g in enumerate(gates):
        assert g['op'] in ['and', 'or']
        assert 0 <= g['a'] < n + i and 0 <= g['b'] < n + i
    errors = []
    for mask in range(1 << n):
        vs = [bool((mask >> i) & 1) for i in range(n)]
        for g in gates:
            a, b = vs[g['a']], vs[g['b']]
            vs.append(a and b if g['op'] == 'and' else a or b)
        want = any(vs[p] and vs[data['points'] + l] for p, l in data['edges'])
        if vs[-1] != want:
            errors.append(mask)
    return errors


def decode(args):
    meta = json.loads(Path(args.meta).read_text())
    data = json.loads(Path(meta['tests']).read_text())
    model = set()
    status = None
    for line in Path(args.model).read_text().splitlines():
        if line.startswith('s '):
            status = line[2:]
        if line.startswith('v '):
            model.update(int(x) for x in line[2:].split() if int(x) > 0)
    if status != 'SATISFIABLE':
        print('No SAT model:', status)
        return
    gates = []
    for g in range(meta['k']):
        aa = [i for i,x in enumerate(meta['left'][g]) if x in model]
        bb = [i for i,x in enumerate(meta['right'][g]) if x in model]
        assert len(aa) == len(bb) == 1
        gates.append({'op':'and' if meta['op'][g] in model else 'or','a':aa[0],'b':bb[0]})
    errors = verify(data, gates)
    print('exhaustive verification errors:', len(errors))
    if not errors:
        Path(args.output).write_text(json.dumps({'gates':gates,'all_inputs_checked':1 << data['n']},indent=2)+'\n')
        print('Verified witness:', args.output)
    else:
        print('first error masks:', errors[:10])
        raise ValueError('SAT encoding/model verification failed')


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest='command', required=True)
    e = sub.add_parser('encode')
    e.add_argument('--tests', required=True)
    e.add_argument('--gates', type=int, required=True)
    e.add_argument('--output', required=True)
    e.add_argument('--first')
    e.add_argument('--fixed')
    e.add_argument('--free')
    e.add_argument('--and-count', type=int)
    e.add_argument('--irredundant', action='store_true')
    e.add_argument('--live', action='store_true')
    e.add_argument('--edge-live', action='store_true')
    e.add_argument('--minimal', action='store_true')
    e.add_argument('--topform', action='store_true')
    d = sub.add_parser('decode')
    d.add_argument('--meta', required=True)
    d.add_argument('--model', required=True)
    d.add_argument('--output', required=True)
    a = sub.add_parser('canonical')
    a.add_argument('--tests', required=True)
    a.add_argument('--output', required=True)
    a.add_argument('--delete', type=int)
    a.add_argument('--side', choices=['a','b'], default='a')
    args = p.parse_args()
    if args.command == 'encode':
        encode(args)
    elif args.command == 'decode':
        decode(args)
    else:
        data = json.loads(Path(args.tests).read_text())
        gates = canonical(data)
        if args.delete is not None:
            gates = delete_gate(data, gates, args.delete, args.side)
        Path(args.output).write_text(json.dumps(gates,indent=2)+'\n')
        print('gates:',len(gates),'exhaustive semantic errors:',len(verify(data,gates)))


if __name__ == '__main__':
    main()
