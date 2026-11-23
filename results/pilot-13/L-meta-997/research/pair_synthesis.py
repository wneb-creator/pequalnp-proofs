import argparse
import json
import time
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--gates', type=int, default=10)
    parser.add_argument('--paid', type=int, default=3)
    parser.add_argument('--seconds', type=int, default=60)
    parser.add_argument('--case', choices=['n8', 'n9', 'n10'], default='n8')
    parser.add_argument('--mode', choices=['outside_meeting', 'selected_union'], default='outside_meeting')
    parser.add_argument('--full-target', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    n = int(args.case[1:])
    y = {0, 1, 2}
    target = {3, 4, 5, 6, 7}
    if n == 8:
        family = [{0, 1, 3}, {0, 2, 4}, {1, 2, 5}]
    elif n == 9:
        family = [{0, 8, 3}, {1, 8, 4}, {2, 8, 5}, {0, 1, 6}, {0, 2, 7}]
    else:
        family = [{0, 8, 3}, {1, 8, 4}, {2, 8, 5}, {0, 9, 4}, {1, 9, 5}, {2, 9, 6}]
    assert all(len(a & b) <= 1 for i, a in enumerate(family) for b in family[i + 1:])
    assert all(len(a & target) <= 1 for a in family)
    remaining = sorted(set(range(n)) - y)
    samples = [({p}, True) for p in range(n)]
    samples += [(y, False)] + [(y | {p}, False) for p in remaining]
    if args.full_target:
        complement = set(range(n)) - target
        samples += [(complement - {p}, True) for p in sorted(y)]
        samples += [(complement, False)]
    rows = len(samples)
    initial = [[int(p in x) for x, _ in samples] for p in range(n)]
    initial += [[int(z) for _, z in samples]]
    initial += [[0] * rows, [1] * rows]
    ni = len(initial)
    nvars = 0
    nclasses = len(family)
    light_bad = [('small', None)] + [('outside', p) for p in range(n) if p not in target]
    heavy_bad = [('small', None), ('base', None)] + [
        ('outside', p) for p in remaining if p not in target]
    if args.mode == 'selected_union':
        nclasses += len(light_bad) * len(heavy_bad)

    def variables(count):
        nonlocal nvars
        result = list(range(nvars, nvars + count))
        nvars += count
        return result

    left, right, op, av, bv, value, free = [], [], [], [], [], [], []
    for g in range(args.gates):
        left.append(variables(ni + g))
        right.append(variables(ni + g))
        op.append(variables(1)[0])
        av.append(variables(rows))
        bv.append(variables(rows))
        value.append(variables(rows))
        free.append(variables(nclasses))
    rr, cc, dd, lo, hi = [], [], [], [], []

    def add(coeffs, lower=-np.inf, upper=np.inf):
        row = len(lo)
        for col, coefficient in coeffs.items():
            if coefficient:
                rr.append(row)
                cc.append(col)
                dd.append(coefficient)
        lo.append(lower)
        hi.append(upper)

    for g in range(args.gates):
        add(dict.fromkeys(left[g], 1), 1, 1)
        add(dict.fromkeys(right[g], 1), 1, 1)
        ordering = {v: w for w, v in enumerate(left[g])}
        ordering.update({v: -w for w, v in enumerate(right[g])})
        add(ordering, upper=0)
        for r in range(rows):
            for sels, selected in [(left[g], av[g][r]), (right[g], bv[g][r])]:
                for w, sel in enumerate(sels):
                    if w < ni:
                        c = initial[w][r]
                        add({selected: 1, sel: 1}, upper=1 + c)
                        add({selected: 1, sel: -1}, lower=c - 1)
                    else:
                        prev = value[w - ni][r]
                        add({selected: 1, prev: -1, sel: 1}, upper=1)
                        add({selected: 1, prev: -1, sel: -1}, lower=-1)
            a, b, v, t = av[g][r], bv[g][r], value[g][r], op[g]
            add({v: 1, a: -1, t: -1}, lower=-1)
            add({v: 1, b: -1, t: -1}, lower=-1)
            add({v: 1, a: -1, b: -1, t: 1}, upper=1)
            add({v: 1, a: -1, t: -1}, upper=0)
            add({v: 1, b: -1, t: -1}, upper=0)
            add({v: 1, a: -1, b: -1, t: 1}, lower=-1)
        add(dict.fromkeys(free[g], 1), upper=1)
        for i, support in enumerate(family):
            f = free[g][i]
            for p in range(n):
                if p not in support:
                    add({value[g][p]: 1, f: 1}, upper=1)
            count = dict.fromkeys(value[g][:n], 1)
            count[f] = -2
            add(count, lower=0)
        if args.mode == 'selected_union':
            for i, (lb, hb) in enumerate((l, h) for l in light_bad for h in heavy_bad):
                f = free[g][len(family) + i]
                if lb[0] == 'small':
                    count = dict.fromkeys(value[g][:n], 1)
                    count[f] = n
                    add(count, upper=n + 1)
                else:
                    add({value[g][lb[1]]: 1, f: -1}, lower=0)
                if hb[0] == 'small':
                    count = {value[g][n + 1 + j]: 1 for j in range(len(remaining))}
                    count[f] = len(remaining)
                    add(count, upper=len(remaining) + 1)
                elif hb[0] == 'base':
                    add({value[g][n]: 1, f: -1}, lower=0)
                else:
                    j = remaining.index(hb[1])
                    add({value[g][n + 1 + j]: 1, f: -1}, lower=0)
    target_values = [int(bool(x & target)) for x, _ in samples]
    for r, expected in enumerate(target_values):
        add({value[-1][r]: 1}, expected, expected)
    add({f: 1 for gs in free for f in gs}, lower=args.gates - args.paid)
    mat = coo_matrix((dd, (rr, cc)), shape=(len(lo), nvars)).tocsc()
    print(json.dumps({'case': args.case, 'variables': nvars, 'constraints': len(lo),
                      'gates': args.gates, 'paid_limit': args.paid,
                      'mode': args.mode, 'full_target': args.full_target,
                      'family': [sorted(s) for s in family], 'target': sorted(target)}), flush=True)
    start = time.time()
    result = milp(np.zeros(nvars), integrality=np.ones(nvars), bounds=Bounds(0, 1),
                  constraints=LinearConstraint(mat, np.array(lo), np.array(hi)),
                  options={'time_limit': args.seconds, 'disp': True})
    answer = {'status': int(result.status), 'message': result.message, 'elapsed': time.time() - start,
              'n': n, 'y': sorted(y), 'family': [sorted(s) for s in family],
              'target': sorted(target), 'initial_count': ni}
    if result.x is not None:
        gates = []
        values = list(initial)
        cost = 0
        for g in range(args.gates):
            a = int(np.argmax(result.x[left[g]]))
            b = int(np.argmax(result.x[right[g]]))
            is_or = result.x[op[g]] >= .5
            vals = [int(bool(u or v) if is_or else bool(u and v))
                    for u, v in zip(values[a], values[b])]
            supp = {p for p in range(n) if vals[p]}
            heavy = {p for p, yes in zip(remaining, vals[n+1:n+1+len(remaining)]) if yes}
            assigned = next((i for i, s in enumerate(family) if len(supp) >= 2 and supp <= s), None)
            if args.mode == 'outside_meeting':
                charged = assigned is None
            else:
                light_charge = len(supp) >= 2 and supp <= target
                heavy_charge = not vals[n] and len(heavy) >= 2 and heavy <= target
                charged = assigned is None and (light_charge or heavy_charge)
            cost += charged
            gates.append({'op': 'or' if is_or else 'and', 'a': a, 'b': b,
                          'singleton_support': sorted(supp), 'heavy_base': vals[n],
                          'heavy_support': sorted(heavy),
                          'assigned': assigned, 'charged': charged})
            values.append(vals)
        answer.update({'gates': gates, 'paid': cost, 'correct_samples': values[-1] == target_values})
        assert values[-1] == target_values
        assert cost <= args.paid
        if args.full_target:
            for mask in range(1 << n):
                x = {p for p in range(n) if mask & (1 << p)}
                wire = [int(p in x) for p in range(n)] + [int(not y <= x), 0, 1]
                for gate in gates:
                    a, b = wire[gate['a']], wire[gate['b']]
                    wire.append(int(bool(a or b) if gate['op'] == 'or' else bool(a and b)))
                assert wire[-1] == int(bool(x & target)), (mask, wire[-1])
            answer['full_truth_table_pass'] = True
    args.output.write_text(json.dumps(answer, indent=2))
    print(json.dumps(answer), flush=True)


if __name__ == '__main__':
    main()
