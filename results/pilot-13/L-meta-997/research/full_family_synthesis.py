import argparse
import itertools
import json
import functools
import operator
import time
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--target-size', type=int, default=6)
    ap.add_argument('--tail', type=int)
    ap.add_argument('--seconds', type=int, default=180)
    ap.add_argument('--rounds', type=int, default=3)
    ap.add_argument('--pair-order', choices=['pq', 'yp', 'yq'], default='pq')
    ap.add_argument('--baseline-only', action='store_true')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    r = args.target_size
    width = r - 1
    n = 3 + 2 * width + 1
    y = {0, 1, 2}
    ps = list(range(3, 3 + width))
    qs = list(range(3 + width, 3 + 2 * width))
    common = n - 1
    targets = [set(ps + [common]), set(qs + [common])]
    family = [{i, ps[j], qs[(j + i) % width]} for i in range(3) for j in range(width)]
    all_family = family + targets
    assert all(len(a & b) <= 1 for i, a in enumerate(all_family) for b in all_family[i + 1:])
    prefix = []

    def gate(op, a, b=None):
        prefix.append((op, a, b))
        return n + len(prefix) - 1

    outs_a = []
    for i in range(3):
        for j in range(width):
            p, q = ps[j], qs[(j + i) % width]
            if args.pair_order == 'pq':
                w = gate('or', p, q)
                out = gate('or', i, w)
            elif args.pair_order == 'yp':
                w = gate('or', i, p)
                out = gate('or', w, q)
            else:
                w = gate('or', i, q)
                out = gate('or', w, p)
            outs_a.append(out)
    choices = next(js for js in itertools.product(range(width), repeat=3)
                   if len(set(js)) == 3 and len({(js[i] + i) % width for i in range(3)}) == 3)
    factor_indices = [i * width + choices[i] for i in range(3)]
    factors = [family[i] for i in factor_indices]
    assert all(not a & b for i, a in enumerate(factors) for b in factors[i + 1:])
    h = gate('and', outs_a[factor_indices[0]], outs_a[factor_indices[1]])
    h = gate('and', h, outs_a[factor_indices[2]])
    not_index = len(prefix)
    z = gate('not', h)
    tail_size = args.tail if args.tail is not None else 2 * r - 8
    assert tail_size > 0
    universe = (1 << (1 << n)) - 1
    full_initial = []
    for p in range(n):
        block = 1 << p
        bit = (universe // ((1 << (2 * block)) - 1)) * (((1 << block) - 1) << block)
        full_initial.append(bit)
    for op, a, b in prefix:
        if op == 'not':
            v = universe ^ full_initial[a]
        elif op == 'or':
            v = full_initial[a] | full_initial[b]
        else:
            v = full_initial[a] & full_initial[b]
        full_initial.append(v)
    full_targets = [functools.reduce(operator.or_, (full_initial[p] for p in t), 0) for t in targets]
    low_inputs = [sum(1 << p for p in c) for j in range(3) for c in itertools.combinations(range(n), j)]
    assert all((full_initial[z] >> mask) & 1 for mask in low_inputs)
    ym = sum(1 << p for p in y)
    assert not (full_initial[z] >> ym) & 1
    samples = {0, ym} | {1 << p for p in range(n)} | {ym | (1 << p) for p in range(n)}
    universe_mask = (1 << n) - 1
    for target in targets:
        tm = sum(1 << p for p in target)
        for factor in factors:
            fm = sum(1 << p for p in factor)
            samples.add(universe_mask & ~(tm | fm))
        samples.add(universe_mask & ~tm)
    # Add a small initial collection of other minimal H-positive assignments.
    for choice in list(itertools.product(*(sorted(f) for f in factors)))[::4]:
        hm = sum(1 << p for p in set(choice))
        samples.add(hm)
        for target in targets:
            samples.add(hm | (1 << min(target)))
    result_record = {'n': n, 'target_size': r, 'tail_size': tail_size,
                     'prefix_gates': len(prefix), 'total_gates': len(prefix) + tail_size,
                     'pair_order': args.pair_order, 'not_index': not_index,
                     'family': [sorted(s) for s in all_family], 'y': sorted(y),
                     'h_factors': [sorted(s) for s in factors], 'rounds': []}
    print(json.dumps(result_record), flush=True)
    start_total = time.time()
    for iteration in range(args.rounds):
        samples = sorted(samples)
        rows = len(samples)
        ni = len(full_initial)
        initial = [[int((v >> sample) & 1) for sample in samples] for v in full_initial]
        target_values = [[int((v >> sample) & 1) for sample in samples] for v in full_targets]
        nvars = 0

        def variables(k):
            nonlocal nvars
            out = list(range(nvars, nvars + k))
            nvars += k
            return out

        left, right, op, av, bv, value = [], [], [], [], [], []
        for g in range(tail_size):
            left.append(variables(ni + g))
            right.append(variables(ni + g))
            op.append(variables(1)[0])
            av.append(variables(rows))
            bv.append(variables(rows))
            value.append(variables(rows))
        outputs = [variables(tail_size) for _ in targets]
        rr, cc, dd, lo, hi = [], [], [], [], []

        def add(coefs, lower=-np.inf, upper=np.inf):
            row = len(lo)
            for col, coefficient in coefs.items():
                if coefficient:
                    rr.append(row)
                    cc.append(col)
                    dd.append(coefficient)
            lo.append(lower)
            hi.append(upper)

        for g in range(tail_size):
            add(dict.fromkeys(left[g], 1), 1, 1)
            add(dict.fromkeys(right[g], 1), 1, 1)
            order = {v: w for w, v in enumerate(left[g])}
            order.update({v: -w for w, v in enumerate(right[g])})
            add(order, upper=0)
            for row in range(rows):
                for choices_s, selected in [(left[g], av[g][row]), (right[g], bv[g][row])]:
                    for wire, selected_wire in enumerate(choices_s):
                        if wire < ni:
                            c = initial[wire][row]
                            add({selected: 1, selected_wire: 1}, upper=1+c)
                            add({selected: 1, selected_wire: -1}, lower=c-1)
                        else:
                            previous = value[wire-ni][row]
                            add({selected: 1, previous: -1, selected_wire: 1}, upper=1)
                            add({selected: 1, previous: -1, selected_wire: -1}, lower=-1)
                a, b, v, t = av[g][row], bv[g][row], value[g][row], op[g]
                add({v: 1, a: -1, t: -1}, -1, 0)
                add({v: 1, b: -1, t: -1}, -1, 0)
                add({v: 1, a: -1, b: -1, t: 1}, -1, 1)
        for j, selectors in enumerate(outputs):
            add(dict.fromkeys(selectors, 1), 1, 1)
            for g, sel in enumerate(selectors):
                for row, c in enumerate(target_values[j]):
                    add({value[g][row]: 1, sel: 1}, upper=1+c)
                    add({value[g][row]: 1, sel: -1}, lower=c-1)
        matrix = coo_matrix((dd, (rr, cc)), shape=(len(lo), nvars)).tocsc()
        metadata = {'round': iteration, 'samples': rows, 'variables': nvars, 'constraints': len(lo)}
        print(json.dumps(metadata), flush=True)
        if tail_size == 2 * (r - 1):
            candidate = np.zeros(nvars)
            vals = [list(v) for v in initial]
            next_gate = 0
            for j, target in enumerate(targets):
                members = sorted(target)
                accumulator = members[0]
                for p in members[1:]:
                    a, b = sorted([accumulator, p])
                    candidate[left[next_gate][a]] = 1
                    candidate[right[next_gate][b]] = 1
                    candidate[op[next_gate]] = 1
                    for row in range(rows):
                        candidate[av[next_gate][row]] = vals[a][row]
                        candidate[bv[next_gate][row]] = vals[b][row]
                        candidate[value[next_gate][row]] = vals[a][row] or vals[b][row]
                    vals.append([int(a or b) for a, b in zip(vals[a], vals[b])])
                    accumulator = ni + next_gate
                    next_gate += 1
                candidate[outputs[j][next_gate - 1]] = 1
            evaluation = matrix @ candidate
            assert np.all(evaluation >= np.array(lo)-1e-8)
            assert np.all(evaluation <= np.array(hi)+1e-8)
            metadata['known_baseline_satisfies_every_constraint'] = True
            print('Known ordinary-OR baseline satisfies every MILP constraint.', flush=True)
            if args.baseline_only:
                result_record['rounds'].append(metadata)
                break
        started = time.time()
        answer = milp(np.zeros(nvars), integrality=np.ones(nvars), bounds=Bounds(0, 1),
                      constraints=LinearConstraint(matrix, np.array(lo), np.array(hi)),
                      options={'time_limit': args.seconds, 'disp': True})
        metadata.update({'status': int(answer.status), 'message': answer.message,
                         'elapsed': time.time()-started})
        result_record['rounds'].append(metadata)
        if answer.x is None:
            break
        values = list(full_initial)
        tail = []
        for g in range(tail_size):
            a = int(np.argmax(answer.x[left[g]]))
            b = int(np.argmax(answer.x[right[g]]))
            is_or = answer.x[op[g]] >= .5
            tail.append(('or' if is_or else 'and', a, b))
            values.append((values[a] | values[b]) if is_or else (values[a] & values[b]))
        out = [ni + int(np.argmax(answer.x[selectors])) for selectors in outputs]
        metadata.update({'tail': tail, 'outputs': out})
        counterexamples = set()
        for j in range(2):
            difference = values[out[j]] ^ full_targets[j]
            for _ in range(8):
                if not difference:
                    break
                bit = difference & -difference
                counterexamples.add(bit.bit_length()-1)
                difference ^= bit
        if counterexamples:
            metadata['counterexamples'] = sorted(counterexamples)
            samples = set(samples) | counterexamples
            continue
        all_out = outs_a + out
        assert all(values[w] == functools.reduce(operator.or_, (full_initial[p] for p in s), 0)
                   for s, w in zip(all_family, all_out))
        refunds = []
        disjoint = [s for s in all_family if not s & y]
        for index, bits in enumerate(values[n:]):
            light = {p for p in range(n) if (bits >> (1 << p)) & 1}
            heavy = {p for p in range(n) if p not in y and (bits >> (ym | (1 << p))) & 1}
            if light in all_family and heavy in disjoint:
                refunds.append(index)
        lhs = sum(len(s) if not s & y else min(3, len(s)) for s in all_family)
        rhs = len(prefix) + len(tail) + len(refunds) + len(all_family)
        metadata.update({'full_truth_table_pass': True, 'refunds': refunds,
                         'lhs': lhs, 'rhs': rhs, 'actual_counterexample': lhs > rhs})
        result_record.update({'prefix': prefix, 'tail': tail, 'outputs': all_out})
        break
    result_record['elapsed_total'] = time.time()-start_total
    args.output.write_text(json.dumps(result_record, indent=2))
    print(json.dumps(result_record), flush=True)


if __name__ == '__main__':
    main()
