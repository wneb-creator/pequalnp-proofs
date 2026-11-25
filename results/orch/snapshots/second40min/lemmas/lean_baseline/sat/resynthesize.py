import argparse
import ast
import json
import random
import re
import subprocess
import time
from pathlib import Path

CADICAL = '/tmp/oec/pequalnp-pilot-57/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'


class CNF:
    def __init__(self, path):
        self.path = path
        self.body = path.with_suffix('.body')
        self.file = self.body.open('w')
        self.variables = 1
        self.clauses = 0
        self.file.write('1 0\n')
        self.clauses = 1

    def var(self):
        self.variables += 1
        return self.variables

    def clause(self, *xs):
        if 1 in xs:
            return
        ys = [x for x in dict.fromkeys(xs) if x != -1]
        if any(-x in ys for x in ys):
            return
        self.file.write(' '.join(map(str, ys)) + ' 0\n')
        self.clauses += 1

    def exactly_one(self, xs, preferred_index=None):
        self.clause(*xs)
        if len(xs) < 2:
            return
        chain = [self.var() * (-1 if preferred_index is not None and i < preferred_index else 1) for i in range(len(xs)-1)]
        self.clause(-xs[0], chain[0])
        for i in range(1, len(xs) - 1):
            self.clause(-xs[i], chain[i])
            self.clause(-chain[i - 1], chain[i])
            self.clause(-xs[i], -chain[i - 1])
        self.clause(-xs[-1], -chain[-1])

    def gate(self, op, a, b, preferred_result=None):
        if abs(a) == 1 and abs(b) == 1 and abs(op) == 1:
            return 1 if ((a == 1 or b == 1) if op == 1 else (a == 1 and b == 1)) else -1
        z = self.var()
        if preferred_result is False:
            z = -z
        self.clause(-a, -b, z)
        self.clause(a, b, -z)
        self.clause(-op, -a, z)
        self.clause(-op, -b, z)
        self.clause(op, a, -z)
        self.clause(op, b, -z)
        return z

    def finish(self):
        self.file.close()
        with self.path.open('w') as out:
            out.write(f'p cnf {self.variables} {self.clauses}\n')
            with self.body.open() as inp:
                for chunk in iter(lambda: inp.read(1 << 20), ''):
                    out.write(chunk)
        self.body.unlink()


def evaluate(gates, mask, ninputs=26):
    wires = [bool(mask >> i & 1) for i in range(ninputs)]
    for op, a, b in gates:
        wires.append((wires[a] or wires[b]) if op else (wires[a] and wires[b]))
    return wires


def run_window(gates, tests, mutable, directory, name, seconds, fixed_ops=False, restrict_sources=None, ninputs=26, ordered_inputs=False, require_used=False, order_max=False, and_count=None, final_op=None, positive_live=False, or_incomparable=False, allow_equal_and=False, and_incomparable=False, order_sameop=False, lock_inputs=False, seed_phases=False):
    cnf = CNF(directory / (name + '.cnf'))
    selected = {}
    for i in mutable:
        op = (1 if gates[i][0] else -1) if fixed_ops else cnf.var()
        if not fixed_ops and seed_phases and gates[i][0] == 0:
            op = -op
        domain = list(range(ninputs + i))
        if restrict_sources is not None:
            domain = sorted(set(gates[i][1:]) | set(restrict_sources(i)))
        preferred_left, preferred_right = gates[i][1:]
        if ordered_inputs:
            preferred_left, preferred_right = sorted((preferred_left, preferred_right))
        sa = [(wire, cnf.var() * (-1 if seed_phases and wire != preferred_left else 1)) for wire in domain]
        sb = [(wire, cnf.var() * (-1 if seed_phases and wire != preferred_right else 1)) for wire in domain]
        cnf.exactly_one([v for _, v in sa], domain.index(preferred_left) if seed_phases else None)
        cnf.exactly_one([v for _, v in sb], domain.index(preferred_right) if seed_phases else None)
        if ordered_inputs:
            for left, left_selector in sa:
                for right, right_selector in sb:
                    if left > right or (left == right and not allow_equal_and):
                        cnf.clause(-left_selector, -right_selector)
                    elif left == right:
                        cnf.clause(-left_selector, -right_selector, -op)
        selected[i] = (op, sa, sb)
        if lock_inputs:
            left,right = gates[i][1:]
            if ordered_inputs:
                left,right = sorted((left,right))
            cnf.clause(dict(sa)[left])
            cnf.clause(dict(sb)[right])
    copy_flags = {}
    if and_incomparable:
        for i, (_, a, b) in enumerate(gates):
            if i in selected and allow_equal_and:
                copy = cnf.var()
                if seed_phases and a != b:
                    copy = -copy
                _, sa, sb = selected[i]
                b_choices = dict(sb)
                for source, selector in sa:
                    cnf.clause(-copy, -selector, b_choices[source])
                copy_flags[i] = copy
            elif i in selected:
                copy_flags[i] = -1
            else:
                copy_flags[i] = 1 if a == b else -1
    if require_used:
        assert set(mutable) == set(range(len(gates)))
        for wire in range(ninputs + len(gates) - 1):
            uses = [selector for _, sa, sb in selected.values() for source, selector in sa+sb if source == wire]
            cnf.clause(*uses)
    if order_max:
        assert ordered_inputs and set(mutable) == set(range(len(gates)))
        for i in range(len(gates)-1):
            for previous_wire, previous_selector in selected[i][2]:
                for next_wire, next_selector in selected[i+1][2]:
                    if previous_wire > next_wire:
                        cnf.clause(-previous_selector, -next_selector)
    if order_sameop:
        assert fixed_ops and ordered_inputs and set(mutable) == set(range(len(gates)))
        for i in range(len(gates)-1):
            if gates[i][0] == gates[i+1][0]:
                for previous_wire, previous_selector in selected[i][2]:
                    for next_wire, next_selector in selected[i+1][2]:
                        if previous_wire > next_wire:
                            cnf.clause(-previous_selector, -next_selector)
    if final_op is not None:
        assert len(gates)-1 in selected
        op = selected[len(gates)-1][0]
        cnf.clause(op if final_op else -op)
    if and_count is not None:
        threshold = [1] + [-1] * (and_count+1)
        seed_and_count = 0
        for i, gate in enumerate(gates):
            seed_and_count += gate[0] == 0
            is_and = -selected[i][0] if i in selected else (1 if gate[0] == 0 else -1)
            next_threshold = [1]
            for j in range(1, and_count+2):
                old, previous = threshold[j], threshold[j-1]
                z = cnf.var()
                if seed_phases and seed_and_count < j:
                    z = -z
                cnf.clause(-old, z)
                cnf.clause(-previous, -is_and, z)
                cnf.clause(old, previous, -z)
                cnf.clause(old, is_and, -z)
                next_threshold.append(z)
            threshold = next_threshold
        cnf.clause(threshold[and_count])
        cnf.clause(-threshold[and_count+1])
    positive_values = [[] for _ in gates]
    directions = [[[], []] for _ in gates]
    negative_directions = [[[], []] for _ in gates]
    for mask, label in tests:
        seed_values = evaluate(gates,mask,ninputs) if seed_phases else None
        wires = [1 if mask >> i & 1 else -1 for i in range(ninputs)]
        for i, (op, a, b) in enumerate(gates):
            seed_a = seed_b = None
            if seed_phases:
                left,right = sorted((a,b)) if ordered_inputs and i in selected else (a,b)
                seed_a,seed_b = seed_values[left],seed_values[right]
            if i in selected:
                opv, sa, sb = selected[i]
                av = cnf.var()
                bv = cnf.var()
                if seed_a is False:
                    av = -av
                if seed_b is False:
                    bv = -bv
                for source, selector in sa:
                    cnf.clause(-selector, -av, wires[source])
                    cnf.clause(-selector, av, -wires[source])
                for source, selector in sb:
                    cnf.clause(-selector, -bv, wires[source])
                    cnf.clause(-selector, bv, -wires[source])
            else:
                opv, av, bv = (1 if op else -1), wires[a], wires[b]
            wires.append(cnf.gate(opv, av, bv, seed_values[ninputs+i] if seed_phases else None))
            if label and or_incomparable and opv != -1:
                first, second = cnf.var(), cnf.var()
                if seed_phases:
                    first *= 1 if seed_a and not seed_b else -1
                    second *= 1 if seed_b and not seed_a else -1
                cnf.clause(-first, av)
                cnf.clause(-first, -bv)
                cnf.clause(-second, -av)
                cnf.clause(-second, bv)
                directions[i][0].append(first)
                directions[i][1].append(second)
            if not label and and_incomparable and opv != 1:
                first, second = cnf.var(), cnf.var()
                if seed_phases:
                    first *= 1 if seed_a and not seed_b else -1
                    second *= 1 if seed_b and not seed_a else -1
                cnf.clause(-first, av)
                cnf.clause(-first, -bv)
                cnf.clause(-second, -av)
                cnf.clause(-second, bv)
                negative_directions[i][0].append(first)
                negative_directions[i][1].append(second)
        cnf.clause(wires[-1] if label else -wires[-1])
        if label:
            for i in range(len(gates)):
                positive_values[i].append(wires[ninputs+i])
    if positive_live:
        for values in positive_values:
            cnf.clause(*values)
    if or_incomparable:
        for i, (first, second) in enumerate(directions):
            opv = selected[i][0] if i in selected else (1 if gates[i][0] else -1)
            cnf.clause(-opv, *first)
            cnf.clause(-opv, *second)
    if and_incomparable:
        for i, (first, second) in enumerate(negative_directions):
            opv = selected[i][0] if i in selected else (1 if gates[i][0] else -1)
            cnf.clause(opv, copy_flags[i], *first)
            cnf.clause(opv, copy_flags[i], *second)
    cnf.finish()
    stamp = time.time()
    print(name, 'mutable', mutable, 'vars', cnf.variables, 'clauses', cnf.clauses, flush=True)
    output = directory / (name + '.solver.log')
    solution = directory / (name + '.solution.txt')
    with output.open('w') as log:
        result = subprocess.run([CADICAL, '-t', str(seconds), '-w', str(solution), str(cnf.path)], stdout=log, stderr=subprocess.STDOUT)
    print(name, 'exit', result.returncode, 'seconds', round(time.time()-stamp, 2), flush=True)
    if result.returncode != 10:
        return None
    positive = set()
    for line in solution.read_text().splitlines():
        if line.startswith('v '):
            positive.update(int(s) for s in line.split()[1:] if int(s) > 0)
    answer = [list(g) for g in gates]
    def literal_true(literal):
        return literal in positive if literal > 0 else -literal not in positive
    for i, (op, sa, sb) in selected.items():
        answer[i] = [int(literal_true(op)), next(w for w, v in sa if literal_true(v)), next(w for w, v in sb if literal_true(v))]
    assert all(op in (0, 1) and 0 <= a < ninputs+i and 0 <= b < ninputs+i for i, (op, a, b) in enumerate(answer))
    errors = [(mask, label) for mask, label in tests if evaluate(answer, mask,ninputs)[-1] != bool(label)]
    assert not errors, errors
    (directory / (name + '.witness.json')).write_text(json.dumps(answer))
    print('WITNESS', name, flush=True)
    return answer


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('candidate', type=Path)
    parser.add_argument('geometry', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--seconds', type=int, default=25)
    parser.add_argument('--jobs', type=int, default=40)
    parser.add_argument('--seed', type=int, default=57)
    parser.add_argument('--cegis', action='store_true')
    args = parser.parse_args()
    gates = json.loads(args.candidate.read_text())
    assert 1 <= len(gates) <= 63
    assert all(op in (0, 1) and 0 <= a < 26+i and 0 <= b < 26+i for i, (op, a, b) in enumerate(gates))
    data = json.loads(args.geometry.read_text())
    posted = json.loads(Path('/tmp/oec/pequalnp-pilot-57/assigned-gap.json').read_text())['gap']['statement']
    posted_edges = ast.literal_eval(re.search(r'\(\[(.*?)\] : List', posted).group(0).split(' : List')[0][1:])
    assert data['edges'] == [list(e) for e in posted_edges]
    tests = [(1 << a | 1 << b, 1) for a, b in data['edges']]
    negatives = data['maximal_independent_sets']
    if negatives and isinstance(negatives[0], list):
        negatives = [point_mask | (line_mask << 13) for point_mask, line_mask in negatives]
    assert len(tests) == 52 and len(negatives) == 704
    assert all(0 <= mask < (1 << 26) for mask in negatives)
    assert all(not (mask >> a & 1 and mask >> b & 1) for mask in negatives for a, b in data['edges'])
    neighborhoods = [sum(1 << (b - 13) for a, b in data['edges'] if a == u) for u in range(13)]
    complete = set()
    for points in range(1 << 13):
        excluded = 0
        for u in range(13):
            if points >> u & 1:
                excluded |= neighborhoods[u]
        lines = ((1 << 13) - 1) ^ excluded
        closure = sum(1 << u for u in range(13) if neighborhoods[u] & lines == 0)
        if closure == points:
            complete.add(points | (lines << 13))
    assert set(negatives) == complete
    tests.extend((mask, 0) for mask in negatives)
    errors = [(mask, label) for mask, label in tests if evaluate(gates, mask)[-1] != bool(label)]
    print('input errors', errors, flush=True)
    args.output.mkdir(parents=True, exist_ok=True)
    rng = random.Random(args.seed)
    bad_masks = [mask for mask, label in errors]
    focus = set()
    for mask in bad_masks:
        wires = evaluate(gates, mask)
        for i, (_, a, b) in enumerate(gates):
            if wires[a] or wires[b]:
                focus.add(i)
    focus.update(range(len(gates)-8, len(gates)))
    print('focus', sorted(focus), flush=True)
    for job in range(args.jobs):
        if job < 3:
            count = [6, 10, 14][job]
            mutable = list(range(len(gates)-count, len(gates)))
        else:
            count = [4, 6, 8, 10, 12][job % 5]
            mutable = sorted(rng.sample(sorted(focus), min(count, len(focus))))
        if args.cegis:
            active = tests[:52] + rng.sample(tests[52:], 48)
            for round_number in range(12):
                name = f'window-{job:03}-round-{round_number:02}'
                result = run_window(gates, active, mutable, args.output, name, args.seconds, fixed_ops=(job % 2 == 0))
                if result is None:
                    break
                failures = [(mask, label) for mask, label in tests if evaluate(result, mask)[-1] != bool(label)]
                print(name, 'full-basis failures', len(failures), flush=True)
                if not failures:
                    (args.output / 'FULL-WITNESS.json').write_text(json.dumps(result))
                    print('FULL WITNESS', name, flush=True)
                    return
                active.extend(failures[:64])
        else:
            result = run_window(gates, tests, mutable, args.output, f'window-{job:03}', args.seconds, fixed_ops=(job % 2 == 0))
            if result is not None:
                (args.output / 'FULL-WITNESS.json').write_text(json.dumps(result))
                return


if __name__ == '__main__':
    main()
