import argparse
import json
import random
import shutil
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path


CADICAL = '/tmp/oec/pequalnp-pilot-57/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'


class CNF:
    def __init__(self, path):
        self.path = path
        self.body = path.with_suffix('.body')
        self.file = self.body.open('w')
        self.variables = 1
        self.clauses = 1
        self.file.write('1 0\n')

    def var(self, prefer=None):
        self.variables += 1
        return -self.variables if prefer is False else self.variables

    def clause(self, *xs):
        if 1 in xs:
            return
        ys = tuple(dict.fromkeys(x for x in xs if x != -1))
        if any(-x in ys for x in ys):
            return
        self.file.write(' '.join(map(str, ys)) + ' 0\n')
        self.clauses += 1

    def exactly_one(self, xs, preferred_index=None):
        self.clause(*xs)
        prefix = [self.var(None if preferred_index is None else preferred_index <= i)
                  for i in range(len(xs) - 1)]
        self.clause(-xs[0], prefix[0])
        for i in range(1, len(xs) - 1):
            self.clause(-xs[i], prefix[i])
            self.clause(-prefix[i - 1], prefix[i])
            self.clause(-xs[i], -prefix[i - 1])
        self.clause(-xs[-1], -prefix[-1])
        return prefix

    def ao_gate(self, op, a, b, prefer=None):
        z = self.var(prefer)
        self.clause(-a, -b, z)
        self.clause(a, b, -z)
        self.clause(-op, -a, z)
        self.clause(-op, -b, z)
        self.clause(op, a, -z)
        self.clause(op, b, -z)
        return z

    def count_row(self, xs, count):
        row = [1] + [-1] * (count + 1)
        for x in xs:
            next_row = [1]
            for j in range(1, count + 2):
                a, b = row[j], row[j - 1]
                z = self.var()
                self.clause(-a, z)
                self.clause(-x, -b, z)
                self.clause(-z, a, x)
                self.clause(-z, a, b)
                next_row.append(z)
            row = next_row
        return row

    def exact_count(self, xs, count):
        row = self.count_row(xs, count)
        self.clause(row[count])
        self.clause(-row[count + 1])

    def finish(self):
        self.file.close()
        with self.path.open('w') as out:
            out.write(f'p cnf {self.variables} {self.clauses}\n')
            with self.body.open() as inp:
                shutil.copyfileobj(inp, out)
        self.body.unlink()


def evaluate(gates, mask, ninputs=26):
    return evaluate_wires(gates, mask, ninputs)[-1]


def evaluate_wires(gates, mask, ninputs=26):
    wires = [bool(mask >> i & 1) for i in range(ninputs)]
    for op, a, b in gates:
        wires.append((wires[a] or wires[b]) if op else (wires[a] and wires[b]))
    return wires


def canonicalize(gates, ninputs):
    mapping = {i: i for i in range(ninputs)}
    remaining = set(range(len(gates)))
    answer = []
    while remaining:
        choices = []
        for i in remaining:
            op, a, b = gates[i]
            if a in mapping and b in mapping:
                a, b = sorted((mapping[a], mapping[b]))
                choices.append((b, a, op, i))
        assert choices
        b, a, op, i = min(choices)
        remaining.remove(i)
        mapping[ninputs + i] = ninputs + len(answer)
        answer.append([op, a, b])
    assert mapping[ninputs + len(gates) - 1] == ninputs + len(gates) - 1
    return answer


def emit(path, gates, samples, useful=True, fixed=None, first=None, ninputs=26, order_max=False,
         order_lex=False, and_count=None, last_and=False, positive_live=False,
         incomparable=False, dominance=False, negative_live=False, wire_excess=False,
         phase_seed=None, max_edits=None, positive_incomparable=False,
         negative_error_levels=None, hard_negative_masks=None):
    cnf = CNF(path)
    selected = []
    bprefixes = []
    aprefixes = []
    for i in range(gates):
        hint_op, hint_a, hint_b = phase_seed[i] if phase_seed is not None else (None, None, None)
        op = cnf.var(None if hint_op is None else bool(hint_op))
        sa = [cnf.var(None if hint_a is None else j == hint_a) for j in range(ninputs + i)]
        sb = [cnf.var(None if hint_b is None else j == hint_b) for j in range(ninputs + i)]
        prefix = cnf.exactly_one(sa, hint_a)
        aprefixes.append(prefix)
        bprefixes.append(cnf.exactly_one(sb, hint_b))
        for j in range(len(sb) - 1):
            cnf.clause(-sb[j], prefix[j])
        if fixed is not None:
            known_op, known_a, known_b = fixed[i]
            cnf.clause(op if known_op else -op)
            cnf.clause(sa[known_a])
            cnf.clause(sb[known_b])
        selected.append((op, sa, sb))
    if max_edits is not None:
        assert phase_seed is not None
        edits = []
        for (op, sa, sb), (hint_op, hint_a, hint_b) in zip(selected, phase_seed):
            edits.extend((-op if hint_op else op, -sa[hint_a], -sb[hint_b]))
        row = cnf.count_row(edits, max_edits)
        cnf.clause(-row[max_edits + 1])
    if order_max or order_lex:
        for i in range(1, gates):
            for j in range(1, len(selected[i - 1][2])):
                cnf.clause(-selected[i - 1][2][j], -bprefixes[i][j - 1])
    if order_lex:
        for i in range(1, gates):
            equalities = []
            for side in (1, 2):
                eq = cnf.var()
                equalities.append(eq)
                before, after = selected[i - 1][side], selected[i][side]
                for x, y in zip(before, after):
                    cnf.clause(-x, -y, eq)
                    cnf.clause(-eq, -x, y)
            ea, eb = equalities
            for j in range(1, len(selected[i - 1][1])):
                cnf.clause(-eb, -selected[i - 1][1][j], -aprefixes[i][j - 1])
            cnf.clause(-eb, -ea, -selected[i - 1][0], selected[i][0])
    if and_count is not None:
        cnf.exact_count([-op for op, _, _ in selected], and_count)
    if last_and:
        cnf.clause(-selected[-1][0])
    copies = []
    if incomparable or dominance:
        for op, sa, sb in selected:
            eq = cnf.var()
            copies.append(eq)
            for x, y in zip(sa, sb):
                cnf.clause(-x, -y, eq)
                cnf.clause(-eq, -x, y)
    if first is not None:
        known_op, known_a, known_b = first
        op, sa, sb = selected[0]
        cnf.clause(op if known_op else -op)
        cnf.clause(sa[known_a])
        cnf.clause(sb[known_b])
    if useful:
        for wire in range(ninputs + gates - 1):
            cnf.clause(*(side[wire] for i, (_, sa, sb) in enumerate(selected)
                         if wire < ninputs + i for side in (sa, sb)))
    if wire_excess:
        excess = gates - ninputs + 1
        assert excess >= 0
        extra_uses = []
        for wire in range(ninputs + gates - 1):
            occurrences = [side[wire] for i, (_, sa, sb) in enumerate(selected)
                           if wire < ninputs + i for side in (sa, sb)]
            row = cnf.count_row(occurrences, excess + 1)
            cnf.clause(-row[excess + 2])
            extra_uses.extend(row[2:excess + 2])
        row = cnf.count_row(extra_uses, excess)
        cnf.clause(-row[excess + 1])
    positive_values = [[] for _ in range(gates)]
    negative_values = [[] for _ in range(gates)]
    difference_witnesses = [[[[], []], [[], []]] for _ in range(gates)]
    wire_values = [[] for _ in range(ninputs + gates)]
    error_outputs = []
    for mask, label in samples:
        wires = [1 if mask >> i & 1 else -1 for i in range(ninputs)]
        hints = evaluate_wires(phase_seed, mask, ninputs) if phase_seed is not None else None
        for i, (op, sa, sb) in enumerate(selected):
            a = cnf.var(None if hints is None else hints[phase_seed[i][1]])
            b = cnf.var(None if hints is None else hints[phase_seed[i][2]])
            for selectors, value in ((sa, a), (sb, b)):
                for wire, selector in enumerate(selectors):
                    cnf.clause(-selector, -value, wires[wire])
                    cnf.clause(-selector, value, -wires[wire])
            wires.append(cnf.ao_gate(op, a, b, None if hints is None else hints[ninputs + i]))
            if incomparable or positive_incomparable:
                hint_a = None if hints is None else hints[phase_seed[i][1]]
                hint_b = None if hints is None else hints[phase_seed[i][2]]
                ab = cnf.var(None if hints is None else hint_a and not hint_b)
                ba = cnf.var(None if hints is None else hint_b and not hint_a)
                cnf.clause(-ab, a)
                cnf.clause(-ab, -b)
                cnf.clause(-ba, -a)
                cnf.clause(-ba, b)
                difference_witnesses[i][int(bool(label))][0].append(ab)
                difference_witnesses[i][int(bool(label))][1].append(ba)
            if label:
                positive_values[i].append(wires[-1])
            else:
                negative_values[i].append(-wires[-1])
        if not label and negative_error_levels is not None:
            if hard_negative_masks is not None and mask in hard_negative_masks:
                cnf.clause(-wires[-1])
            else:
                error_outputs.append(wires[-1])
        else:
            cnf.clause(wires[-1] if label else -wires[-1])
        if dominance:
            for values, value in zip(wire_values, wires):
                values.append(value)
    if positive_live:
        for values in positive_values:
            cnf.clause(*values)
    if negative_live:
        for values in negative_values:
            cnf.clause(*values)
    if incomparable or positive_incomparable:
        for i, (op, _, _) in enumerate(selected):
            for direction in (0, 1):
                cnf.clause(-op, *difference_witnesses[i][1][direction])
                if incomparable:
                    cnf.clause(op, copies[i], *difference_witnesses[i][0][direction])
    if dominance:
        for i in range(gates):
            for earlier in range(ninputs + i):
                witnesses = []
                for t, (_, label) in enumerate(samples):
                    z, q = wire_values[ninputs + i][t], wire_values[earlier][t]
                    a, b = (z, -q) if label else (q, -z)
                    if -1 in (a, b):
                        continue
                    w = cnf.var()
                    cnf.clause(-w, a)
                    cnf.clause(-w, b)
                    witnesses.append(w)
                cnf.clause(copies[i], *witnesses)
    if negative_error_levels is not None:
        negative_error_levels.extend(cnf.count_row(error_outputs, len(error_outputs)))
    cnf.finish()
    return selected, cnf.variables, cnf.clauses


def read_model(solution, selected):
    positive = set()
    for line in solution.read_text().splitlines():
        if line.startswith('v '):
            positive.update(int(s) for s in line.split()[1:] if int(s) > 0)
    gates = []
    def truth(lit):
        return (lit in positive) if lit > 0 else (-lit not in positive)
    for op, sa, sb in selected:
        left = [i for i, v in enumerate(sa) if truth(v)]
        right = [i for i, v in enumerate(sb) if truth(v)]
        assert len(left) == len(right) == 1
        gates.append([int(truth(op)), left[0], right[0]])
    return gates


def main():
    p = argparse.ArgumentParser()
    p.add_argument('geometry', type=Path)
    p.add_argument('output', type=Path)
    p.add_argument('--gates', type=int, default=63)
    p.add_argument('--initial-neg', type=int, default=24)
    p.add_argument('--seconds', type=int, default=180)
    p.add_argument('--rounds', type=int, default=20)
    p.add_argument('--seed', type=int, default=5701)
    p.add_argument('--add', type=int, default=40)
    p.add_argument('--no-useful', action='store_true')
    p.add_argument('--full', action='store_true')
    p.add_argument('--phase-seed', type=Path)
    p.add_argument('--lex', action='store_true')
    p.add_argument('--first', choices=['or-same', 'and-same', 'or-edge', 'and-edge',
                                     'or-nonedge', 'and-nonedge'])
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    geometry = json.loads(args.geometry.read_text())
    assert isinstance(geometry, dict)
    edges = geometry['edges']
    positives = [(1 << a | 1 << b, 1) for a, b in edges]
    negatives = [(left | (right << 13), 0)
                 for left, right in geometry['maximal_independent_sets']]
    assert len(positives) == 52 and len(negatives) == 704
    for mask, label in positives + negatives:
        assert any((mask >> a & 1) and (mask >> b & 1) for a, b in edges) == bool(label)
    negative_masks = {mask for mask, _ in negatives}
    neighborhoods = [sum(1 << (b - 13) for a, b in edges if a == p) for p in range(13)]
    for left in range(1 << 13):
        forbidden = 0
        for point in range(13):
            if left >> point & 1:
                forbidden |= neighborhoods[point]
        right = ((1 << 13) - 1) ^ forbidden
        closed_left = sum(1 << point for point in range(13)
                          if not neighborhoods[point] & right)
        assert closed_left | (right << 13) in negative_masks
    all_samples = positives + negatives
    rng = random.Random(args.seed)
    samples = positives + [(1 << i, 0) for i in range(26)]
    samples += [(0, 0), ((1 << 13) - 1, 0), (((1 << 13) - 1) << 13, 0)]
    samples += rng.sample(negatives, args.initial_neg)
    if args.full:
        samples = all_samples
    samples = list(dict.fromkeys(samples))
    phase_seed = None
    if args.phase_seed:
        phase_data = json.loads(args.phase_seed.read_text())
        phase_seed = phase_data['gates'] if isinstance(phase_data, dict) else phase_data
        assert len(phase_seed) == args.gates
        phase_seed = [[op, *sorted((a, b))] for op, a, b in phase_seed]
        if args.lex:
            phase_seed = canonicalize(phase_seed, 26)
    first = None
    if args.first:
        op, shape = args.first.split('-')
        first = (int(op == 'or'), 0, {'same': 1, 'edge': 13, 'nonedge': 15}[shape])
    for iteration in range(args.rounds):
        stem = args.output / f'round-{iteration:03}'
        begin = time.monotonic()
        selected, nvars, nclauses = emit(stem.with_suffix('.cnf'), args.gates, samples,
                                        not args.no_useful, first=first, phase_seed=phase_seed,
                                        order_lex=args.lex)
        elapsed = time.monotonic() - begin
        print(datetime.now(timezone.utc).isoformat(), 'ROUND', iteration, 'samples', len(samples),
              'vars', nvars, 'clauses', nclauses, 'generation_seconds', round(elapsed, 2), flush=True)
        solution = stem.with_suffix('.solution.txt')
        with stem.with_suffix('.solver.log').open('w') as log:
            run = subprocess.run([CADICAL, '-t', str(args.seconds), '--seed=' + str(args.seed),
                                  '-w', str(solution), str(stem.with_suffix('.cnf'))],
                                 stdout=log, stderr=subprocess.STDOUT)
        print(datetime.now(timezone.utc).isoformat(), 'SOLVER', run.returncode,
              'seconds', round(time.monotonic() - begin, 2), flush=True)
        if run.returncode != 10:
            print('No candidate: UNSAT for encoded samples' if run.returncode == 20 else
                  'No candidate: solver limit or error; no lower bound established', flush=True)
            return
        answer = read_model(solution, selected)
        assert all(evaluate(answer, mask) == bool(label) for mask, label in samples)
        errors = [(mask, label) for mask, label in all_samples
                  if evaluate(answer, mask) != bool(label)]
        stem.with_suffix('.candidate.json').write_text(json.dumps(answer))
        print('VALIDATION_ERRORS', len(errors), flush=True)
        if not errors:
            (args.output / 'EXACT-WITNESS.json').write_text(json.dumps(answer))
            print('EXACT WITNESS', flush=True)
            return
        rng.shuffle(errors)
        samples = list(dict.fromkeys(samples + errors[:args.add]))
        phase_seed = answer


if __name__ == '__main__':
    main()
