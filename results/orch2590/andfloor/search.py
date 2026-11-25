#!/usr/bin/env python3
"""Exact finite-row search for Petersen with k ANDs and arbitrary free ORs.

Each AND operand is an arbitrary OR of primary inputs and earlier AND outputs.
The final output is another arbitrary OR. Empty ORs and unused ANDs are allowed.
No minimum-circuit, productivity, or squarefree-normal-form assumption is used.
SAT witnesses are independently evaluated on every input and expanded to AO2.
UNSAT from the external solver is experimental, not a Lean certificate.
"""
import argparse
import hashlib
import json
import pathlib
import subprocess
import time


class CNF:
    def __init__(self):
        self.variables = 0
        self.clauses = []

    def var(self):
        self.variables += 1
        return self.variables

    def add(self, *lits):
        self.clauses.append(list(lits))

    def conj(self, a, b):
        v = self.var()
        self.add(-v, a)
        self.add(-v, b)
        self.add(v, -a, -b)
        return v

    def disj(self, terms):
        v = self.var()
        for t in terms:
            self.add(-t, v)
        self.add(-v, *terms)
        return v


def evaluate(n, gates, output, row):
    wires = [bool(row & (1 << i)) for i in range(n)]
    for a, b in gates:
        wires.append(any(wires[i] for i in a) and any(wires[i] for i in b))
    return any(wires[i] for i in output)


def expand(n, gates, output):
    binary = []
    mapped = list(range(n))

    def make_or(indices):
        if not indices:
            return None
        value = indices[0]
        for nxt in indices[1:]:
            binary.append([1, value, nxt])
            value = n + len(binary) - 1
        return value

    for a, b in gates:
        left = make_or([mapped[i] for i in a if mapped[i] is not None])
        right = make_or([mapped[i] for i in b if mapped[i] is not None])
        if left is None or right is None:
            mapped.append(None)
        else:
            binary.append([0, left, right])
            mapped.append(n + len(binary) - 1)
    result = make_or([mapped[i] for i in output if mapped[i] is not None])
    return binary, result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--ands', type=int, required=True)
    ap.add_argument('--seconds', type=int, default=60)
    ap.add_argument('--prefix', type=pathlib.Path, required=True)
    ap.add_argument('--data', type=pathlib.Path, required=True)
    ap.add_argument('--solver', type=pathlib.Path, required=True)
    ap.add_argument('--pin', type=pathlib.Path)
    ap.add_argument('--productive', action='store_true')
    ap.add_argument('--dual', action='store_true')
    ap.add_argument('--require-non-read1', action='store_true')
    args = ap.parse_args()
    data = json.loads(args.data.read_text())
    n = data['inputs']
    edges = data['edges']
    k = args.ands
    assert n == 10 and len(edges) == 15
    positives = data['positive_rows']
    negatives = data['negative_rows']
    expected_pos = sorted({(1 << u) | (1 << v) for u, v in edges})
    expected_neg = []
    original_target = lambda row: any(row & (1 << u) and row & (1 << v) for u, v in edges)
    target = original_target
    for row in range(1 << n):
        if not target(row) and all(target(row | (1 << i)) for i in range(n) if not row & (1 << i)):
            expected_neg.append(row)
    assert sorted(positives) == expected_pos
    assert sorted(negatives) == expected_neg
    if args.dual:
        mask = (1 << n) - 1
        positives, negatives = [mask ^ r for r in negatives], [mask ^ r for r in positives]
        target = lambda row: not original_target(mask ^ row)
    cnf = CNF()
    selectors = [[[cnf.var() for _ in range(n + i)] for _ in range(2)] for i in range(k)]
    final = [cnf.var() for _ in range(n + k)]
    positive_values = [[] for _ in range(k)]
    for row, wanted in [(r, True) for r in positives] + [(r, False) for r in negatives]:
        values = []
        for i, sides in enumerate(selectors):
            operands = []
            for side in sides:
                terms = [side[j] for j in range(n) if row & (1 << j)]
                terms += [cnf.conj(side[n + j], values[j]) for j in range(i)]
                operands.append(cnf.disj(terms))
            value = cnf.conj(*operands)
            values.append(value)
            if wanted:
                positive_values[i].append(value)
        terms = [final[j] for j in range(n) if row & (1 << j)]
        terms += [cnf.conj(final[n + j], values[j]) for j in range(k)]
        result = cnf.disj(terms)
        cnf.add(result if wanted else -result)
    if args.productive:
        for values in positive_values:
            cnf.add(*values)
    if args.require_non_read1:
        assert not args.dual
        missing = []
        for u, v in edges:
            proofs = []
            for i, (left, right) in enumerate(selectors):
                crossing = cnf.disj([cnf.conj(left[u], right[v]), cnf.conj(left[v], right[u])])
                proofs.append(cnf.conj(final[n + i], crossing))
            missing.append(-cnf.disj(proofs))
        cnf.add(*missing)
    if args.pin:
        pinned = json.loads(args.pin.read_text())
        assert len(pinned['gates']) == k
        for sides, picked in zip(selectors, pinned['gates']):
            for side, selected in zip(sides, picked):
                assert all(0 <= i < len(side) for i in selected)
                for i, variable in enumerate(side):
                    cnf.add(variable if i in selected else -variable)
        for i, variable in enumerate(final):
            cnf.add(variable if i in pinned['output'] else -variable)
    args.prefix.parent.mkdir(parents=True, exist_ok=True)
    cnf_path = args.prefix.with_suffix('.cnf')
    with cnf_path.open('w') as f:
        f.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for clause in cnf.clauses:
            f.write(' '.join(map(str, clause)) + ' 0\n')
    start = time.time()
    with args.prefix.with_suffix('.stdout').open('w') as out, args.prefix.with_suffix('.stderr').open('w') as err:
        run = subprocess.run([str(args.solver), '-t', str(args.seconds), str(cnf_path)], stdout=out, stderr=err)
    text = args.prefix.with_suffix('.stdout').read_text()
    result = {'ands': k, 'rows': len(positives) + len(negatives), 'variables': cnf.variables,
              'clauses': len(cnf.clauses), 'seconds': time.time() - start, 'exit_code': run.returncode,
              'source_sha256': hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
              'cnf_sha256': hashlib.sha256(cnf_path.read_bytes()).hexdigest(),
              'productive': args.productive, 'dual': args.dual,
              'require_non_read1': args.require_non_read1,
              'pin': str(args.pin) if args.pin else None}
    if 's SATISFIABLE' in text:
        values = {int(t) for line in text.splitlines() if line.startswith('v ') for t in line.split()[1:] if int(t) > 0}
        gates = [[[j for j, v in enumerate(side) if v in values] for side in sides] for sides in selectors]
        output = [j for j, v in enumerate(final) if v in values]
        mismatches = [row for row in range(1 << n) if evaluate(n, gates, output, row) != bool(target(row))]
        binary, out = expand(n, gates, output)
        expanded_mismatches = []
        for row in range(1 << n):
            wires = [bool(row & (1 << i)) for i in range(n)]
            for op, a, b in binary:
                wires.append((wires[a] and wires[b]) if op == 0 else (wires[a] or wires[b]))
            actual = wires[out] if out is not None else False
            if actual != bool(target(row)):
                expanded_mismatches.append(row)
        result.update(status='SAT', gates=gates, output=output, mismatches=mismatches,
                      expanded_gates=binary, expanded_output=out, expanded_size=len(binary),
                      expanded_mismatches=expanded_mismatches)
        assert not mismatches and not expanded_mismatches
        if not args.dual:
            missing = [[u, v] for u, v in edges if not any(
                i + n in output and ((u in left and v in right) or (v in left and u in right))
                for i, (left, right) in enumerate(gates))]
            result['missing_squarefree_edges'] = missing
            if args.require_non_read1:
                assert missing
        if args.dual:
            primal = [[1 - op, a, b] for op, a, b in binary]
            primal_mismatches = []
            for row in range(1 << n):
                wires = [bool(row & (1 << i)) for i in range(n)]
                for op, a, b in primal:
                    wires.append((wires[a] and wires[b]) if op == 0 else (wires[a] or wires[b]))
                if (wires[out] if out is not None else True) != bool(original_target(row)):
                    primal_mismatches.append(row)
            result.update(primal_gates=primal, primal_or_count=sum(op == 1 for op, _, _ in primal),
                          primal_mismatches=primal_mismatches)
            assert not primal_mismatches
    elif 's UNSATISFIABLE' in text:
        result['status'] = 'UNSAT-external-only'
    else:
        result['status'] = 'UNKNOWN'
    args.prefix.with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
