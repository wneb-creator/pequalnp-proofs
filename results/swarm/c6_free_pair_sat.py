#!/usr/bin/env python3
"""Exploratory overapproximation; an UNSAT result is not a Lean proof."""
import argparse
import itertools
import json
from pathlib import Path

EDGES = [(0, 3), (0, 4), (1, 3), (1, 5), (2, 4), (2, 5)]
PAIRS = [33, 18, 12]
ROWS = [1 << i for i in range(6)] + [1 << a | 1 << b for a, b in EDGES] + [7, 56, 33, 18, 12]

class Encoder:
    def __init__(self, gates):
        self.n = 0
        self.clauses = []
        self.gates = gates
        self.values = []
        self.types = []
        self.operands = []
        for k in range(gates):
            left, lm = self.operand(k)
            right, rm = self.operand(k)
            typ = self.fresh()
            out = [self.fresh() for _ in ROWS]
            for a, b, c in zip(left, right, out):
                # typ=true selects AND, false selects OR.
                self.clauses += [[-typ, -c, a], [-typ, -c, b], [-typ, c, -a, -b],
                                 [typ, c, -a], [typ, c, -b], [typ, -c, a, b]]
            self.values.append(out)
            self.types.append(typ)
            self.operands.append([lm, rm])
        for r, mask in enumerate(ROWS):
            truth = any(mask >> a & 1 and mask >> b & 1 for a, b in EDGES)
            self.clauses.append([self.values[-1][r] if truth else -self.values[-1][r]])

    def fresh(self):
        self.n += 1
        return self.n

    def conditional_eq(self, select, out, value):
        if isinstance(value, bool):
            self.clauses.append([-select, out if value else -out])
        else:
            self.clauses += [[-select, -out, value], [-select, out, -value]]

    def operand(self, k):
        # Six inputs, false, true, previous paid outputs, or a free pair closure.
        modes = [self.fresh() for _ in range(8 + k + 3)]
        self.clauses.append(modes)
        self.clauses += [[-a, -b] for a, b in itertools.combinations(modes, 2)]
        out = [self.fresh() for _ in ROWS]
        for mode in range(8 + k):
            for r, mask in enumerate(ROWS):
                value = bool(mask >> mode & 1) if mode < 6 else (mode == 7 if mode < 8 else self.values[mode - 8][r])
                self.conditional_eq(modes[mode], out[r], value)
        borrow = []
        for p, pair in enumerate(PAIRS):
            sel = modes[8 + k + p]
            chosen = [self.fresh() for _ in range(k)]
            borrow.append(chosen)
            for j, use in enumerate(chosen):
                self.clauses.append([-use, sel])
                for v in range(6):
                    if not (pair >> v & 1):
                        self.clauses.append([-use, -self.values[j][v]])
            for r, mask in enumerate(ROWS):
                if mask & pair:
                    self.clauses.append([-sel, out[r]])
                else:
                    terms = []
                    for j, use in enumerate(chosen):
                        z = self.fresh()
                        value = self.values[j][r]
                        self.clauses += [[-z, use], [-z, value], [z, -use, -value]]
                        terms.append(z)
                        self.clauses.append([-sel, -z, out[r]])
                    self.clauses.append([-sel, -out[r]] + terms)
        return out, {"modes": modes, "borrow": borrow}

    def write(self, path):
        with path.open('w') as f:
            f.write(f'p cnf {self.n} {len(self.clauses)}\n')
            for clause in self.clauses:
                f.write(' '.join(map(str, clause)) + ' 0\n')
        path.with_suffix('.json').write_text(json.dumps({
            'gates': self.gates, 'variables': self.n, 'clauses': len(self.clauses),
            'rows': ROWS, 'types': self.types, 'values': self.values,
            'operands': self.operands, 'pairs': PAIRS, 'edges': EDGES}, indent=2))

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('path', type=Path)
    parser.add_argument('--gates', type=int, default=7)
    args = parser.parse_args()
    enc = Encoder(args.gates)
    enc.write(args.path)
    print(json.dumps({'variables': enc.n, 'clauses': len(enc.clauses), 'gates': enc.gates}))

if __name__ == '__main__':
    main()
